(function (global) {
  "use strict";

  var AE = (typeof require === "function" && typeof window === "undefined")
    ? require("./arm_emulator.js")
    : global.ArmEmulator;

  var MTK_IMAGE_MAGIC = 0x58881688;
  var DTBO_MAGIC_BE = 0xd7b7ab1e;
  var FDT_MAGIC_BE = 0xd00dfeed;
  var ZIMAGE_MAGIC_LE = 0x016f2818;

  var DSI_MODE_NAMES = {
    0: "CMD_MODE",
    1: "SYNC_PULSE_VDO_MODE",
    2: "SYNC_EVENT_VDO_MODE",
    3: "BURST_VDO_MODE"
  };

  var DSI_PS_NAMES = {
    0: "LCM_PACKED_PS_16BIT_RGB565",
    1: "LCM_LOOSELY_PS_18BIT_RGB666",
    2: "LCM_PACKED_PS_24BIT_RGB888",
    3: "LCM_PACKED_PS_18BIT_RGB666"
  };

  function toHex(val) {
    if (val === null || val === undefined) return "N/A";
    if (typeof val === "bigint") return "0x" + val.toString(16);
    return "0x" + (val >>> 0).toString(16);
  }

  function safeIdent(name, fallback) {
    var s = String(name || "").replace(/[^A-Za-z0-9_]/g, "_").replace(/_+/g, "_").replace(/^_+|_+$/g, "");
    if (!s) return fallback || "lcm_panel";
    if (/^[0-9]/.test(s)) s = "lcm_" + s;
    return s;
  }

  function asciiAt(bytes, off, maxLen) {
    maxLen = maxLen || 96;
    if (off < 0 || off >= bytes.length) return "";
    var end = Math.min(bytes.length, off + maxLen);
    var out = "";
    for (var i = off; i < end; i++) {
      var b = bytes[i];
      if (b === 0) return out;
      if (b < 32 || b >= 127) return "";
      out += String.fromCharCode(b);
    }
    return "";
  }

  function findBytes(haystack, needle, startPos) {
    var s = startPos || 0;
    var nlen = needle.length;
    var limit = haystack.length - nlen;
    outer: for (var i = s; i <= limit; i++) {
      if (haystack[i] !== needle[0]) continue;
      for (var j = 1; j < nlen; j++) {
        if (haystack[i + j] !== needle[j]) continue outer;
      }
      return i;
    }
    return -1;
  }

  function findAscii(haystack, text, startPos) {
    var needle = new Uint8Array(text.length);
    for (var i = 0; i < text.length; i++) needle[i] = text.charCodeAt(i);
    return findBytes(haystack, needle, startPos);
  }

  function hasAscii(haystack, text) {
    return findAscii(haystack, text, 0) !== -1;
  }

  function readCStringVa(bytes, baseAddr, va, minLen, maxLen) {
    var off = va - baseAddr;
    if (off < 0 || off >= bytes.length) return null;
    var s = asciiAt(bytes, off, maxLen || 96);
    if (s.length < (minLen || 2)) return null;
    return s;
  }

  async function decompressGzip(chunk) {
    if (typeof DecompressionStream !== "undefined") {
      try {
        var ds = new DecompressionStream("gzip");
        var writer = ds.writable.getWriter();
        writer.write(chunk);
        writer.close();
        var reader = ds.readable.getReader();
        var chunks = [];
        var total = 0;
        while (true) {
          var step = await reader.read();
          if (step.done) break;
          chunks.push(step.value);
          total += step.value.length;
        }
        var merged = new Uint8Array(total);
        var pos = 0;
        for (var i = 0; i < chunks.length; i++) {
          merged.set(chunks[i], pos);
          pos += chunks[i].length;
        }
        return merged;
      } catch (err) {
      }
    }
    if (typeof require === "function") {
      try {
        var zlib = require("zlib");
        return new Uint8Array(zlib.gunzipSync(chunk));
      } catch (err2) {
      }
    }
    return null;
  }

  function extractEmbeddedDtbs(data, labelPrefix) {
    var out = [];
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    var pos = 0;
    while (pos + 40 <= data.length) {
      if (
        data[pos] === 0xd0 &&
        data[pos + 1] === 0x0d &&
        data[pos + 2] === 0xfe &&
        data[pos + 3] === 0xed
      ) {
        var totSize = dv.getUint32(pos + 4, false);
        var offStruct = dv.getUint32(pos + 8, false);
        var offStr = dv.getUint32(pos + 12, false);
        if (totSize >= 40 && totSize <= data.length - pos && offStruct >= 40 && offStruct < totSize && offStr >= 40 && offStr < totSize) {
          out.push({
            label: labelPrefix + "_dtb_0x" + pos.toString(16),
            offset: pos,
            bytes: data.slice(pos, pos + totSize)
          });
          pos += totSize;
          continue;
        }
      }
      pos += 4;
    }
    return out;
  }

  function parseMtkPartitions(data) {
    var parts = [];
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    var pos = 0;
    while (pos + 512 <= data.length) {
      if (dv.getUint32(pos, true) === MTK_IMAGE_MAGIC) {
        var dsize = dv.getUint32(pos + 4, true);
        var maddr = dv.getUint32(pos + 40, true);
        var pname = asciiAt(data, pos + 8, 32) || "part";
        if (dsize > 0 && dsize <= data.length - (pos + 512)) {
          var loadAddr = (maddr === 0xffffffff || maddr === 0x12345678 || maddr === 0) ? null : (maddr >>> 0);
          parts.push({
            headerOffset: pos,
            payloadOffset: pos + 512,
            size: dsize,
            name: pname,
            loadAddress: loadAddr,
            payload: data.subarray(pos + 512, pos + 512 + dsize)
          });
          pos = pos + 512 + dsize;
          continue;
        }
      }
      pos += 4;
    }
    return parts;
  }

  function parseElf(data) {
    if (data.length < 64) return null;
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    var is64 = data[4] === 2;
    var le = data[5] === 1;
    var machine = dv.getUint16(18, le);
    var entry = is64 ? Number(dv.getBigUint64(24, le)) : dv.getUint32(24, le);
    var phoff = is64 ? Number(dv.getBigUint64(32, le)) : dv.getUint32(28, le);
    var phentsize = dv.getUint16(is64 ? 54 : 42, le);
    var phnum = dv.getUint16(is64 ? 56 : 44, le);
    var segs = [];
    for (var i = 0; i < phnum; i++) {
      var o = phoff + i * phentsize;
      if (o + phentsize > data.length) break;
      var pType = dv.getUint32(o, le);
      var pOffset = is64 ? Number(dv.getBigUint64(o + 8, le)) : dv.getUint32(o + 4, le);
      var pVaddr = is64 ? Number(dv.getBigUint64(o + 16, le)) : dv.getUint32(o + 8, le);
      var pFilesz = is64 ? Number(dv.getBigUint64(o + 32, le)) : dv.getUint32(o + 16, le);
      if (pType === 1 && pFilesz > 0) {
        segs.push({ offset: pOffset, vaddr: pVaddr, filesz: pFilesz });
      }
    }
    if (!segs.length) return null;
    var minVa = segs[0].vaddr;
    var maxEnd = segs[0].vaddr + segs[0].filesz;
    for (var k = 1; k < segs.length; k++) {
      if (segs[k].vaddr < minVa) minVa = segs[k].vaddr;
      if (segs[k].vaddr + segs[k].filesz > maxEnd) maxEnd = segs[k].vaddr + segs[k].filesz;
    }
    var span = maxEnd - minVa;
    if (span <= 0 || span > 96 * 1024 * 1024) return null;
    var flat = new Uint8Array(span);
    for (var m = 0; m < segs.length; m++) {
      flat.set(data.subarray(segs[m].offset, segs[m].offset + segs[m].filesz), segs[m].vaddr - minVa);
    }
    return { is64: is64, machine: machine, entry: entry, baseAddress: minVa, flat: flat };
  }

  async function unpackInputBuffer(fileName, rawData) {
    var dv = new DataView(rawData.buffer, rawData.byteOffset, rawData.byteLength);
    if (
      rawData.length >= 2048 &&
      rawData[0] === 0x41 && rawData[1] === 0x4e && rawData[2] === 0x44 && rawData[3] === 0x52 &&
      rawData[4] === 0x4f && rawData[5] === 0x49 && rawData[6] === 0x44 && rawData[7] === 0x21
    ) {
      var kSz = dv.getUint32(8, true);
      var kAddr = dv.getUint32(12, true);
      var rSz = dv.getUint32(16, true);
      var sSz = dv.getUint32(24, true);
      var pageSz = dv.getUint32(36, true);
      var hdrVer = dv.getUint32(40, true);
      if (hdrVer >= 3 && pageSz === 0) pageSz = 4096;
      if (pageSz < 512 || pageSz > 65536) pageSz = 2048;
      var cmdline = asciiAt(rawData, 0x40, 512);
      var kOff = pageSz;
      var kRaw = rawData.subarray(kOff, Math.min(rawData.length, kOff + kSz));
      var gzPos = findBytes(kRaw, [0x1f, 0x8b, 0x08], 0);
      var kDecomp = null;
      if (gzPos !== -1) {
        kDecomp = await decompressGzip(kRaw.subarray(gzPos));
      }
      var primary = kDecomp || kRaw;
      var dtbs = [];
      if (hdrVer >= 2 && rawData.length >= 0x67c) {
        var recDtboSz = dv.getUint32(0x660, true);
        var dtbSz = dv.getUint32(0x670, true);
        var rnd = function (v) { return Math.ceil(v / pageSz) * pageSz; };
        var dtbOff = pageSz + rnd(kSz) + rnd(rSz) + rnd(sSz) + rnd(recDtboSz);
        if (dtbSz >= 40 && dtbOff + dtbSz <= rawData.length) {
          dtbs = extractEmbeddedDtbs(rawData.subarray(dtbOff, dtbOff + dtbSz), "boot_v2");
        }
      }
      if (!dtbs.length) dtbs = extractEmbeddedDtbs(kRaw.subarray(Math.max(0, kRaw.length - 512 * 1024)), "zimage");
      return {
        inputName: fileName,
        rawSize: rawData.length,
        formatType: "ANDROID_BOOT_IMG",
        evidence: "Android boot image v" + hdrVer + ", page_size=" + pageSz + (kDecomp ? ", gzip unpacked" : ""),
        primaryCode: primary,
        codeFileOffset: kDecomp ? 0 : kOff,
        headerLoadAddress: kAddr ? (kAddr >>> 0) : null,
        dtbs: dtbs,
        subPartitions: [],
        metadata: { headerVersion: hdrVer, pageSize: pageSz, cmdline: cmdline, kernelSize: kSz }
      };
    }

    if (rawData.length >= 32 && dv.getUint32(0, false) === DTBO_MAGIC_BE) {
      var cnt = dv.getUint32(16, false);
      var eSz = dv.getUint32(12, false);
      var eOff = dv.getUint32(20, false);
      var dtboList = [];
      for (var d = 0; d < cnt && d < 64; d++) {
        var o = eOff + d * eSz;
        if (o + 12 > rawData.length) break;
        var sz = dv.getUint32(o, false);
        var doff = dv.getUint32(o + 4, false);
        if (sz >= 40 && doff + sz <= rawData.length) {
          dtboList.push({ label: "dtbo_" + d, offset: doff, bytes: rawData.slice(doff, doff + sz) });
        }
      }
      return {
        inputName: fileName,
        rawSize: rawData.length,
        formatType: "DTBO_IMG",
        evidence: "Android DTBO table with " + dtboList.length + " FDT blob(s)",
        primaryCode: new Uint8Array(0),
        codeFileOffset: 0,
        headerLoadAddress: null,
        dtbs: dtboList,
        subPartitions: [],
        metadata: {}
      };
    }

    if (rawData.length >= 40 && dv.getUint32(0, false) === FDT_MAGIC_BE) {
      return {
        inputName: fileName,
        rawSize: rawData.length,
        formatType: "FDT_DTB",
        evidence: "Flattened Device Tree blob",
        primaryCode: new Uint8Array(0),
        codeFileOffset: 0,
        headerLoadAddress: null,
        dtbs: [{ label: fileName, offset: 0, bytes: rawData }],
        subPartitions: [],
        metadata: {}
      };
    }

    if (rawData.length >= 64 && rawData[0] === 0x7f && rawData[1] === 0x45 && rawData[2] === 0x4c && rawData[3] === 0x46) {
      var elf = parseElf(rawData);
      if (elf) {
        return {
          inputName: fileName,
          rawSize: rawData.length,
          formatType: "ELF",
          evidence: (elf.is64 ? "ELF64" : "ELF32") + " machine=0x" + elf.machine.toString(16),
          primaryCode: elf.flat,
          codeFileOffset: 0,
          headerLoadAddress: elf.baseAddress,
          elfMachine: elf.machine,
          elfIs64: elf.is64,
          dtbs: extractEmbeddedDtbs(elf.flat, "elf"),
          subPartitions: [],
          metadata: {}
        };
      }
    }

    var mtkParts = parseMtkPartitions(rawData.subarray(0, Math.min(rawData.length, 4 * 1024 * 1024)));
    if (mtkParts.length) {
      var lkPart = mtkParts[0];
      for (var p = 0; p < mtkParts.length; p++) {
        var ln = mtkParts[p].name.toLowerCase();
        if (ln === "lk" || ln === "lk1" || ln === "uboot") { lkPart = mtkParts[p]; break; }
      }
      var lkDtbs = [];
      for (var q = 0; q < mtkParts.length; q++) {
        var part = mtkParts[q];
        if (part.payload.length >= 40 && new DataView(part.payload.buffer, part.payload.byteOffset, 4).getUint32(0, false) === FDT_MAGIC_BE) {
          lkDtbs.push({ label: part.name, offset: part.payloadOffset, bytes: new Uint8Array(part.payload) });
        } else {
          var subD = extractEmbeddedDtbs(part.payload, part.name);
          for (var sd = 0; sd < subD.length; sd++) {
            subD[sd].offset += part.payloadOffset;
            lkDtbs.push(subD[sd]);
          }
        }
      }
      return {
        inputName: fileName,
        rawSize: rawData.length,
        formatType: "MTK_LK",
        evidence: "MediaTek LK header (0x58881688) partition '" + lkPart.name + "', size=0x" + lkPart.size.toString(16),
        primaryCode: lkPart.payload,
        codeFileOffset: lkPart.payloadOffset,
        headerLoadAddress: lkPart.loadAddress,
        dtbs: lkDtbs,
        subPartitions: mtkParts.map(function (sp) {
          return { name: sp.name, headerOffset: sp.headerOffset, payloadOffset: sp.payloadOffset, size: sp.size, loadAddress: sp.loadAddress };
        }),
        metadata: {}
      };
    }

    if (rawData.length >= 0x40 && dv.getUint32(0x24, true) === ZIMAGE_MAGIC_LE) {
      var gzZ = findBytes(rawData, [0x1f, 0x8b, 0x08], 0);
      var zDecomp = gzZ !== -1 ? await decompressGzip(rawData.subarray(gzZ)) : null;
      return {
        inputName: fileName,
        rawSize: rawData.length,
        formatType: "ARM_ZIMAGE",
        evidence: "ARM zImage" + (zDecomp ? " (gzip decompressed)" : ""),
        primaryCode: zDecomp || rawData,
        codeFileOffset: 0,
        headerLoadAddress: null,
        dtbs: extractEmbeddedDtbs(rawData.subarray(Math.max(0, rawData.length - 512 * 1024)), "zimage"),
        subPartitions: [],
        metadata: {}
      };
    }

    if (rawData.length >= 0x40 && rawData[0x38] === 0x41 && rawData[0x39] === 0x52 && rawData[0x3a] === 0x4d && rawData[0x3b] === 0x64) {
      return {
        inputName: fileName,
        rawSize: rawData.length,
        formatType: "ARM64_IMAGE",
        evidence: "Linux ARM64 Image (ARMd magic)",
        primaryCode: rawData,
        codeFileOffset: 0,
        headerLoadAddress: null,
        dtbs: [],
        subPartitions: [],
        metadata: { textOffset: Number(dv.getBigUint64(8, true)) }
      };
    }

    if (rawData.length >= 32 && rawData[0] === 0x1f && rawData[1] === 0x8b && rawData[2] === 0x08) {
      var gDecomp = await decompressGzip(rawData);
      if (gDecomp) {
        return {
          inputName: fileName,
          rawSize: rawData.length,
          formatType: "GZIP_KERNEL",
          evidence: "Gzip-compressed kernel image (" + gDecomp.length + " bytes unpacked)",
          primaryCode: gDecomp,
          codeFileOffset: 0,
          headerLoadAddress: null,
          dtbs: [],
          subPartitions: [],
          metadata: {}
        };
      }
    }

    return {
      inputName: fileName,
      rawSize: rawData.length,
      formatType: "RAW_BINARY",
      evidence: "Raw ARM executable / firmware payload (" + rawData.length + " bytes)",
      primaryCode: rawData,
      codeFileOffset: 0,
      headerLoadAddress: null,
      dtbs: extractEmbeddedDtbs(rawData, "raw"),
      subPartitions: [],
      metadata: {}
    };
  }

  function scoreBase32(data, words, base) {
    var endVa = base + data.length;
    var codeLim = base + Math.floor((data.length * 3) / 4);
    var n = words.length;
    var step = n <= 1500000 ? 1 : Math.max(1, Math.floor(n / 1500000));
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    var hits = 0;
    for (var i = 0; i < n - 4; i += step) {
      var w0 = words[i];
      var w1 = words[i + 1];
      if (w0 < base + 0x100 || w0 >= endVa || w1 < base || w1 >= codeLim) continue;
      if ((w1 & 3) > 1) continue;
      var sOff = w0 - base;
      if (sOff + 4 >= data.length) continue;
      var b0 = data[sOff];
      if (!((b0 >= 97 && b0 <= 122) || (b0 >= 65 && b0 <= 90) || b0 === 95)) continue;
      if (asciiAt(data, sOff, 48).length < 4) continue;
      var cOff = ((w1 & ~1) >>> 0) - base;
      if (cOff < 0 || cOff + 4 >= data.length) continue;
      if (w1 & 1) {
        var hw = dv.getUint16(cOff, true);
        if ((hw & 0xff00) === 0xb500 || (hw & 0xff00) === 0xe900 || (hw & 0xf800) === 0xf000) hits++;
      } else {
        var ins = dv.getUint32(cOff, true);
        if ((ins >>> 28) === 0xe) hits++;
      }
      if (hits >= 180) break;
    }
    return hits;
  }

  function recoverCrt0Base32(data) {
    if (data.length < 0x100) return null;
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    var w0 = dv.getUint32(0, true);
    if ((w0 >>> 24) !== 0xea) return null;
    var imm24 = w0 & 0x00ffffff;
    if (imm24 & 0x800000) imm24 -= 0x1000000;
    var resetOff = 8 + (imm24 << 2);
    if (resetOff < 0x18 || resetOff >= Math.min(data.length, 0x400)) return null;
    var lits = [];
    for (var o = resetOff; o + 4 <= Math.min(data.length, resetOff + 0xa0); o += 4) {
      var ins = dv.getUint32(o, true);
      if ((ins & 0x0fff0000) === 0x059f0000) {
        var disp = ins & 0xfff;
        var litOff = o + 8 + disp;
        if (litOff + 4 <= data.length) lits.push(dv.getUint32(litOff, true));
      }
    }
    for (var i = 0; i + 1 < lits.length; i++) {
      var v1 = lits[i];
      var v2 = lits[i + 1];
      if ((v1 & 0xffff) === 0 && v2 > v1 && Math.abs((v2 - v1) - data.length) <= 0x20000) {
        return { address: v1, method: "crt0_self_relocation_literal_pool", status: "CONFIRMED", confidence: 0.99 };
      }
    }
    return null;
  }

  function detectArchitectureAndBase(payload) {
    var data = payload.primaryCode;
    if (!data || !data.length) {
      return { architecture: "NON_EXECUTABLE", pointerSize: 4, baseAddress: 0n, baseMethod: "not_applicable", baseStatus: "CONFIRMED", baseConfidence: 1.0 };
    }
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    var isArm64 = payload.elfMachine === 183 || (data.length >= 0x40 && data[0x38] === 0x41 && data[0x39] === 0x52 && data[0x3a] === 0x4d && data[0x3b] === 0x64);

    if (isArm64) {
      var textOff = (data.length >= 0x40 && data[0x38] === 0x41 && data[0x39] === 0x52 && data[0x3a] === 0x4d && data[0x3b] === 0x64) ? Number(dv.getBigUint64(8, true)) : 0x80000;
      if (textOff !== 0 && textOff !== 0x10000 && textOff !== 0x80000) textOff = 0x80000;
      var qwordsLen = Math.floor(data.length / 8);
      var qView = (data.byteOffset & 7) === 0
        ? new BigUint64Array(data.buffer, data.byteOffset, qwordsLen)
        : new BigUint64Array(data.slice(0, qwordsLen * 8).buffer);
      var cands64 = [
        0xffffff8008000000n + BigInt(textOff),
        0xffffffc010000000n + BigInt(textOff),
        0xffffffc008000000n + BigInt(textOff),
        0xffffff8008000000n
      ];
      var best64 = cands64[0];
      var bestScore64 = -1;
      for (var c = 0; c < cands64.length; c++) {
        var b64 = cands64[c];
        var end64 = b64 + BigInt(data.length);
        var clim64 = b64 + BigInt(Math.floor((data.length * 3) / 4));
        var step64 = Math.max(1, Math.floor(qwordsLen / 500000));
        var chits = 0;
        var shits = 0;
        for (var q = 0; q < qwordsLen; q += step64) {
          var qv = qView[q];
          if (qv < b64 + 0x100n || qv >= end64) continue;
          var qoff = Number(qv - b64);
          if (qv < clim64) {
            if ((qoff & 3) === 0 && qoff + 4 <= data.length) {
              var i64 = dv.getUint32(qoff, true);
              if (((i64 & 0xffc003ff) >>> 0) === 0xa98003fd || ((i64 & 0xff00001f) >>> 0) === 0xd10003ff || ((i64 & 0x9f000000) >>> 0) === 0x90000000) chits++;
            }
          } else if (qoff + 4 <= data.length && (qoff === 0 || data[qoff - 1] === 0)) {
            if (asciiAt(data, qoff, 48).length >= 4) shits++;
          }
          if (chits >= 50 && shits >= 50) break;
        }
        var tot = (chits > 0 && shits > 0) ? (chits + shits * 2) : (chits + shits);
        if (tot > bestScore64) {
          bestScore64 = tot;
          best64 = b64;
        }
        if (bestScore64 >= 150 && b64 === 0xffffff8008080000n) break;
      }
      return {
        architecture: "ARM64",
        pointerSize: 8,
        baseAddress: best64,
        baseMethod: "arm64_va_pointer_alignment",
        baseStatus: bestScore64 >= 40 ? "CONFIRMED" : "INFERRED",
        baseConfidence: bestScore64 >= 40 ? 0.96 : 0.72
      };
    }

    var crt0 = recoverCrt0Base32(data);
    if (crt0) {
      return {
        architecture: "THUMB",
        pointerSize: 4,
        baseAddress: crt0.address,
        baseMethod: crt0.method,
        baseStatus: crt0.status,
        baseConfidence: crt0.confidence
      };
    }

    var alignedWords = Math.floor(data.length / 4);
    var words = (data.byteOffset & 3) === 0
      ? new Uint32Array(data.buffer, data.byteOffset, alignedWords)
      : new Uint32Array(data.slice(0, alignedWords * 4).buffer);
    var cands32 = [0xc0008000, 0x48000000, 0x48200000, 0x81e00000, 0xc0000000, 0x80008000, 0x40008000];
    if (payload.headerLoadAddress) cands32.unshift(payload.headerLoadAddress >>> 0);
    var best32 = payload.headerLoadAddress || 0xc0008000;
    var bestScore32 = payload.headerLoadAddress ? 200 : -1;

    if (!payload.headerLoadAddress) {
      for (var j = 0; j < cands32.length; j++) {
        var sc = scoreBase32(data, words, cands32[j]);
        if (sc > bestScore32) {
          bestScore32 = sc;
          best32 = cands32[j];
        }
        if (cands32[j] === 0xc0008000 && sc >= 120) break;
      }
    }

    var thumbHits = 0;
    var armHits = 0;
    var probeEnd = Math.min(data.length - 4, 0x8000);
    for (var k = 0; k < probeEnd; k += 2) {
      var hw = dv.getUint16(k, true);
      if ((hw & 0xfe00) === 0xb400 || (hw & 0xff00) === 0xe900) thumbHits++;
      if ((k & 3) === 0) {
        var aw = dv.getUint32(k, true);
        if (((aw & 0xffff0000) >>> 0) === 0xe92d0000 || ((aw & 0xffff0000) >>> 0) === 0xe52d0000) armHits++;
      }
    }
    var isLk = payload.formatType === "MTK_LK" || hasAscii(data, "welcome to lk") || hasAscii(data, "mt_disp_init");
    var archName = (thumbHits > armHits * 2 || isLk) ? "THUMB" : "ARM32";
    return {
      architecture: archName,
      pointerSize: 4,
      baseAddress: best32 >>> 0,
      baseMethod: payload.headerLoadAddress ? "firmware_header_load_addr" : "pointer_string_code_alignment",
      baseStatus: bestScore32 >= 25 ? "CONFIRMED" : "INFERRED",
      baseConfidence: bestScore32 >= 25 ? 0.95 : 0.72
    };
  }

  function detectFramework(payload, arch, data) {
    if (payload.formatType === "FDT_DTB" || payload.formatType === "DTBO_IMG") return "DEVICE_TREE_PANEL";
    var hasDrm = hasAscii(data, "drm_panel_init") || hasAscii(data, "drm_panel_add");
    var hasMtkDsi = hasAscii(data, "mtk_dsi_probe");
    var hasDispLcm = hasAscii(data, "disp_lcm_probe") || hasAscii(data, "disp_lcm_init");
    var hasMtkfb = hasAscii(data, "mtkfb_find_lcm_driver");
    var hasDispGet = hasAscii(data, "disp_drv_get_lcm_driver");
    var hasDts = hasAscii(data, "lcm_common_parse_dts");
    var isLk = payload.formatType === "MTK_LK" || hasAscii(data, "welcome to lk") || hasAscii(data, "mt_disp_init");
    var hasLinux = hasAscii(data, "Linux version ");

    if (hasDrm && (arch.architecture === "ARM64" || (!hasDispLcm && !hasMtkfb && !hasDispGet))) {
      return hasMtkDsi ? "LINUX_DRM_PANEL_MTK" : "LINUX_DRM_PANEL_GENERIC";
    }
    if (isLk && !hasLinux) {
      if (hasDts) return "MTK_LK_DTS";
      if (hasAscii(data, "dsc_params") || hasAscii(data, "DISP_AAL0_TO_DISP_GAMMA0_VALID") || hasAscii(data, "VDO_MODE")) return "MTK_LK_SHIFTED";
      return "MTK_LK_LEGACY";
    }
    if (hasDispGet || hasAscii(data, "Linux version 3.4")) return "MTK_KERNEL_LEGACY_3_4";
    if (hasAscii(data, "Linux version 3.10") || hasAscii(data, "Linux version 3.18")) return "MTK_KERNEL_LEGACY_3_18";
    if (hasDispLcm || hasMtkfb || hasLinux) return "MTK_KERNEL_LEGACY_4_9";
    return "UNKNOWN";
  }

  function looksLikeCodeEntry32(data, base, va) {
    var clean = (va & ~1) >>> 0;
    if (clean < base + 0x100 || clean >= base + data.length - 4) return false;
    var off = clean - base;
    if (va & 1) {
      var hw = data[off] | (data[off + 1] << 8);
      return hw !== 0 && hw !== 0xffff;
    }
    if ((va & 3) !== 0) return false;
    var w = (data[off] | (data[off + 1] << 8) | (data[off + 2] << 16) | (data[off + 3] << 24)) >>> 0;
    return (w >>> 28) === 0xe;
  }

  function analyzeProfileQuick32(data, base, va) {
    var isThumb = (va & 1) !== 0;
    var clean = (va & ~1) >>> 0;
    var startOff = clean - base;
    if (startOff < 0 || startOff + 4 > data.length) return { size: 0, insns: 0, tailJump: null, lits: [] };
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    var lits = AE.resolvePointerLiterals(data, base, va, 0x120);
    var maxEnd = Math.min(data.length, startOff + 0x240);
    var pos = startOff;
    var insns = 0;
    var tailJump = null;
    if (isThumb) {
      while (pos + 2 <= maxEnd) {
        insns++;
        var hw1 = dv.getUint16(pos, true);
        if ((hw1 & 0xf800) >= 0xe800 && pos + 4 <= maxEnd) {
          var hw2 = dv.getUint16(pos + 2, true);
          if ((hw1 & 0xf800) === 0xf000 && (hw2 & 0xd000) === 0x9000) {
            var s = (hw1 >>> 10) & 1;
            var j1 = (hw2 >>> 13) & 1;
            var j2 = (hw2 >>> 11) & 1;
            var i1 = (~(j1 ^ s)) & 1;
            var i2 = (~(j2 ^ s)) & 1;
            var imm = (s << 24) | (i1 << 23) | (i2 << 22) | ((hw1 & 0x3ff) << 12) | ((hw2 & 0x7ff) << 1);
            var signed = (imm << 7) >> 7;
            var t = ((base + pos + 4 + signed) | 1) >>> 0;
            if (Math.abs(t - va) > 0x400) { tailJump = t; pos += 4; break; }
          }
          if (hw1 === 0xe8bd && (hw2 & 0x8000) !== 0) { pos += 4; break; }
          pos += 4;
          continue;
        }
        if (hw1 === 0x4770 || ((hw1 & 0xfe00) === 0xbc00 && (hw1 & 0x0100) !== 0)) { pos += 2; break; }
        pos += 2;
      }
    } else {
      for (; pos + 4 <= maxEnd; pos += 4) {
        insns++;
        var w = dv.getUint32(pos, true);
        if ((w & 0x0fff0fff) === 0x012fff1e || (w & 0x0fff8000) === 0x08bd8000) { pos += 4; break; }
        if (((w & 0xff000000) >>> 0) === 0xea000000) {
          var imm24 = ((w & 0xffffff) << 8) >> 8;
          var tA = (base + pos + 8 + (imm24 << 2)) >>> 0;
          if (Math.abs(tA - va) > 0x400) { tailJump = tA; pos += 4; break; }
        }
      }
    }
    return { size: pos - startOff, insns: insns, tailJump: tailJump, lits: lits };
  }

  function inferUtilSlotMap(events, compareEvents) {
    var bySlot = new Map();
    for (var i = 0; i < events.length; i++) {
      var ev = events[i];
      if (ev.kind === "UTIL_SLOT" && ev.slotOffset !== null) {
        if (!bySlot.has(ev.slotOffset)) bySlot.set(ev.slotOffset, []);
        bySlot.get(ev.slotOffset).push(ev);
      }
    }
    var map = {};
    bySlot.forEach(function (evs, slotOff) {
      if (evs.some(function (e) { return e.tableV3Ops && e.tableV3Ops.length > 0; })) {
        map[slotOff] = "dsi_set_cmdq_V3";
        return;
      }
      if (evs.some(function (e) { return e.arg2Bytes.length > 0 || (e.args[0] <= 0xff && e.args[1] <= 128 && (e.args[3] === 0 || e.args[3] === 1) && e.args[2] >= 0x10000); })) {
        map[slotOff] = "dsi_set_cmdq_V2";
        return;
      }
      if (evs.some(function (e) { return e.arg0Words.length > 0; })) {
        map[slotOff] = "dsi_set_cmdq";
        return;
      }
      if (evs.some(function (e) { return e.args[0] >= 0x10000 && e.args[1] >= 1 && e.args[1] <= 1024 && (e.args[2] === 0 || e.args[2] === 1 || e.args[2] === 2); })) {
        map[slotOff] = "dsi_set_cmdq_V3";
        return;
      }
      if (slotOff === 0 && evs.every(function (e) { return e.args[0] === 0 || e.args[0] === 1; })) {
        map[slotOff] = "set_reset_pin";
        return;
      }
      if (slotOff >= 0x4c && evs.every(function (e) { return e.args[0] === 0 || e.args[0] === 1; })) {
        map[slotOff] = "set_gpio_lcd_enp_bias";
        return;
      }
      if (evs.every(function (e) { return e.args[0] >= 1 && e.args[0] <= 2000; })) {
        map[slotOff] = slotOff >= 0x0c ? "mdelay" : "udelay";
      }
    });
    if (compareEvents) {
      for (var c = 0; c < compareEvents.length; c++) {
        var ce = compareEvents[c];
        if (ce.kind === "UTIL_SLOT" && ce.slotOffset !== null && !(ce.slotOffset in map)) {
          if (ce.args[0] <= 0xff && ce.args[1] >= 0x10000 && ce.args[2] >= 1 && ce.args[2] <= 32) {
            map[ce.slotOffset] = "dsi_dcs_read_lcm_reg_v2";
          } else if (ce.slotOffset === 0 && (ce.args[0] === 0 || ce.args[0] === 1)) {
            map[ce.slotOffset] = "set_reset_pin";
          } else if (ce.arg0Words.length > 0) {
            map[ce.slotOffset] = "dsi_set_cmdq";
          }
        }
      }
    }
    return map;
  }

  function eventsToOps(events, slotRoles, data, base) {
    var ops = [];
    for (var i = 0; i < events.length; i++) {
      var ev = events[i];
      if (ev.kind === "UTIL_SLOT" && ev.slotOffset !== null) {
        var role = slotRoles[ev.slotOffset] || "";
        if (role === "dsi_set_cmdq_V3") {
          if (ev.tableV3Ops && ev.tableV3Ops.length > 0) {
            for (var v3 = 0; v3 < ev.tableV3Ops.length; v3++) ops.push(ev.tableV3Ops[v3]);
          } else if (ev.args[0] >= 0x10000 && data && base) {
            var dynOps = AE.tryDecodeSettingTableV3(data, base, ev.args[0], ev.args[1]);
            for (var d3 = 0; d3 < dynOps.length; d3++) ops.push(dynOps[d3]);
          }
        } else if (role === "dsi_set_cmdq_V2") {
          var cnt = ev.args[1] & 0xff;
          ops.push({ opType: "DCS_WRITE", cmd: ev.args[0] & 0xff, params: ev.arg2Bytes.slice(0, cnt), delayValue: null, pinOrRail: null, pinLevel: null, sourceAddress: ev.callSite, status: "CONFIRMED", rawEncoding: "slot+0x" + ev.slotOffset.toString(16) });
        } else if (role === "dsi_set_cmdq" && ev.arg0Words.length > 0) {
          var packed = AE.decodePackedCmdqWords(ev.arg0Words, ev.callSite);
          for (var p = 0; p < packed.length; p++) ops.push(packed[p]);
        } else if (role === "dsi_dcs_read_lcm_reg_v2") {
          ops.push({ opType: "DCS_READ", cmd: ev.args[0] & 0xff, params: [], delayValue: ev.args[2] & 0xff, pinOrRail: null, pinLevel: null, sourceAddress: ev.callSite, status: "CONFIRMED", rawEncoding: "read_len=" + ev.args[2] });
        } else if (role === "set_reset_pin") {
          ops.push({ opType: "RESET_PIN", cmd: null, params: [], delayValue: null, pinOrRail: "LCM_RESET", pinLevel: ev.args[0] ? 1 : 0, sourceAddress: ev.callSite, status: "CONFIRMED", rawEncoding: "slot+0x" + ev.slotOffset.toString(16) });
        } else if (role === "mdelay") {
          ops.push({ opType: "DELAY_MS", cmd: null, params: [], delayValue: ev.args[0], pinOrRail: null, pinLevel: null, sourceAddress: ev.callSite, status: "CONFIRMED", rawEncoding: "slot+0x" + ev.slotOffset.toString(16) });
        } else if (role === "udelay") {
          ops.push({ opType: "DELAY_US", cmd: null, params: [], delayValue: ev.args[0], pinOrRail: null, pinLevel: null, sourceAddress: ev.callSite, status: "CONFIRMED", rawEncoding: "slot+0x" + ev.slotOffset.toString(16) });
        } else if (role === "set_gpio_lcd_enp_bias") {
          ops.push({ opType: "GPIO_OUT", cmd: null, params: [], delayValue: null, pinOrRail: "LCD_BIAS_ENP", pinLevel: ev.args[0] ? 1 : 0, sourceAddress: ev.callSite, status: "INFERRED", rawEncoding: "slot+0x" + ev.slotOffset.toString(16) });
        }
      } else if (ev.kind === "EXTERNAL_CALL") {
        if ((ev.args[0] === 0 || ev.args[0] === 1) && ev.args[1] === 0 && ev.callSite) {
          ops.push({ opType: "GPIO_OUT", cmd: null, params: [], delayValue: null, pinOrRail: "EXT_0x" + ev.targetVa.toString(16), pinLevel: ev.args[0], sourceAddress: ev.callSite, status: "INFERRED", rawEncoding: "ext_call" });
        }
      }
    }
    return ops;
  }

  function extractParamsFromRaw(raw, written, gpVa) {
    var dv = new DataView(raw.buffer, raw.byteOffset, raw.byteLength);
    var words = [];
    for (var o = 0; o + 4 <= raw.length; o += 4) words.push(dv.getUint32(o, true));
    var timings = {};
    var dsiConfig = {};
    var esdItems = [];
    var lcmType = words[0];
    var iface = lcmType === 1 ? "DPI_RGB" : (lcmType === 0 ? "DBI_MCU" : "MIPI_DSI");

    var w = 0;
    var h = 0;
    var wOff = 0x18;
    var hOff = 0x1c;
    if (words[6] >= 120 && words[6] <= 4096 && words[7] >= 120 && words[7] <= 4096) {
      w = words[6]; h = words[7]; wOff = 0x18; hOff = 0x1c;
    } else if (words[2] >= 120 && words[2] <= 4096 && words[3] >= 120 && words[3] <= 4096) {
      w = words[2]; h = words[3]; wOff = 0x08; hOff = 0x0c;
    } else {
      return { timings: timings, dsiConfig: dsiConfig, esdItems: esdItems, iface: iface, validGeom: false };
    }

    function mkEv(val, off) {
      return { value: val, location: "LCM_PARAMS+0x" + off.toString(16).toUpperCase().padStart(3, "0"), sourceAddress: gpVa, status: "CONFIRMED" };
    }

    timings.width = mkEv(w, wOff);
    timings.height = mkEv(h, hOff);

    var anchor = null;
    var strides = [0x14, 0x10];
    for (var s = 0; s < strides.length && !anchor; s++) {
      var step = strides[s] / 4;
      for (var idx = 0x20; idx < words.length - step - 4; idx++) {
        if (words[idx] === h && words[idx + step] === w) {
          anchor = { vactOff: idx * 4, hactOff: (idx + step) * 4, stride: strides[s] };
          break;
        }
      }
    }

    if (anchor) {
      var vi = anchor.vactOff / 4;
      timings.vertical_active_line = mkEv(h, anchor.vactOff);
      timings.horizontal_active_pixel = mkEv(w, anchor.hactOff);
      var vMap = anchor.stride === 0x14 ? [["vsa", -4], ["vbp", -3], ["vfp", -2]] : [["vsa", -3], ["vbp", -2], ["vfp", -1]];
      for (var vm = 0; vm < vMap.length; vm++) {
        var tname = vMap[vm][0];
        var dlt = vMap[vm][1];
        timings[tname] = mkEv(words[vi + dlt], (vi + dlt) * 4);
      }
      var hMap = [["hsa", 1], ["hbp", 2], ["hfp", 3]];
      for (var hm = 0; hm < hMap.length; hm++) {
        timings[hMap[hm][0]] = mkEv(words[vi + hMap[hm][1]], (vi + hMap[hm][1]) * 4);
      }
      var laneOff = null;
      var laneDeltas = [0x38, 0x3c, 0x30];
      for (var ld = 0; ld < laneDeltas.length; ld++) {
        var candL = anchor.vactOff - laneDeltas[ld];
        if (candL >= 0 && words[candL / 4] >= 1 && words[candL / 4] <= 4) { laneOff = candL; break; }
      }
      if (laneOff !== null) {
        dsiConfig.lanes = mkEv(words[laneOff / 4], laneOff);
        var modeOff = laneOff - anchor.stride;
        if (modeOff >= 0) {
          var mv = words[modeOff / 4];
          dsiConfig.mode = mkEv(mv, modeOff);
          dsiConfig.mode_name = { value: DSI_MODE_NAMES[mv] || ("MODE_" + mv), location: "LCM_PARAMS+0x" + modeOff.toString(16).toUpperCase().padStart(3, "0"), sourceAddress: gpVa, status: "INFERRED" };
        }
      }
      var psOff = anchor.vactOff - (anchor.stride === 0x14 ? 0x20 : 0x18);
      if (psOff >= 0 && words[psOff / 4] in DSI_PS_NAMES) {
        dsiConfig.ps = mkEv(words[psOff / 4], psOff);
      }
      var pktOff = anchor.vactOff - (anchor.stride === 0x14 ? 0x18 : 0x10);
      if (pktOff >= 0 && words[pktOff / 4] > 0) dsiConfig.packet_size = mkEv(words[pktOff / 4], pktOff);

      var pllOff = null;
      var pllDeltas = [0x58, 0x5c, 0x64];
      for (var pd = 0; pd < pllDeltas.length; pd++) {
        var co = anchor.hactOff + pllDeltas[pd];
        if (co < raw.length && (co in written) && words[co / 4] >= 40 && words[co / 4] <= 1200) { pllOff = co; break; }
      }
      if (pllOff !== null) {
        var pll = words[pllOff / 4];
        timings.pll_clock = mkEv(pll, pllOff);
        if (pllOff + 4 < raw.length && words[(pllOff + 4) / 4] === pll * 2) {
          timings.data_rate = mkEv(pll * 2, pllOff + 4);
        }
        var dscDeltas = [0x20, 0x24, 0x28];
        for (var dd = 0; dd < dscDeltas.length; dd++) {
          var doff = pllOff + dscDeltas[dd];
          if ((doff in written) && words[doff / 4] === 1 && doff + 0x20 < raw.length) {
            var ver = words[(doff + 0x1c) / 4];
            if (ver === 8 || ver === 10 || ver === 12 || ver === 16 || ver === 17) {
              dsiConfig.dsc_enable = mkEv(1, doff);
              break;
            }
          }
        }
      }
      var esdPos = anchor.hactOff + 0x100;
      var esdLim = Math.min(raw.length - 8, 0x460);
      while (esdPos < esdLim && esdItems.length < 3) {
        if ((esdPos in written) || ((esdPos + 1) in written)) {
          var ecmd = raw[esdPos];
          var ecnt = raw[esdPos + 1];
          if (ecmd >= 4 && ecmd <= 0xfe && ecnt >= 1 && ecnt <= 8) {
            var ep = [];
            for (var x = 0; x < ecnt; x++) ep.push(raw[esdPos + 2 + x]);
            if (ep.some(function (v) { return v !== 0; }) || ecmd === 0x0a || ecmd === 0x09 || ecmd === 0x68 || ecmd === 0xaf) {
              esdItems.push({ cmd: ecmd, count: ecnt, expectedParams: ep, sourceAddress: gpVa });
            }
          }
        }
        esdPos += 4;
      }
    }

    return { timings: timings, dsiConfig: dsiConfig, esdItems: esdItems, iface: iface, rawStores: written, validGeom: true };
  }

  function discoverArm32Drivers(payload, arch, framework) {
    var data = payload.primaryCode;
    var base = arch.baseAddress >>> 0;
    var endVa = (base + data.length) >>> 0;
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    var nWords = Math.floor(data.length / 4);
    var words = (data.byteOffset & 3) === 0
      ? new Uint32Array(data.buffer, data.byteOffset, nWords)
      : new Uint32Array(data.slice(0, nWords * 4).buffer);

    var firstXref = new Map();
    for (var wi = 0; wi < nWords; wi++) {
      var val = words[wi];
      if (val >= base && val < endVa && !firstXref.has(val)) {
        firstXref.set(val, (base + wi * 4) >>> 0);
      }
    }

    var allowNull = framework === "MTK_LK_DTS" || hasAscii(data, "lcm_common_parse_dts");
    var emu = new AE.ArmMicroEmulator(data, base, arch.architecture);
    var candidates = [];

    for (var idx = 0; idx < nWords - 12; idx++) {
      var w1 = words[idx + 1];
      if (w1 < base + 0x100 || w1 >= endVa || !looksLikeCodeEntry32(data, base, w1)) continue;
      var w2 = words[idx + 2];
      var w3 = words[idx + 3];
      var c2 = w2 >= base + 0x100 && w2 < endVa && w2 !== w1;
      var c3 = w3 >= base + 0x100 && w3 < endVa && w3 !== w1;
      if (!c2 && !c3) continue;

      var w0 = words[idx];
      if (w0 === 0) {
        if (!allowNull) continue;
      } else if (w0 < base || w0 >= endVa) {
        continue;
      }

      var zcnt = 0;
      var tailOk = true;
      for (var t = 6; t < 13 && idx + t < nWords; t++) {
        var tw = words[idx + t];
        if (tw === 0) zcnt++;
        else if (tw < base || tw >= endVa) { tailOk = false; break; }
      }
      if (!tailOk || zcnt < 1) continue;

      var structVa = (base + idx * 4) >>> 0;
      if (!firstXref.has(structVa)) continue;

      var codeHits = 0;
      var uniq = new Set();
      for (var s = 1; s <= 6; s++) {
        var sw = words[idx + s];
        if (looksLikeCodeEntry32(data, base, sw)) {
          codeHits++;
          uniq.add(sw);
        }
      }
      if (codeHits < 3 || uniq.size < 3) continue;

      var dname = "";
      if (w0 !== 0) {
        dname = readCStringVa(data, base, w0, 3, 96);
        if (!dname || dname.indexOf(" ") !== -1) continue;
      }
      candidates.push(structVa);
    }

    var roleNamesStd = { 6: "init_power", 7: "suspend_power", 8: "resume_power", 9: "update", 10: "compare_id", 11: "parse_dts", 12: "set_backlight", 13: "set_backlight_cmdq", 18: "esd_check", 19: "esd_recover", 21: "ata_check" };
    var roleNamesShift = { 7: "init_power", 8: "suspend_power", 9: "resume_power", 10: "update", 11: "compare_id", 12: "set_backlight", 13: "set_backlight_cmdq", 14: "esd_check", 16: "ata_check" };
    var drivers = [];
    var seen = new Set();

    function processStruct(structVa, method) {
      if (seen.has(structVa)) return;
      var sOff = (structVa - base) >>> 0;
      if (sOff + 48 > data.length) return;
      var w0 = dv.getUint32(sOff, true);
      var dname = w0 ? readCStringVa(data, base, w0, 2, 96) : ("lcm_0x" + structVa.toString(16));
      if (!dname || dname.indexOf(" ") !== -1) return;

      var slots = [];
      for (var k = 0; k < 26 && sOff + k * 4 + 4 <= data.length; k++) {
        slots.push(dv.getUint32(sOff + k * 4, true));
      }
      var gpIdx = null;
      var gpRes = null;
      var gpOrder = [2, 3];
      for (var gi = 0; gi < gpOrder.length; gi++) {
        var candIdx = gpOrder[gi];
        var candVa = slots[candIdx];
        if (candVa && looksLikeCodeEntry32(data, base, candVa)) {
          var res = emu.executeGetParams(candVa, 0x580, 900);
          var par = extractParamsFromRaw(res.raw, res.written, candVa);
          if (par.validGeom) {
            gpIdx = candIdx;
            gpRes = par;
            break;
          }
        }
      }
      if (gpIdx === null) return;
      seen.add(structVa);

      var variant = gpIdx === 3 ? "shifted_slot2_null" : "standard";
      var functions = {};
      var setUtilIdx = looksLikeCodeEntry32(data, base, slots[1]) ? 1 : null;
      if (setUtilIdx !== null) {
        var suProf = analyzeProfileQuick32(data, base, slots[1]);
        functions.set_util_funcs = { role: "set_util_funcs", slotIndex: 1, address: slots[1], mode: (slots[1] & 1) ? "THUMB" : "ARM", size: suProf.size, status: "CONFIRMED" };
      }
      var gpProf = analyzeProfileQuick32(data, base, slots[gpIdx]);
      functions.get_params = { role: "get_params", slotIndex: gpIdx, address: slots[gpIdx], mode: (slots[gpIdx] & 1) ? "THUMB" : "ARM", size: gpProf.size, status: "CONFIRMED" };

      var baseRoles = [
        ["init", gpIdx + 1],
        ["suspend", gpIdx + 2],
        ["resume", gpIdx + 3]
      ];
      for (var br = 0; br < baseRoles.length; br++) {
        var rName = baseRoles[br][0];
        var rSlot = baseRoles[br][1];
        if (slots[rSlot] && looksLikeCodeEntry32(data, base, slots[rSlot])) {
          var pf = analyzeProfileQuick32(data, base, slots[rSlot]);
          functions[rName] = { role: rName, slotIndex: rSlot, address: slots[rSlot], mode: (slots[rSlot] & 1) ? "THUMB" : "ARM", size: pf.size, tailJump: pf.tailJump, status: "INFERRED" };
        }
      }

      var optMap = variant === "shifted_slot2_null" ? roleNamesShift : roleNamesStd;
      for (var sKey in optMap) {
        var sNum = Number(sKey);
        var oVa = slots[sNum];
        if (oVa && looksLikeCodeEntry32(data, base, oVa)) {
          var opf = analyzeProfileQuick32(data, base, oVa);
          functions[optMap[sKey]] = { role: optMap[sKey], slotIndex: sNum, address: oVa, mode: (oVa & 1) ? "THUMB" : "ARM", size: opf.size, status: "INFERRED" };
        }
      }
      if (gpIdx === 3 && slots[2] && looksLikeCodeEntry32(data, base, slots[2])) {
        var gnProf = analyzeProfileQuick32(data, base, slots[2]);
        functions.get_name = { role: "get_name", slotIndex: 2, address: slots[2], mode: (slots[2] & 1) ? "THUMB" : "ARM", size: gnProf.size, status: "INFERRED" };
      }

      var suVa = functions.set_util_funcs ? functions.set_util_funcs.address : null;
      var initEvs = functions.init ? emu.executeWithUtilTraps(suVa, functions.init.address) : [];
      var suspEvs = functions.suspend ? emu.executeWithUtilTraps(suVa, functions.suspend.address) : [];
      var cmpEvs = functions.compare_id ? emu.executeWithUtilTraps(suVa, functions.compare_id.address) : [];

      var slotRoles = inferUtilSlotMap(initEvs.concat(suspEvs), cmpEvs);
      var initOps = eventsToOps(initEvs, slotRoles, data, base);
      if (!initOps.some(function (op) { return op.opType === "DCS_WRITE"; }) && functions.init) {
        var stOps = AE.findStaticSettingTable(data, base, functions.init.address);
        if (stOps.length) initOps = initOps.concat(stOps);
      }
      var suspOps = eventsToOps(suspEvs, slotRoles, data, base);
      if (!suspOps.some(function (op) { return op.opType === "DCS_WRITE"; }) && functions.suspend) {
        var stSusp = AE.findStaticSettingTable(data, base, functions.suspend.address);
        if (stSusp.length) suspOps = suspOps.concat(stSusp);
      }

      var resetSeq = [];
      for (var ri = 0; ri < initOps.length; ri++) {
        var rop = initOps[ri];
        if (rop.opType === "DCS_WRITE") break;
        if (rop.opType === "RESET_PIN" || rop.opType === "DELAY_MS" || rop.opType === "DELAY_US") resetSeq.push(rop);
      }

      var idDet = null;
      if (functions.compare_id) {
        var cmpOps = eventsToOps(cmpEvs, slotRoles, data, base);
        var expIds = AE.extractExpectedIdsStatic(data, base, functions.compare_id.address);
        var readOp = cmpOps.find(function (op) { return op.opType === "DCS_READ"; });
        idDet = {
          sourceAddress: functions.compare_id.address,
          readCommand: readOp ? readOp.cmd : null,
          readLength: readOp ? (readOp.delayValue || 0) : 0,
          expectedIds: expIds
        };
      }

      drivers.push({
        name: dname,
        framework: framework,
        interfaceType: gpRes.iface,
        structAddress: structVa,
        xrefAddress: firstXref.get(structVa) || null,
        utilSlotMap: slotRoles,
        functions: functions,
        timings: gpRes.timings,
        dsiConfig: gpRes.dsiConfig,
        esdItems: gpRes.esdItems,
        initSequence: initOps,
        suspendSequence: suspOps,
        resetSequence: resetSeq,
        idDetection: idDet,
        discoveryMethod: method,
        compatible: null,
        platformDependencies: []
      });
    }

    for (var ci = 0; ci < candidates.length; ci++) {
      var sva = candidates[ci];
      processStruct(sva, "pointer_table_behavioral_scan");
      var xva = firstXref.get(sva);
      if (xva && xva >= base && xva < endVa) {
        var xIdx = ((xva - base) / 4) | 0;
        for (var d = -12; d <= 12; d++) {
          var posIdx = xIdx + d;
          if (posIdx >= 0 && posIdx < nWords) {
            var ptrVal = words[posIdx];
            if (ptrVal >= base && ptrVal < endVa - 32 && (ptrVal & 3) === 0 && !seen.has(ptrVal)) {
              processStruct(ptrVal, "lcm_driver_list_traversal");
            }
          }
        }
      }
    }
    return drivers;
  }

  function discoverArm64Drivers(payload, arch, framework) {
    var data = payload.primaryCode;
    var baseLo = BigInt.asUintN(64, BigInt(arch.baseAddress));
    var endVa = baseLo + BigInt(data.length);
    var codeEnd = baseLo + BigInt(Math.floor((data.length * 4) / 5));
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    var nQ = Math.floor(data.length / 8);
    var qwords = (data.byteOffset & 7) === 0
      ? new BigUint64Array(data.buffer, data.byteOffset, nQ)
      : new BigUint64Array(data.slice(0, nQ * 8).buffer);

    function isCodePtr(va) {
      if (va < baseLo + 0x100n || va >= codeEnd || (va & 3n) !== 0n) return false;
      var off = Number(va - baseLo);
      if (off + 4 > data.length) return false;
      var w = dv.getUint32(off, true);
      return w !== 0 && w !== 0xffffffff;
    }

    var drivers = [];
    var seen = new Set();

    for (var idx = 0; idx < nQ - 24; idx++) {
      if (qwords[idx + 1] !== 0n || qwords[idx + 2] !== 0n) continue;
      var q0 = qwords[idx];
      if (q0 < baseLo || q0 >= endVa) continue;
      var qOff = Number(q0 - baseLo);
      var dname = asciiAt(data, qOff, 96);
      if (!dname || dname.length < 4 || dname.indexOf(" ") !== -1) continue;

      var compat = null;
      var ofVa = null;
      for (var oi = 2; oi < 10; oi++) {
        var candOf = qwords[idx + oi];
        if (candOf >= baseLo && candOf < endVa - 200n) {
          var cOff = Number(candOf - baseLo) + 0x40;
          var cs = asciiAt(data, cOff, 120);
          if (cs.length >= 4 && cs.indexOf(",") !== -1 && cs.indexOf(" ") === -1) {
            compat = cs;
            ofVa = candOf;
            break;
          }
        }
      }
      if (!compat) continue;

      var probeVa = null;
      var remVa = null;
      for (var pi = 11; pi < 22; pi++) {
        if (isCodePtr(qwords[idx + pi])) {
          probeVa = qwords[idx + pi];
          if (isCodePtr(qwords[idx + pi + 1])) remVa = qwords[idx + pi + 1];
          break;
        }
      }
      if (!probeVa) continue;

      var structVa = baseLo + BigInt(idx * 8);
      if (seen.has(structVa)) continue;

      var pFlow = AE.analyzeArm64FunctionFlow(data, baseLo, probeVa, 0x1000);
      var funcsVa = null;
      var cbMap = null;
      var roles = ["disable", "unprepare", "prepare", "enable", "get_modes"];

      for (var ai = 0; ai < pFlow.adrpPtrs.length; ai++) {
        var ava = pFlow.adrpPtrs[ai];
        var aoff = Number(ava - baseLo);
        if (aoff < 0 || aoff + 40 > data.length) continue;
        var p0 = dv.getBigUint64(aoff, true);
        var p1 = dv.getBigUint64(aoff + 8, true);
        var p2 = dv.getBigUint64(aoff + 16, true);
        var p3 = dv.getBigUint64(aoff + 24, true);
        var p4 = dv.getBigUint64(aoff + 32, true);
        var arr = [p0, p1, p2, p3, p4];
        var vcnt = arr.filter(isCodePtr).length;
        if (vcnt >= 4 && isCodePtr(p2) && isCodePtr(p4)) {
          funcsVa = ava;
          cbMap = {};
          for (var ri = 0; ri < 5; ri++) {
            if (isCodePtr(arr[ri])) cbMap[roles[ri]] = arr[ri];
          }
          break;
        }
      }
      if (!cbMap || !cbMap.get_modes) continue;

      var gmFlow = AE.analyzeArm64FunctionFlow(data, baseLo, cbMap.get_modes, 0x1200);
      var timings = {};
      var modeCands = gmFlow.adrpPtrs.slice();
      for (var gc = 0; gc < gmFlow.calls.length; gc++) {
        for (var ga = 0; ga < 4; ga++) {
          var av = gmFlow.calls[gc].args[ga];
          if (av !== null && av >= baseLo && av < endVa) modeCands.push(av);
        }
      }
      for (var mc = 0; mc < modeCands.length && !timings.width; mc++) {
        var mVa = modeCands[mc];
        var mOff = Number(mVa - baseLo);
        if (mOff < 0 || mOff + 0xa0 > data.length) continue;
        for (var dlt = 0x20; dlt < 0x80; dlt += 4) {
          if (mOff + dlt + 40 > data.length) break;
          var clk = dv.getUint32(mOff + dlt, true);
          var hd = dv.getUint32(mOff + dlt + 4, true);
          var hss = dv.getUint32(mOff + dlt + 8, true);
          var hse = dv.getUint32(mOff + dlt + 12, true);
          var htot = dv.getUint32(mOff + dlt + 16, true);
          var vd = dv.getUint32(mOff + dlt + 24, true);
          var vss = dv.getUint32(mOff + dlt + 28, true);
          var vse = dv.getUint32(mOff + dlt + 32, true);
          var vtot = dv.getUint32(mOff + dlt + 36, true);
          if (
            hd >= 120 && hd <= hss && hss <= hse && hse <= htot && htot <= 8192 &&
            vd >= 120 && vd <= vss && vss <= vse && vse <= vtot && vtot <= 8192 &&
            clk >= 5000 && clk <= 2000000
          ) {
            var modeLoc = "drm_display_mode@" + toHex(mVa + BigInt(dlt));
            timings.pixel_clock_khz = { value: clk, location: modeLoc, sourceAddress: mVa + BigInt(dlt), status: "CONFIRMED" };
            timings.width = { value: hd, location: modeLoc, sourceAddress: mVa + BigInt(dlt), status: "CONFIRMED" };
            timings.hfp = { value: hss - hd, location: modeLoc, sourceAddress: mVa + BigInt(dlt), status: "CONFIRMED" };
            timings.hsa = { value: hse - hss, location: modeLoc, sourceAddress: mVa + BigInt(dlt), status: "CONFIRMED" };
            timings.hbp = { value: htot - hse, location: modeLoc, sourceAddress: mVa + BigInt(dlt), status: "CONFIRMED" };
            timings.height = { value: vd, location: modeLoc, sourceAddress: mVa + BigInt(dlt), status: "CONFIRMED" };
            timings.vfp = { value: vss - vd, location: modeLoc, sourceAddress: mVa + BigInt(dlt), status: "CONFIRMED" };
            timings.vsa = { value: vse - vss, location: modeLoc, sourceAddress: mVa + BigInt(dlt), status: "CONFIRMED" };
            timings.vbp = { value: vtot - vse, location: modeLoc, sourceAddress: mVa + BigInt(dlt), status: "CONFIRMED" };
            timings.fps = { value: Math.max(1, Math.round((clk * 1000) / Math.max(1, htot * vtot))), location: modeLoc, sourceAddress: mVa + BigInt(dlt), status: "CONFIRMED" };
            break;
          }
        }
      }
      if (!timings.width) continue;

      seen.add(structVa);
      var functions = {
        probe: { role: "probe", slotIndex: null, address: probeVa, mode: "ARM64", size: pFlow.size, status: "CONFIRMED" },
        get_modes: { role: "get_modes", slotIndex: 4, address: cbMap.get_modes, mode: "ARM64", size: gmFlow.size, status: "CONFIRMED" }
      };
      if (remVa) functions.remove = { role: "remove", slotIndex: null, address: remVa, mode: "ARM64", size: 0, status: "CONFIRMED" };

      function extractArm64Seq(fnVa) {
        var flow = AE.analyzeArm64FunctionFlow(data, baseLo, fnVa, 0x8000);
        var tgtCounts = new Map();
        for (var i = 0; i < flow.calls.length; i++) {
          var c = flow.calls[i];
          var bva = c.args[1];
          var dlen = c.args[2];
          if (c.target && bva !== null && dlen !== null && dlen >= 1n && dlen <= 255n) {
            var boff = Number(bva - baseLo);
            var nlen = Number(dlen);
            if (boff >= 0 && boff + nlen <= data.length) {
              var sTxt = asciiAt(data, boff, 128);
              if (sTxt && (sTxt.indexOf("%") !== -1 || sTxt.indexOf(" ") !== -1)) continue;
              if (nlen >= 4) {
                var allLower = true;
                for (var u = 0; u < nlen; u++) {
                  var ch = data[boff + u];
                  if (!((ch >= 97 && ch <= 122) || ch === 45 || ch === 95)) { allLower = false; break; }
                }
                if (allLower) continue;
              }
              var tKey = c.target.toString();
              tgtCounts.set(tKey, (tgtCounts.get(tKey) || 0) + 1);
            }
          }
        }
        var dcsTargets = new Set();
        var bestT = null;
        var bestCnt = 0;
        tgtCounts.forEach(function (cnt, key) {
          if (cnt >= 2) dcsTargets.add(key);
          if (cnt > bestCnt) { bestCnt = cnt; bestT = key; }
        });
        if (dcsTargets.size === 0 && bestT) dcsTargets.add(bestT);

        var ops = [];
        for (var k = 0; k < flow.calls.length; k++) {
          var cl = flow.calls[k];
          if (cl.target && dcsTargets.has(cl.target.toString())) {
            var bva2 = cl.args[1];
            var dlen2 = cl.args[2];
            if (bva2 !== null && dlen2 !== null && dlen2 >= 1n && dlen2 <= 255n) {
              var off2 = Number(bva2 - baseLo);
              var n2 = Number(dlen2);
              if (off2 >= 0 && off2 + n2 <= data.length) {
                var pBytes = [];
                for (var pb = 1; pb < n2; pb++) pBytes.push(data[off2 + pb]);
                ops.push({ opType: "DCS_WRITE", cmd: data[off2], params: pBytes, delayValue: null, pinOrRail: null, pinLevel: null, sourceAddress: cl.address, status: "CONFIRMED", rawEncoding: "buf@" + toHex(bva2) });
              }
            }
          } else if (cl.args[0] !== null && cl.args[1] !== null && cl.args[0] >= 10n && cl.args[0] <= 500000n && cl.args[1] >= cl.args[0] && cl.args[1] <= cl.args[0] + 5000n) {
            var us = Number(cl.args[0]);
            ops.push({ opType: us < 1000 ? "DELAY_US" : "DELAY_MS", cmd: null, params: [], delayValue: us < 1000 ? us : Math.max(1, Math.floor(us / 1000)), pinOrRail: null, pinLevel: null, sourceAddress: cl.address, status: "INFERRED", rawEncoding: "usleep_range" });
          } else if (cl.args[0] !== null && cl.args[1] === null && cl.args[0] >= 1n && cl.args[0] <= 500n) {
            ops.push({ opType: "DELAY_MS", cmd: null, params: [], delayValue: Number(cl.args[0]), pinOrRail: null, pinLevel: null, sourceAddress: cl.address, status: "INFERRED", rawEncoding: "msleep" });
          }
        }
        return { ops: ops, flow: flow };
      }

      var initOps = [];
      var suspOps = [];
      if (cbMap.prepare) {
        var pRes = extractArm64Seq(cbMap.prepare);
        initOps = pRes.ops;
        functions.prepare = { role: "prepare", slotIndex: 2, address: cbMap.prepare, mode: "ARM64", size: pRes.flow.size, status: "CONFIRMED" };
      }
      if (cbMap.unprepare) {
        var uRes = extractArm64Seq(cbMap.unprepare);
        suspOps = uRes.ops;
        functions.unprepare = { role: "unprepare", slotIndex: 3, address: cbMap.unprepare, mode: "ARM64", size: uRes.flow.size, status: "CONFIRMED" };
      }

      drivers.push({
        name: dname,
        framework: framework,
        interfaceType: "MIPI_DSI",
        structAddress: structVa,
        xrefAddress: ofVa,
        utilSlotMap: {},
        functions: functions,
        timings: timings,
        dsiConfig: { lanes: { value: 4, location: "drm_default", sourceAddress: probeVa, status: "INFERRED" } },
        esdItems: [],
        initSequence: initOps,
        suspendSequence: suspOps,
        resetSequence: [],
        idDetection: null,
        discoveryMethod: "arm64_mipi_dsi_driver_scan",
        compatible: compat,
        platformDependencies: ["reset"]
      });
    }
    return drivers;
  }

  function rankDrivers(drivers, payload) {
    if (!drivers.length) return null;
    var cmdline = String((payload.metadata && payload.metadata.cmdline) || "");
    var cmdLcm = "";
    var toks = cmdline.split(/\s+/);
    for (var i = 0; i < toks.length; i++) {
      if (toks[i].indexOf("lcm=") === 0 || toks[i].indexOf("lcmname=") !== -1) {
        cmdLcm = toks[i].split("=")[1].replace(/['"]/g, "");
        break;
      }
    }
    var best = null;
    var bestScore = -1;
    for (var d = 0; d < drivers.length; d++) {
      var drv = drivers[d];
      drv.isActive = false;
      var sc = 0;
      if (cmdLcm && (drv.name.indexOf(cmdLcm) !== -1 || cmdLcm.indexOf(drv.name) !== -1)) sc += 50;
      if (drv.timings.width && drv.timings.height) sc += 15;
      var dcsCnt = drv.initSequence.filter(function (o) { return o.opType === "DCS_WRITE"; }).length;
      if (drv.initSequence.length) sc += Math.min(20, 5 + dcsCnt * 0.4);
      if (drv.idDetection && drv.idDetection.expectedIds.length) sc += 12;
      if (drv.esdItems.length) sc += 4;
      if (/virtual|dummy|default/i.test(drv.name)) sc -= 25;
      sc += Math.max(0, 3 - d * 0.25);
      drv.selectionScore = sc;
      if (sc > bestScore) { bestScore = sc; best = drv; }
    }
    if (best) best.isActive = true;
    return best ? best.name : null;
  }

  function renderMtkC(drv, isKernel) {
    var cSym = safeIdent(drv.name.replace(/_lcm_drv$/, ""), "panel");
    var t = drv.timings;
    var d = drv.dsiConfig;
    var val = function (obj, k, fb) { return (obj[k] && obj[k].value !== undefined) ? obj[k].value : fb; };
    var modeMap = { 0: "CMD_MODE", 1: "SYNC_PULSE_VDO_MODE", 2: "SYNC_EVENT_VDO_MODE", 3: "BURST_VDO_MODE" };
    var laneMap = { 1: "LCM_ONE_LANE", 2: "LCM_TWO_LANE", 3: "LCM_THREE_LANE", 4: "LCM_FOUR_LANE" };
    var psMap = { 0: "LCM_PACKED_PS_16BIT_RGB565", 1: "LCM_LOOSELY_PS_18BIT_RGB666", 2: "LCM_PACKED_PS_24BIT_RGB888", 3: "LCM_PACKED_PS_18BIT_RGB666" };

    var lines = isKernel
      ? ["#include <linux/string.h>", "#include <linux/kernel.h>", "#include \"lcm_drv.h\"", ""]
      : ["#include \"lcm_drv.h\"", ""];

    lines.push("#define LCM_DSI_CMD_MODE " + (val(d, "mode", 1) === 0 ? 1 : 0));
    lines.push("#define FRAME_WIDTH (" + val(t, "width", 720) + ")");
    lines.push("#define FRAME_HEIGHT (" + val(t, "height", 1280) + ")");
    lines.push("#define REGFLAG_DELAY 0xFFFE");
    lines.push("#define REGFLAG_END_OF_TABLE 0xFFFD");
    if (drv.idDetection && drv.idDetection.expectedIds.length) {
      lines.push("#define LCM_ID_EXPECTED " + toHex(drv.idDetection.expectedIds[0]));
    }
    lines.push("");
    lines.push("static struct LCM_util_funcs lcm_util;");
    lines.push("#define SET_RESET_PIN(v) (lcm_util.set_reset_pin((v)))");
    lines.push("#define UDELAY(n) (lcm_util.udelay(n))");
    lines.push("#define MDELAY(n) (lcm_util.mdelay(n))");
    lines.push("#define dsi_set_cmdq_V2(cmd, count, ppara, force_update) lcm_util.dsi_set_cmdq_V2(cmd, count, ppara, force_update)");
    lines.push("#define dsi_set_cmdq(pdata, queue_size, force_update) lcm_util.dsi_set_cmdq(pdata, queue_size, force_update)");
    lines.push("#define read_reg_v2(cmd, buffer, buffer_size) lcm_util.dsi_dcs_read_lcm_reg_v2(cmd, buffer, buffer_size)");
    lines.push("");
    lines.push("struct LCM_setting_table {");
    lines.push("\tunsigned int cmd;");
    lines.push("\tunsigned char count;");
    lines.push("\tunsigned char para_list[64];");
    lines.push("};");
    lines.push("");

    function formatTable(varName, seq) {
      lines.push("static struct LCM_setting_table " + varName + "[] = {");
      for (var i = 0; i < seq.length; i++) {
        var op = seq[i];
        if (op.opType === "DCS_WRITE" && op.cmd !== null) {
          var phex = op.params.map(function (b) { return "0x" + b.toString(16).toUpperCase().padStart(2, "0"); }).join(", ");
          lines.push("\t{0x" + op.cmd.toString(16).toUpperCase().padStart(2, "0") + ", " + op.params.length + ", {" + phex + "}},");
        } else if (op.opType === "DELAY_MS" && op.delayValue !== null) {
          lines.push("\t{REGFLAG_DELAY, " + op.delayValue + ", {}},");
        }
      }
      lines.push("\t{REGFLAG_END_OF_TABLE, 0x00, {}},");
      lines.push("};");
      lines.push("");
    }

    formatTable("lcm_initialization_setting", drv.initSequence);
    if (drv.suspendSequence.length) formatTable("lcm_deep_sleep_mode_in_setting", drv.suspendSequence);

    lines.push("static void push_table(struct LCM_setting_table *table, unsigned int count, unsigned char force_update)");
    lines.push("{");
    lines.push("\tunsigned int i;");
    lines.push("\tfor (i = 0; i < count; i++) {");
    lines.push("\t\tunsigned int cmd = table[i].cmd;");
    lines.push("\t\tswitch (cmd) {");
    lines.push("\t\tcase REGFLAG_DELAY:");
    lines.push("\t\t\tMDELAY(table[i].count);");
    lines.push("\t\t\tbreak;");
    lines.push("\t\tcase REGFLAG_END_OF_TABLE:");
    lines.push("\t\t\treturn;");
    lines.push("\t\tdefault:");
    lines.push("\t\t\tdsi_set_cmdq_V2(cmd, table[i].count, table[i].para_list, force_update);");
    lines.push("\t\t\tbreak;");
    lines.push("\t\t}");
    lines.push("\t}");
    lines.push("}");
    lines.push("");
    lines.push("static void lcm_set_util_funcs(const struct LCM_util_funcs *util)");
    lines.push("{");
    lines.push("\tmemcpy(&lcm_util, util, sizeof(struct LCM_util_funcs));");
    lines.push("}");
    lines.push("");
    lines.push("static void lcm_get_params(struct LCM_PARAMS *params)");
    lines.push("{");
    lines.push("\tmemset(params, 0, sizeof(struct LCM_PARAMS));");
    lines.push("\tparams->type = LCM_TYPE_DSI;");
    lines.push("\tparams->width = FRAME_WIDTH;");
    lines.push("\tparams->height = FRAME_HEIGHT;");
    lines.push("\tparams->dsi.mode = " + (modeMap[val(d, "mode", 1)] || "SYNC_PULSE_VDO_MODE") + ";");
    lines.push("\tparams->dsi.LANE_NUM = " + (laneMap[val(d, "lanes", 4)] || "LCM_FOUR_LANE") + ";");
    lines.push("\tparams->dsi.PS = " + (psMap[val(d, "ps", 2)] || "LCM_PACKED_PS_24BIT_RGB888") + ";");
    lines.push("\tparams->dsi.vertical_sync_active = " + val(t, "vsa", 4) + ";");
    lines.push("\tparams->dsi.vertical_backporch = " + val(t, "vbp", 12) + ";");
    lines.push("\tparams->dsi.vertical_frontporch = " + val(t, "vfp", 16) + ";");
    lines.push("\tparams->dsi.vertical_active_line = FRAME_HEIGHT;");
    lines.push("\tparams->dsi.horizontal_sync_active = " + val(t, "hsa", 10) + ";");
    lines.push("\tparams->dsi.horizontal_backporch = " + val(t, "hbp", 20) + ";");
    lines.push("\tparams->dsi.horizontal_frontporch = " + val(t, "hfp", 20) + ";");
    lines.push("\tparams->dsi.horizontal_active_pixel = FRAME_WIDTH;");
    if (t.pll_clock) lines.push("\tparams->dsi.PLL_CLOCK = " + t.pll_clock.value + ";");
    if (t.data_rate) lines.push("\tparams->dsi.data_rate = " + t.data_rate.value + ";");
    if (d.dsc_enable) lines.push("\tparams->dsi.dsc_enable = " + d.dsc_enable.value + ";");
    if (drv.esdItems.length) {
      lines.push("\tparams->dsi.esd_check_enable = 1;");
      lines.push("\tparams->dsi.customization_esd_check_enable = 1;");
      for (var ei = 0; ei < drv.esdItems.length; ei++) {
        var esd = drv.esdItems[ei];
        lines.push("\tparams->dsi.lcm_esd_check_table[" + ei + "].cmd = 0x" + esd.cmd.toString(16).toUpperCase() + ";");
        lines.push("\tparams->dsi.lcm_esd_check_table[" + ei + "].count = " + esd.count + ";");
        for (var ep = 0; ep < esd.expectedParams.length; ep++) {
          lines.push("\tparams->dsi.lcm_esd_check_table[" + ei + "].para_list[" + ep + "] = 0x" + esd.expectedParams[ep].toString(16).toUpperCase() + ";");
        }
      }
    }
    lines.push("}");
    lines.push("");
    lines.push("static void lcm_init(void)");
    lines.push("{");
    if (drv.resetSequence.length) {
      for (var ri = 0; ri < drv.resetSequence.length; ri++) {
        var rop = drv.resetSequence[ri];
        if (rop.opType === "RESET_PIN") lines.push("\tSET_RESET_PIN(" + rop.pinLevel + ");");
        else if (rop.opType === "DELAY_MS") lines.push("\tMDELAY(" + rop.delayValue + ");");
      }
    } else {
      lines.push("\tSET_RESET_PIN(1);");
      lines.push("\tMDELAY(10);");
      lines.push("\tSET_RESET_PIN(0);");
      lines.push("\tMDELAY(10);");
      lines.push("\tSET_RESET_PIN(1);");
      lines.push("\tMDELAY(120);");
    }
    lines.push("\tpush_table(lcm_initialization_setting, sizeof(lcm_initialization_setting) / sizeof(struct LCM_setting_table), 1);");
    lines.push("}");
    lines.push("");
    lines.push("static void lcm_suspend(void)");
    lines.push("{");
    if (drv.suspendSequence.length) {
      lines.push("\tpush_table(lcm_deep_sleep_mode_in_setting, sizeof(lcm_deep_sleep_mode_in_setting) / sizeof(struct LCM_setting_table), 1);");
    } else {
      lines.push("\tSET_RESET_PIN(0);");
      lines.push("\tMDELAY(10);");
    }
    lines.push("}");
    lines.push("");
    lines.push("static void lcm_resume(void)");
    lines.push("{");
    lines.push("\tlcm_init();");
    lines.push("}");
    lines.push("");
    lines.push("static unsigned int lcm_compare_id(void)");
    lines.push("{");
    lines.push("\tunsigned char buffer[4] = {0};");
    lines.push("\tunsigned int data_array[2];");
    lines.push("\tSET_RESET_PIN(1);");
    lines.push("\tMDELAY(10);");
    lines.push("\tSET_RESET_PIN(0);");
    lines.push("\tMDELAY(10);");
    lines.push("\tSET_RESET_PIN(1);");
    lines.push("\tMDELAY(50);");
    lines.push("\tdata_array[0] = 0x00023700;");
    lines.push("\tdsi_set_cmdq(data_array, 1, 1);");
    var rCmd = (drv.idDetection && drv.idDetection.readCommand !== null) ? drv.idDetection.readCommand : 0x04;
    lines.push("\tread_reg_v2(0x" + rCmd.toString(16).toUpperCase().padStart(2, "0") + ", buffer, 2);");
    if (drv.idDetection && drv.idDetection.expectedIds.length) {
      lines.push("\treturn (((buffer[0] << 8) | buffer[1]) == LCM_ID_EXPECTED) ? 1 : 0;");
    } else {
      lines.push("\treturn 1;");
    }
    lines.push("}");
    lines.push("");
    lines.push("struct LCM_DRIVER " + cSym + "_lcm_drv = {");
    lines.push("\t.name = \"" + drv.name + "\",");
    lines.push("\t.set_util_funcs = lcm_set_util_funcs,");
    lines.push("\t.get_params = lcm_get_params,");
    lines.push("\t.init = lcm_init,");
    lines.push("\t.suspend = lcm_suspend,");
    lines.push("\t.resume = lcm_resume,");
    lines.push("\t.compare_id = lcm_compare_id,");
    lines.push("};");
    lines.push("");
    return lines.join("\n");
  }

  function renderDrmPanelC(drv) {
    var cSym = safeIdent(drv.name.replace(/_lcm_drv$/, ""), "panel");
    var t = drv.timings;
    var val = function (k, fb) { return (t[k] && t[k].value !== undefined) ? t[k].value : fb; };
    var w = val("width", 1080);
    var h = val("height", 2400);
    var hfp = val("hfp", 40);
    var hsa = val("hsa", 10);
    var hbp = val("hbp", 40);
    var vfp = val("vfp", 20);
    var vsa = val("vsa", 4);
    var vbp = val("vbp", 12);
    var clk = val("pixel_clock_khz", Math.floor(((w + hfp + hsa + hbp) * (h + vfp + vsa + vbp) * 60) / 1000));
    var lanes = (drv.dsiConfig.lanes && drv.dsiConfig.lanes.value) ? drv.dsiConfig.lanes.value : 4;
    var compat = drv.compatible || ("vendor," + cSym.replace(/_/g, "-"));

    var lines = [
      "#include <linux/delay.h>",
      "#include <linux/gpio/consumer.h>",
      "#include <linux/module.h>",
      "#include <linux/of.h>",
      "#include <drm/drm_mipi_dsi.h>",
      "#include <drm/drm_modes.h>",
      "#include <drm/drm_panel.h>",
      "",
      "struct " + cSym + "_panel {",
      "\tstruct drm_panel panel;",
      "\tstruct mipi_dsi_device *dsi;",
      "\tstruct gpio_desc *reset_gpio;",
      "};",
      "",
      "static inline struct " + cSym + "_panel *to_panel_ctx(struct drm_panel *p)",
      "{",
      "\treturn container_of(p, struct " + cSym + "_panel, panel);",
      "}",
      "",
      "static int " + cSym + "_prepare(struct drm_panel *panel)",
      "{",
      "\tstruct " + cSym + "_panel *ctx = to_panel_ctx(panel);",
      "\tstruct mipi_dsi_device *dsi = ctx->dsi;",
      "\tgpiod_set_value_cansleep(ctx->reset_gpio, 1);",
      "\tmsleep(10);",
      "\tgpiod_set_value_cansleep(ctx->reset_gpio, 0);",
      "\tmsleep(10);",
      "\tgpiod_set_value_cansleep(ctx->reset_gpio, 1);",
      "\tmsleep(120);"
    ];
    for (var i = 0; i < drv.initSequence.length; i++) {
      var op = drv.initSequence[i];
      if (op.opType === "DCS_WRITE" && op.cmd !== null) {
        var bytes = [op.cmd].concat(op.params).map(function (b) { return "0x" + b.toString(16).toUpperCase().padStart(2, "0"); }).join(", ");
        lines.push("\tmipi_dsi_dcs_write_buffer(dsi, (const u8[]){" + bytes + "}, " + (1 + op.params.length) + ");");
      } else if (op.opType === "DELAY_MS" && op.delayValue !== null) {
        lines.push("\tmsleep(" + op.delayValue + ");");
      } else if (op.opType === "DELAY_US" && op.delayValue !== null) {
        lines.push("\tusleep_range(" + op.delayValue + ", " + (op.delayValue + 50) + ");");
      }
    }
    lines.push("\treturn 0;");
    lines.push("}");
    lines.push("");
    lines.push("static int " + cSym + "_unprepare(struct drm_panel *panel)");
    lines.push("{");
    lines.push("\tstruct " + cSym + "_panel *ctx = to_panel_ctx(panel);");
    lines.push("\tstruct mipi_dsi_device *dsi = ctx->dsi;");
    lines.push("\tmipi_dsi_dcs_set_display_off(dsi);");
    lines.push("\tmipi_dsi_dcs_enter_sleep_mode(dsi);");
    lines.push("\tmsleep(120);");
    lines.push("\treturn 0;");
    lines.push("}");
    lines.push("");
    lines.push("static const struct drm_display_mode " + cSym + "_default_mode = {");
    lines.push("\t.clock = " + clk + ",");
    lines.push("\t.hdisplay = " + w + ",");
    lines.push("\t.hsync_start = " + (w + hfp) + ",");
    lines.push("\t.hsync_end = " + (w + hfp + hsa) + ",");
    lines.push("\t.htotal = " + (w + hfp + hsa + hbp) + ",");
    lines.push("\t.vdisplay = " + h + ",");
    lines.push("\t.vsync_start = " + (h + vfp) + ",");
    lines.push("\t.vsync_end = " + (h + vfp + vsa) + ",");
    lines.push("\t.vtotal = " + (h + vfp + vsa + vbp) + ",");
    lines.push("};");
    lines.push("");
    lines.push("static int " + cSym + "_get_modes(struct drm_panel *panel, struct drm_connector *connector)");
    lines.push("{");
    lines.push("\tstruct drm_display_mode *mode = drm_mode_duplicate(connector->dev, &" + cSym + "_default_mode);");
    lines.push("\tif (!mode) return -ENOMEM;");
    lines.push("\tdrm_mode_set_name(mode);");
    lines.push("\tmode->type = DRM_MODE_TYPE_DRIVER | DRM_MODE_TYPE_PREFERRED;");
    lines.push("\tdrm_mode_probed_add(connector, mode);");
    lines.push("\treturn 1;");
    lines.push("}");
    lines.push("");
    lines.push("static const struct drm_panel_funcs " + cSym + "_panel_funcs = {");
    lines.push("\t.prepare = " + cSym + "_prepare,");
    lines.push("\t.unprepare = " + cSym + "_unprepare,");
    lines.push("\t.get_modes = " + cSym + "_get_modes,");
    lines.push("};");
    lines.push("");
    lines.push("static int " + cSym + "_probe(struct mipi_dsi_device *dsi)");
    lines.push("{");
    lines.push("\tstruct device *dev = &dsi->dev;");
    lines.push("\tstruct " + cSym + "_panel *ctx = devm_kzalloc(dev, sizeof(*ctx), GFP_KERNEL);");
    lines.push("\tif (!ctx) return -ENOMEM;");
    lines.push("\tctx->dsi = dsi;");
    lines.push("\tdsi->lanes = " + lanes + ";");
    lines.push("\tdsi->format = MIPI_DSI_FMT_RGB888;");
    lines.push("\tdsi->mode_flags = MIPI_DSI_MODE_VIDEO | MIPI_DSI_MODE_VIDEO_SYNC_PULSE;");
    lines.push("\tctx->reset_gpio = devm_gpiod_get_optional(dev, \"reset\", GPIOD_OUT_HIGH);");
    lines.push("\tdrm_panel_init(&ctx->panel, dev, &" + cSym + "_panel_funcs, DRM_MODE_CONNECTOR_DSI);");
    lines.push("\tdrm_panel_add(&ctx->panel);");
    lines.push("\tmipi_dsi_set_drvdata(dsi, ctx);");
    lines.push("\treturn mipi_dsi_attach(dsi);");
    lines.push("}");
    lines.push("");
    lines.push("static const struct of_device_id " + cSym + "_of_match[] = {");
    lines.push("\t{ .compatible = \"" + compat + "\" },");
    lines.push("\t{ }");
    lines.push("};");
    lines.push("MODULE_DEVICE_TABLE(of, " + cSym + "_of_match);");
    lines.push("");
    lines.push("static struct mipi_dsi_driver " + cSym + "_driver = {");
    lines.push("\t.probe = " + cSym + "_probe,");
    lines.push("\t.driver = { .name = \"" + drv.name + "\", .of_match_table = " + cSym + "_of_match },");
    lines.push("};");
    lines.push("module_mipi_dsi_driver(" + cSym + "_driver);");
    lines.push("");
    return lines.join("\n");
  }

  function renderDtsi(drv) {
    var cSym = safeIdent(drv.name.replace(/_lcm_drv$/, ""), "panel");
    var t = drv.timings;
    var v = function (k, fb) { return (t[k] && t[k].value !== undefined) ? t[k].value : fb; };
    var w = v("width", 1080);
    var h = v("height", 2400);
    var hfp = v("hfp", 40);
    var hsa = v("hsa", 10);
    var hbp = v("hbp", 40);
    var vfp = v("vfp", 20);
    var vsa = v("vsa", 4);
    var vbp = v("vbp", 12);
    var clk = v("pixel_clock_khz", 60000) * 1000;
    var compat = drv.compatible || ("vendor," + cSym.replace(/_/g, "-"));
    var lanes = (drv.dsiConfig.lanes && drv.dsiConfig.lanes.value) ? drv.dsiConfig.lanes.value : 4;
    return [
      "&dsi0 {",
      "\tstatus = \"okay\";",
      "",
      "\tpanel_" + cSym + ": panel@0 {",
      "\t\tcompatible = \"" + compat + "\";",
      "\t\treg = <0>;",
      "\t\treset-gpios = <&pio 45 0>;",
      "\t\tdsi-lanes = <" + lanes + ">;",
      "",
      "\t\tdisplay-timings {",
      "\t\t\tnative-mode = <&timing_0>;",
      "\t\t\ttiming_0: timing0 {",
      "\t\t\t\tclock-frequency = <" + clk + ">;",
      "\t\t\t\thactive = <" + w + ">;",
      "\t\t\t\tvactive = <" + h + ">;",
      "\t\t\t\thfront-porch = <" + hfp + ">;",
      "\t\t\t\thsync-len = <" + hsa + ">;",
      "\t\t\t\thback-porch = <" + hbp + ">;",
      "\t\t\t\tvfront-porch = <" + vfp + ">;",
      "\t\t\t\tvsync-len = <" + vsa + ">;",
      "\t\t\t\tvback-porch = <" + vbp + ">;",
      "\t\t\t};",
      "\t\t};",
      "\t};",
      "};",
      ""
    ].join("\n");
  }

  function renderGenericC(drv) {
    var cSym = safeIdent(drv.name.replace(/_lcm_drv$/, ""), "panel");
    var t = drv.timings;
    var v = function (k, fb) { return (t[k] && t[k].value !== undefined) ? t[k].value : fb; };
    var lines = [
      "#include <stdint.h>",
      "#include <stddef.h>",
      "",
      "struct panel_dcs_cmd {",
      "\tuint8_t cmd;",
      "\tuint8_t len;",
      "\tconst uint8_t *params;",
      "\tuint16_t delay_ms;",
      "};",
      "",
      "struct panel_timing_config {",
      "\tuint32_t width, height;",
      "\tuint32_t hfp, hsa, hbp;",
      "\tuint32_t vfp, vsa, vbp;",
      "\tuint32_t dsi_lanes;",
      "};",
      "",
      "static const struct panel_timing_config " + cSym + "_timing = {",
      "\t.width = " + v("width", 0) + ", .height = " + v("height", 0) + ",",
      "\t.hfp = " + v("hfp", 0) + ", .hsa = " + v("hsa", 0) + ", .hbp = " + v("hbp", 0) + ",",
      "\t.vfp = " + v("vfp", 0) + ", .vsa = " + v("vsa", 0) + ", .vbp = " + v("vbp", 0) + ",",
      "\t.dsi_lanes = " + ((drv.dsiConfig.lanes && drv.dsiConfig.lanes.value) || 4) + ",",
      "};",
      ""
    ];
    for (var i = 0; i < drv.initSequence.length; i++) {
      var op = drv.initSequence[i];
      if (op.opType === "DCS_WRITE" && op.cmd !== null && op.params.length) {
        var ph = op.params.map(function (b) { return "0x" + b.toString(16).toUpperCase().padStart(2, "0"); }).join(", ");
        lines.push("static const uint8_t " + cSym + "_p_" + i + "[] = {" + ph + "};");
      }
    }
    lines.push("static const struct panel_dcs_cmd " + cSym + "_init_seq[] = {");
    for (var k = 0; k < drv.initSequence.length; k++) {
      var op2 = drv.initSequence[k];
      if (op2.opType === "DCS_WRITE" && op2.cmd !== null) {
        if (op2.params.length) lines.push("\t{ 0x" + op2.cmd.toString(16).toUpperCase().padStart(2, "0") + ", " + op2.params.length + ", " + cSym + "_p_" + k + ", 0 },");
        else lines.push("\t{ 0x" + op2.cmd.toString(16).toUpperCase().padStart(2, "0") + ", 0, NULL, 0 },");
      } else if (op2.opType === "DELAY_MS" && op2.delayValue !== null) {
        lines.push("\t{ 0x00, 0, NULL, " + op2.delayValue + " },");
      }
    }
    lines.push("};");
    lines.push("");
    return lines.join("\n");
  }

  function vaToFileOff(va, baseAddr, codeLen, codeFileOff) {
    if (va === null || va === undefined || !codeLen || !baseAddr) return "N/A";
    var rel = typeof va === "bigint" ? Number(va - BigInt(baseAddr)) : (va - baseAddr);
    if (rel >= 0 && rel < codeLen) {
      if (codeFileOff > 0) return "0x" + rel.toString(16).toUpperCase() + " (input +0x" + (codeFileOff + rel).toString(16).toUpperCase() + ")";
      return "0x" + rel.toString(16).toUpperCase();
    }
    return "N/A";
  }

  function buildAddressesReportTxt(res) {
    var base = res.architecture.baseAddress;
    var clen = res.payload.primaryCode ? res.payload.primaryCode.length : 0;
    var foff = res.payload.codeFileOffset || 0;
    var sep = "================================================================================================";
    var lines = [
      sep,
      "UNIVERSAL LCM REVERSE ENGINEERING - COMPLETE ADDRESSES & DRIVER REPORT",
      sep,
      "Input File          : " + res.inputName,
      "Raw File Size       : " + res.rawSize + " bytes (0x" + res.rawSize.toString(16).toUpperCase() + ")",
      "Detected Format     : " + res.payload.formatType + " (" + res.payload.evidence + ")",
      "Architecture        : " + res.architecture.architecture,
      "Framework           : " + res.framework,
      "Load Base Address   : " + toHex(base) + " (" + res.architecture.baseMethod + ", " + res.architecture.baseStatus + ")",
      "Drivers Discovered  : " + res.drivers.length,
      "Active Driver       : " + (res.activeDriverName || "NONE")
    ];

    for (var i = 0; i < res.drivers.length; i++) {
      var drv = res.drivers[i];
      lines.push("");
      lines.push(sep);
      lines.push("DRIVER #" + (i + 1) + ": " + drv.name + (drv.isActive ? " [ACTIVE PANEL]" : ""));
      lines.push(sep);
      lines.push("  Display Interface    : " + drv.interfaceType);
      lines.push("  Struct VA            : " + toHex(drv.structAddress) + "  (file off: " + vaToFileOff(drv.structAddress, base, clen, foff) + ")");
      lines.push("  Xref / Match VA      : " + toHex(drv.xrefAddress) + "  (file off: " + vaToFileOff(drv.xrefAddress, base, clen, foff) + ")");
      lines.push("  Discovery Method     : " + drv.discoveryMethod);
      if (drv.compatible) lines.push("  DT Compatible        : " + drv.compatible);

      if (Object.keys(drv.utilSlotMap).length) {
        lines.push("");
        lines.push("  [LCM_UTIL_FUNCS Slot Offset Table]");
        Object.keys(drv.utilSlotMap).sort(function (a, b) { return Number(a) - Number(b); }).forEach(function (k) {
          lines.push("    +0x" + Number(k).toString(16).toUpperCase().padStart(2, "0") + " : " + drv.utilSlotMap[k]);
        });
      }

      lines.push("");
      lines.push("  [Callback Function Addresses]");
      lines.push("    Slot  Role                  Virtual Addr          File Offset                 Mode   Size");
      Object.values(drv.functions).sort(function (a, b) { return (a.slotIndex !== null ? a.slotIndex : 999) - (b.slotIndex !== null ? b.slotIndex : 999); }).forEach(function (fn) {
        var sTxt = fn.slotIndex !== null ? ("[" + String(fn.slotIndex).padStart(2, "0") + "]") : " -- ";
        var vaStr = toHex(fn.address).padEnd(20, " ");
        var offStr = vaToFileOff(fn.address, base, clen, foff).padEnd(26, " ");
        lines.push("    " + sTxt + "  " + fn.role.padEnd(20, " ") + "  " + vaStr + "  " + offStr + "  " + fn.mode.padEnd(5, " ") + "  0x" + fn.size.toString(16));
      });

      lines.push("");
      lines.push("  [Hardware Timings & DSI Parameters]");
      Object.keys(drv.timings).concat(Object.keys(drv.dsiConfig)).forEach(function (pk) {
        var ev = drv.timings[pk] || drv.dsiConfig[pk];
        lines.push("    " + pk.padEnd(24, " ") + " = " + String(ev.value).padEnd(18, " ") + " (" + ev.location + " @ " + toHex(ev.sourceAddress) + ")");
      });

      if (drv.idDetection) {
        lines.push("");
        lines.push("  [Panel ID Detection]");
        lines.push("    compare_id Func VA : " + toHex(drv.idDetection.sourceAddress));
        lines.push("    DCS Read Register  : " + (drv.idDetection.readCommand !== null ? "0x" + drv.idDetection.readCommand.toString(16).toUpperCase() : "N/A"));
        lines.push("    Expected IDs       : [" + drv.idDetection.expectedIds.map(toHex).join(", ") + "]");
      }

      if (drv.esdItems.length) {
        lines.push("");
        lines.push("  [ESD Check Registers]");
        drv.esdItems.forEach(function (e) {
          lines.push("    cmd=0x" + e.cmd.toString(16).toUpperCase() + ", count=" + e.count + ", expected=[" + e.expectedParams.map(toHex).join(", ") + "]");
        });
      }

      lines.push("");
      lines.push("  [Initialization Sequence (" + drv.initSequence.length + " ops)]");
      drv.initSequence.forEach(function (op, idx) {
        if (op.opType === "DCS_WRITE" && op.cmd !== null) {
          var phex = op.params.map(function (b) { return b.toString(16).toUpperCase().padStart(2, "0"); }).join(" ");
          lines.push("    " + String(idx + 1).padStart(3, "0") + ". DCS_WRITE  cmd=0x" + op.cmd.toString(16).toUpperCase().padStart(2, "0") + " len=" + op.params.length + " [" + phex + "] @ " + toHex(op.sourceAddress));
        } else if (op.opType === "DELAY_MS" || op.opType === "DELAY_US") {
          lines.push("    " + String(idx + 1).padStart(3, "0") + ". " + op.opType + "   " + op.delayValue + " @ " + toHex(op.sourceAddress));
        } else if (op.opType === "RESET_PIN" || op.opType === "GPIO_OUT") {
          lines.push("    " + String(idx + 1).padStart(3, "0") + ". " + op.opType + "  " + (op.pinOrRail || "PIN") + "=" + op.pinLevel + " @ " + toHex(op.sourceAddress));
        } else {
          lines.push("    " + String(idx + 1).padStart(3, "0") + ". " + op.opType + " " + op.rawEncoding + " @ " + toHex(op.sourceAddress));
        }
      });
    }
    lines.push("");
    return lines.join("\n");
  }

  function buildAddressesReportMd(res) {
    var base = res.architecture.baseAddress;
    var clen = res.payload.primaryCode ? res.payload.primaryCode.length : 0;
    var foff = res.payload.codeFileOffset || 0;
    var lines = [
      "# LCM Reverse Engineering Report: " + res.inputName,
      "",
      "- Format: `" + res.payload.formatType + "`",
      "- Architecture: `" + res.architecture.architecture + "`",
      "- Framework: `" + res.framework + "`",
      "- Load Base Address: `" + toHex(base) + "` (" + res.architecture.baseMethod + ")",
      "- Active Driver: `" + (res.activeDriverName || "NONE") + "`",
      "",
      "| Driver | Struct VA | File Offset | init VA | get_params VA | compare_id VA |",
      "|---|---|---|---|---|---|"
    ];
    res.drivers.forEach(function (drv) {
      var initFn = drv.functions.init || drv.functions.prepare;
      var gpFn = drv.functions.get_params || drv.functions.get_modes;
      var cidFn = drv.functions.compare_id;
      lines.push("| `" + drv.name + "` | `" + toHex(drv.structAddress) + "` | `" + vaToFileOff(drv.structAddress, base, clen, foff) + "` | `" + (initFn ? toHex(initFn.address) : "N/A") + "` | `" + (gpFn ? toHex(gpFn.address) : "N/A") + "` | `" + (cidFn ? toHex(cidFn.address) : "N/A") + "` |");
    });
    lines.push("");
    return lines.join("\n");
  }

  function renderInitTableTxt(drv) {
    var lines = [
      "DRIVER: " + drv.name,
      "STRUCT VA: " + toHex(drv.structAddress),
      "INTERFACE: " + drv.interfaceType,
      "",
      "static struct LCM_setting_table lcm_initialization_setting[] = {"
    ];
    drv.initSequence.forEach(function (op) {
      if (op.opType === "DCS_WRITE" && op.cmd !== null) {
        var ph = op.params.map(function (b) { return "0x" + b.toString(16).toUpperCase().padStart(2, "0"); }).join(", ");
        lines.push("\t{0x" + op.cmd.toString(16).toUpperCase().padStart(2, "0") + ", " + op.params.length + ", {" + ph + "}},");
      } else if (op.opType === "DELAY_MS" && op.delayValue !== null) {
        lines.push("\t{REGFLAG_DELAY, " + op.delayValue + ", {}},");
      }
    });
    lines.push("\t{REGFLAG_END_OF_TABLE, 0x00, {}},");
    lines.push("};");
    lines.push("");
    return lines.join("\n");
  }

  async function analyzeBinaryAndBuildOut(fileName, uint8Array) {
    var payload = await unpackInputBuffer(fileName, uint8Array);
    var arch = detectArchitectureAndBase(payload);
    var fw = detectFramework(payload, arch, payload.primaryCode);
    var drivers = [];
    if (arch.architecture === "ARM64") {
      drivers = discoverArm64Drivers(payload, arch, fw);
    } else if (payload.primaryCode.length > 0 && arch.architecture !== "NON_EXECUTABLE") {
      drivers = discoverArm32Drivers(payload, arch, fw);
    }
    var activeName = rankDrivers(drivers, payload);

    var res = {
      inputName: fileName,
      rawSize: uint8Array.length,
      payload: payload,
      architecture: arch,
      framework: fw,
      drivers: drivers,
      activeDriverName: activeName
    };

    var stem = safeIdent(fileName.replace(/\.[^.]+$/, ""), "firmware");
    var prefix = "out/" + stem + "/";
    var outFiles = [];

    outFiles.push({ path: prefix + "ADDRESSES_REPORT.txt", content: buildAddressesReportTxt(res) });
    outFiles.push({ path: prefix + "ADDRESSES_REPORT.md", content: buildAddressesReportMd(res) });
    outFiles.push({
      path: prefix + "ACTIVE_DRIVER.txt",
      content: "Active Panel Candidate: " + (activeName || "NONE") + "\nDrivers Discovered: " + drivers.length + "\nLoad Base Address: " + toHex(arch.baseAddress) + "\n"
    });
    outFiles.push({
      path: prefix + "unpacked/payload_info.txt",
      content: [
        "Input Name     : " + fileName,
        "Format         : " + payload.formatType + " (" + payload.evidence + ")",
        "Raw Size       : " + uint8Array.length,
        "Unpacked Size  : " + payload.primaryCode.length,
        "Architecture   : " + arch.architecture,
        "Framework      : " + fw,
        "Load Base VA   : " + toHex(arch.baseAddress),
        "Embedded DTBs  : " + payload.dtbs.length
      ].join("\n") + "\n"
    });
    if (payload.primaryCode.length > 0) {
      outFiles.push({ path: prefix + "unpacked/primary_payload.bin", content: payload.primaryCode });
    }
    for (var di = 0; di < payload.dtbs.length; di++) {
      outFiles.push({
        path: prefix + "unpacked/dtb_" + di + "_" + safeIdent(payload.dtbs[di].label, "fdt") + ".dtb",
        content: payload.dtbs[di].bytes
      });
    }

    for (var i = 0; i < drivers.length; i++) {
      var drv = drivers[i];
      var dName = safeIdent(drv.name, "panel_" + i);
      var cSym = safeIdent(drv.name.replace(/_lcm_drv$/, ""), "panel");
      var dPrefix = prefix + "drivers/" + dName + "/";
      var lkC = renderMtkC(drv, false);
      var kernC = renderMtkC(drv, true);
      var drmC = renderDrmPanelC(drv);
      var dtsi = renderDtsi(drv);
      var genC = renderGenericC(drv);
      var initTbl = renderInitTableTxt(drv);

      drv.generated = { lkC: lkC, kernelC: kernC, drmC: drmC, dtsi: dtsi, genericC: genC, initTable: initTbl };

      outFiles.push({ path: dPrefix + "lk/" + cSym + ".c", content: lkC });
      outFiles.push({ path: dPrefix + "lk/Makefile", content: "include $(srctree)/drivers/misc/mediatek/Makefile.custom\nobj-y += " + cSym + ".o\n" });
      outFiles.push({ path: dPrefix + "lk/mt_lcm_list_entry.txt", content: "extern LCM_DRIVER " + cSym + "_lcm_drv;\n&" + cSym + "_lcm_drv,\n" });
      outFiles.push({ path: dPrefix + "kernel_mtk/" + cSym + ".c", content: kernC });
      outFiles.push({ path: dPrefix + "kernel_mtk/Makefile", content: "obj-y += " + cSym + ".o\n" });
      outFiles.push({ path: dPrefix + "kernel_mtk/Kconfig", content: "config CUSTOM_KERNEL_LCM_" + cSym.toUpperCase() + "\n\tbool \"Enable " + cSym + " LCM driver\"\n\tdefault y\n" });
      outFiles.push({ path: dPrefix + "drm_panel/panel-" + cSym + ".c", content: drmC });
      outFiles.push({ path: dPrefix + "drm_panel/" + cSym + ".dtsi", content: dtsi });
      outFiles.push({ path: dPrefix + "drm_panel/Makefile", content: "obj-$(CONFIG_DRM_PANEL_" + cSym.toUpperCase() + ") += panel-" + cSym + ".o\n" });
      outFiles.push({ path: dPrefix + "drm_panel/Kconfig", content: "config DRM_PANEL_" + cSym.toUpperCase() + "\n\ttristate \"DRM MIPI DSI panel " + cSym + "\"\n\tdepends on OF && DRM_MIPI_DSI\n" });
      outFiles.push({ path: dPrefix + "generic_mipi/" + cSym + "_generic.c", content: genC });
      outFiles.push({ path: dPrefix + "init_commands_table.txt", content: initTbl });
    }

    res.outFiles = outFiles;
    res.addressesReportTxt = outFiles[0].content;
    res.addressesReportMd = outFiles[1].content;
    return res;
  }

  var api = {
    analyzeBinaryAndBuildOut: analyzeBinaryAndBuildOut,
    toHex: toHex,
    vaToFileOff: vaToFileOff
  };

  if (typeof module !== "undefined" && module.exports) {
    module.exports = api;
  }
  global.LcmEngine = api;
})(typeof window !== "undefined" ? window : globalThis);
