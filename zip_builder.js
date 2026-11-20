(function (global) {
  "use strict";

  var CRC_TABLE = new Uint32Array(256);
  for (var i = 0; i < 256; i++) {
    var c = i;
    for (var k = 0; k < 8; k++) {
      c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
    }
    CRC_TABLE[i] = c >>> 0;
  }

  function crc32(bytes) {
    var c = 0xffffffff;
    for (var i = 0; i < bytes.length; i++) {
      c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
    }
    return (c ^ 0xffffffff) >>> 0;
  }

  function encodeUtf8(str) {
    if (typeof TextEncoder !== "undefined") {
      return new TextEncoder().encode(str);
    }
    var out = new Uint8Array(str.length);
    for (var i = 0; i < str.length; i++) {
      out[i] = str.charCodeAt(i) & 0xff;
    }
    return out;
  }

  function ZipBuilder() {
    this.entries = [];
  }

  ZipBuilder.prototype.addFile = function (path, data) {
    var normPath = String(path).replace(/\\/g, "/").replace(/^\/+/, "");
    var nameBytes = encodeUtf8(normPath);
    var bodyBytes = data instanceof Uint8Array ? data : encodeUtf8(String(data));
    this.entries.push({
      nameBytes: nameBytes,
      bodyBytes: bodyBytes,
      crc: crc32(bodyBytes),
      offset: 0
    });
  };

  ZipBuilder.prototype.buildUint8Array = function () {
    var totalLocal = 0;
    var totalCentral = 0;
    for (var i = 0; i < this.entries.length; i++) {
      var e = this.entries[i];
      totalLocal += 30 + e.nameBytes.length + e.bodyBytes.length;
      totalCentral += 46 + e.nameBytes.length;
    }
    var totalSize = totalLocal + totalCentral + 22;
    var out = new Uint8Array(totalSize);
    var dv = new DataView(out.buffer);
    var pos = 0;

    for (var i = 0; i < this.entries.length; i++) {
      var e = this.entries[i];
      e.offset = pos;
      dv.setUint32(pos, 0x04034b50, true);
      dv.setUint16(pos + 4, 20, true);
      dv.setUint16(pos + 6, 0x0800, true);
      dv.setUint16(pos + 8, 0, true);
      dv.setUint16(pos + 10, 0, true);
      dv.setUint16(pos + 12, 0x5421, true);
      dv.setUint32(pos + 14, e.crc, true);
      dv.setUint32(pos + 18, e.bodyBytes.length, true);
      dv.setUint32(pos + 22, e.bodyBytes.length, true);
      dv.setUint16(pos + 26, e.nameBytes.length, true);
      dv.setUint16(pos + 28, 0, true);
      pos += 30;
      out.set(e.nameBytes, pos);
      pos += e.nameBytes.length;
      out.set(e.bodyBytes, pos);
      pos += e.bodyBytes.length;
    }

    var cdStart = pos;
    for (var i = 0; i < this.entries.length; i++) {
      var e = this.entries[i];
      dv.setUint32(pos, 0x02014b50, true);
      dv.setUint16(pos + 4, 20, true);
      dv.setUint16(pos + 6, 20, true);
      dv.setUint16(pos + 8, 0x0800, true);
      dv.setUint16(pos + 10, 0, true);
      dv.setUint16(pos + 12, 0, true);
      dv.setUint16(pos + 14, 0x5421, true);
      dv.setUint32(pos + 16, e.crc, true);
      dv.setUint32(pos + 20, e.bodyBytes.length, true);
      dv.setUint32(pos + 24, e.bodyBytes.length, true);
      dv.setUint16(pos + 28, e.nameBytes.length, true);
      dv.setUint16(pos + 30, 0, true);
      dv.setUint16(pos + 32, 0, true);
      dv.setUint16(pos + 34, 0, true);
      dv.setUint16(pos + 36, 0, true);
      dv.setUint32(pos + 38, 0, true);
      dv.setUint32(pos + 42, e.offset, true);
      pos += 46;
      out.set(e.nameBytes, pos);
      pos += e.nameBytes.length;
    }

    var cdSize = pos - cdStart;
    dv.setUint32(pos, 0x06054b50, true);
    dv.setUint16(pos + 4, 0, true);
    dv.setUint16(pos + 6, 0, true);
    dv.setUint16(pos + 8, this.entries.length, true);
    dv.setUint16(pos + 10, this.entries.length, true);
    dv.setUint32(pos + 12, cdSize, true);
    dv.setUint32(pos + 16, cdStart, true);
    dv.setUint16(pos + 20, 0, true);
    return out;
  };

  if (typeof module !== "undefined" && module.exports) {
    module.exports = { ZipBuilder: ZipBuilder };
  }
  global.ZipBuilder = ZipBuilder;
})(typeof window !== "undefined" ? window : globalThis);
