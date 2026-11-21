(function (global) {
  "use strict";

  var PARAMS_ADDR = 0x20000000;
  var UTIL_SRC_ADDR = 0x20010000;
  var TRAP_BASE_ADDR = 0x20020000;
  var STACK_ADDR = 0x30000000;
  var RET_SENTINEL = 0x3000f000;

  function signExtend(val, bits) {
    var shift = 32 - bits;
    return (val << shift) >> shift;
  }

  function ror32(val, rot) {
    rot = rot & 31;
    if (rot === 0) return val >>> 0;
    return ((val >>> rot) | (val << (32 - rot))) >>> 0;
  }

  function thumbExpandImmC(imm12, carryIn) {
    if ((imm12 & 0xc00) === 0) {
      var byteVal = imm12 & 0xff;
      var type = (imm12 >>> 8) & 3;
      if (type === 0) return [byteVal, carryIn];
      if (type === 1) return [((byteVal << 16) | byteVal) >>> 0, carryIn];
      if (type === 2) return [((byteVal << 24) | (byteVal << 8)) >>> 0, carryIn];
      return [((byteVal << 24) | (byteVal << 16) | (byteVal << 8) | byteVal) >>> 0, carryIn];
    }
    var unrotated = 0x80 | (imm12 & 0x7f);
    var amount = (imm12 >>> 7) & 0x1f;
    var res = ror32(unrotated, amount);
    return [res, (res >>> 31) & 1];
  }

  function shiftWithCarry(val, type, amount, carryIn) {
    val = val >>> 0;
    if (amount === 0) {
      return [val, carryIn];
    }
    if (type === 0) {
      if (amount < 32) {
        return [(val << amount) >>> 0, (val >>> (32 - amount)) & 1];
      }
      if (amount === 32) return [0, val & 1];
      return [0, 0];
    }
    if (type === 1) {
      if (amount < 32) return [(val >>> amount) >>> 0, (val >>> (amount - 1)) & 1];
      if (amount === 32) return [0, (val >>> 31) & 1];
      return [0, 0];
    }
    if (type === 2) {
      var sval = val | 0;
      if (amount < 32) return [(sval >> amount) >>> 0, (val >>> (amount - 1)) & 1];
      var bit = (val >>> 31) & 1;
      return [bit ? 0xffffffff : 0, bit];
    }
    var r = amount & 31;
    if (r === 0) return [val, (val >>> 31) & 1];
    var out = ror32(val, r);
    return [out, (out >>> 31) & 1];
  }

  function addWithCarry32(a, b, carryIn) {
    var ua = a >>> 0;
    var ub = b >>> 0;
    var c = carryIn ? 1 : 0;
    var sum = ua + ub + c;
    var res = sum >>> 0;
    var carryOut = sum > 0xffffffff ? 1 : 0;
    var sa = ua | 0;
    var sb = ub | 0;
    var sres = res | 0;
    var overflow = ((sa >= 0 && sb >= 0 && sres < 0) || (sa < 0 && sb < 0 && sres >= 0)) ? 1 : 0;
    return [res, carryOut, overflow];
  }

  function ArmMicroEmulator(data, baseAddress, architecture) {
    this.data = data;
    this.dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    this.baseAddress = baseAddress >>> 0;
    this.endAddress = (this.baseAddress + data.length) >>> 0;
    this.architecture = architecture || "ARM32";
    this.paramsBuf = new Uint8Array(0x2000);
    this.paramsDv = new DataView(this.paramsBuf.buffer);
    this.utilBuf = new Uint8Array(0x2000);
    this.utilDv = new DataView(this.utilBuf.buffer);
    this.stackBuf = new Uint8Array(0x10000);
    this.stackDv = new DataView(this.stackBuf.buffer);
    for (var i = 0; i < 128; i++) {
      this.utilDv.setUint32(i * 4, (TRAP_BASE_ADDR + i * 4) >>> 0, true);
    }
    this.dirtyPages = new Map();
    this.regs = new Uint32Array(16);
    this.flagN = 0;
    this.flagZ = 0;
    this.flagC = 0;
    this.flagV = 0;
    this.thumb = false;
    this.itState = 0;
    this.activeWriteHook = null;
  }

  ArmMicroEmulator.prototype.resetScratch = function () {
    this.paramsBuf.fill(0);
    this.stackBuf.fill(0);
    this.dirtyPages.clear();
    this.regs.fill(0);
    this.flagN = 0;
    this.flagZ = 0;
    this.flagC = 0;
    this.flagV = 0;
    this.itState = 0;
    this.activeWriteHook = null;
  };

  ArmMicroEmulator.prototype._getDirtyPage = function (addr, create) {
    var pageBase = (addr & 0xffff0000) >>> 0;
    var page = this.dirtyPages.get(pageBase);
    if (!page && create) {
      page = new Uint8Array(0x10000);
      var binStart = Math.max(pageBase, this.baseAddress);
      var binEnd = Math.min((pageBase + 0x10000) >>> 0, this.endAddress);
      if (binEnd > binStart) {
        var srcOff = (binStart - this.baseAddress) >>> 0;
        var dstOff = (binStart - pageBase) >>> 0;
        var len = (binEnd - binStart) >>> 0;
        page.set(this.data.subarray(srcOff, srcOff + len), dstOff);
      }
      this.dirtyPages.set(pageBase, page);
    }
    return page || null;
  };

  ArmMicroEmulator.prototype.isReadable = function (addr) {
    var u = addr >>> 0;
    if (u >= this.baseAddress && u < this.endAddress) return true;
    if (u >= PARAMS_ADDR && u < PARAMS_ADDR + 0x2000) return true;
    if (u >= UTIL_SRC_ADDR && u < UTIL_SRC_ADDR + 0x2000) return true;
    if (u >= STACK_ADDR && u < STACK_ADDR + 0x10000) return true;
    return this.dirtyPages.has((u & 0xffff0000) >>> 0);
  };

  ArmMicroEmulator.prototype.readU8 = function (addr) {
    var u = addr >>> 0;
    if (u >= PARAMS_ADDR && u < PARAMS_ADDR + 0x2000) return this.paramsBuf[u - PARAMS_ADDR];
    if (u >= UTIL_SRC_ADDR && u < UTIL_SRC_ADDR + 0x2000) return this.utilBuf[u - UTIL_SRC_ADDR];
    if (u >= STACK_ADDR && u < STACK_ADDR + 0x10000) return this.stackBuf[u - STACK_ADDR];
    var page = this.dirtyPages.get((u & 0xffff0000) >>> 0);
    if (page) return page[u & 0xffff];
    if (u >= this.baseAddress && u < this.endAddress) return this.data[u - this.baseAddress];
    return 0;
  };

  ArmMicroEmulator.prototype.readU16 = function (addr) {
    var u = addr >>> 0;
    if (u >= PARAMS_ADDR && u + 2 <= PARAMS_ADDR + 0x2000) return this.paramsDv.getUint16(u - PARAMS_ADDR, true);
    if (u >= UTIL_SRC_ADDR && u + 2 <= UTIL_SRC_ADDR + 0x2000) return this.utilDv.getUint16(u - UTIL_SRC_ADDR, true);
    if (u >= STACK_ADDR && u + 2 <= STACK_ADDR + 0x10000) return this.stackDv.getUint16(u - STACK_ADDR, true);
    var page = this.dirtyPages.get((u & 0xffff0000) >>> 0);
    if (page && (u & 0xffff) <= 0xfffe) {
      return page[u & 0xffff] | (page[(u & 0xffff) + 1] << 8);
    }
    if (u >= this.baseAddress && u + 2 <= this.endAddress) return this.dv.getUint16(u - this.baseAddress, true);
    return this.readU8(u) | (this.readU8(u + 1) << 8);
  };

  ArmMicroEmulator.prototype.readU32 = function (addr) {
    var u = addr >>> 0;
    if (u >= PARAMS_ADDR && u + 4 <= PARAMS_ADDR + 0x2000) return this.paramsDv.getUint32(u - PARAMS_ADDR, true);
    if (u >= UTIL_SRC_ADDR && u + 4 <= UTIL_SRC_ADDR + 0x2000) return this.utilDv.getUint32(u - UTIL_SRC_ADDR, true);
    if (u >= STACK_ADDR && u + 4 <= STACK_ADDR + 0x10000) return this.stackDv.getUint32(u - STACK_ADDR, true);
    var page = this.dirtyPages.get((u & 0xffff0000) >>> 0);
    if (page && (u & 0xffff) <= 0xfffc) {
      var o = u & 0xffff;
      return (page[o] | (page[o + 1] << 8) | (page[o + 2] << 16) | (page[o + 3] << 24)) >>> 0;
    }
    if (u >= this.baseAddress && u + 4 <= this.endAddress) return this.dv.getUint32(u - this.baseAddress, true);
    return (this.readU8(u) | (this.readU8(u + 1) << 8) | (this.readU8(u + 2) << 16) | (this.readU8(u + 3) << 24)) >>> 0;
  };

  ArmMicroEmulator.prototype.writeU8 = function (addr, val) {
    var u = addr >>> 0;
    var b = val & 0xff;
    if (u >= PARAMS_ADDR && u < PARAMS_ADDR + 0x2000) {
      var off = u - PARAMS_ADDR;
      this.paramsBuf[off] = b;
      if (this.activeWriteHook) this.activeWriteHook(off, 1, b);
      return;
    }
    if (u >= UTIL_SRC_ADDR && u < UTIL_SRC_ADDR + 0x2000) {
      this.utilBuf[u - UTIL_SRC_ADDR] = b;
      return;
    }
    if (u >= STACK_ADDR && u < STACK_ADDR + 0x10000) {
      this.stackBuf[u - STACK_ADDR] = b;
      return;
    }
    if (u < 0x1000) return;
    var page = this._getDirtyPage(u, true);
    page[u & 0xffff] = b;
  };

  ArmMicroEmulator.prototype.writeU16 = function (addr, val) {
    var u = addr >>> 0;
    var v = val & 0xffff;
    if (u >= PARAMS_ADDR && u + 2 <= PARAMS_ADDR + 0x2000) {
      var off = u - PARAMS_ADDR;
      this.paramsDv.setUint16(off, v, true);
      if (this.activeWriteHook) this.activeWriteHook(off, 2, v);
      return;
    }
    if (u >= STACK_ADDR && u + 2 <= STACK_ADDR + 0x10000) {
      this.stackDv.setUint16(u - STACK_ADDR, v, true);
      return;
    }
    this.writeU8(u, v & 0xff);
    this.writeU8(u + 1, (v >>> 8) & 0xff);
  };

  ArmMicroEmulator.prototype.writeU32 = function (addr, val) {
    var u = addr >>> 0;
    var v = val >>> 0;
    if (u >= PARAMS_ADDR && u + 4 <= PARAMS_ADDR + 0x2000) {
      var off = u - PARAMS_ADDR;
      this.paramsDv.setUint32(off, v, true);
      if (this.activeWriteHook) this.activeWriteHook(off, 4, v);
      return;
    }
    if (u >= STACK_ADDR && u + 4 <= STACK_ADDR + 0x10000) {
      this.stackDv.setUint32(u - STACK_ADDR, v, true);
      return;
    }
    if (u < 0x1000) return;
    var page = this._getDirtyPage(u, true);
    var o = u & 0xffff;
    if (o <= 0xfffc) {
      page[o] = v & 0xff;
      page[o + 1] = (v >>> 8) & 0xff;
      page[o + 2] = (v >>> 16) & 0xff;
      page[o + 3] = (v >>> 24) & 0xff;
      return;
    }
    this.writeU8(u, v & 0xff);
    this.writeU8(u + 1, (v >>> 8) & 0xff);
    this.writeU8(u + 2, (v >>> 16) & 0xff);
    this.writeU8(u + 3, (v >>> 24) & 0xff);
  };

  ArmMicroEmulator.prototype.checkCond = function (cond) {
    switch (cond & 0xf) {
      case 0: return this.flagZ === 1;
      case 1: return this.flagZ === 0;
      case 2: return this.flagC === 1;
      case 3: return this.flagC === 0;
      case 4: return this.flagN === 1;
      case 5: return this.flagN === 0;
      case 6: return this.flagV === 1;
      case 7: return this.flagV === 0;
      case 8: return this.flagC === 1 && this.flagZ === 0;
      case 9: return this.flagC === 0 || this.flagZ === 1;
      case 10: return this.flagN === this.flagV;
      case 11: return this.flagN !== this.flagV;
      case 12: return this.flagZ === 0 && this.flagN === this.flagV;
      case 13: return this.flagZ === 1 || this.flagN !== this.flagV;
      case 14: return true;
      default: return true;
    }
  };

  ArmMicroEmulator.prototype.setBranch = function (target) {
    var t = target >>> 0;
    if (t === RET_SENTINEL || t === (RET_SENTINEL & ~1)) {
      this.regs[15] = RET_SENTINEL;
      return;
    }
    this.thumb = (t & 1) !== 0;
    this.regs[15] = (t & ~1) >>> 0;
  };

  ArmMicroEmulator.prototype._execAlu = function (opcode, rnVal, op2, shiftCarry, rd, setFlags) {
    var res = 0;
    var cOut = shiftCarry;
    var vOut = this.flagV;
    var writeRd = true;
    var tmp;
    switch (opcode) {
      case 0:
        res = (rnVal & op2) >>> 0;
        break;
      case 1:
        res = (rnVal ^ op2) >>> 0;
        break;
      case 2:
        tmp = addWithCarry32(rnVal, (~op2) >>> 0, 1);
        res = tmp[0]; cOut = tmp[1]; vOut = tmp[2];
        break;
      case 3:
        tmp = addWithCarry32(op2, (~rnVal) >>> 0, 1);
        res = tmp[0]; cOut = tmp[1]; vOut = tmp[2];
        break;
      case 4:
        tmp = addWithCarry32(rnVal, op2, 0);
        res = tmp[0]; cOut = tmp[1]; vOut = tmp[2];
        break;
      case 5:
        tmp = addWithCarry32(rnVal, op2, this.flagC);
        res = tmp[0]; cOut = tmp[1]; vOut = tmp[2];
        break;
      case 6:
        tmp = addWithCarry32(rnVal, (~op2) >>> 0, this.flagC);
        res = tmp[0]; cOut = tmp[1]; vOut = tmp[2];
        break;
      case 7:
        tmp = addWithCarry32(op2, (~rnVal) >>> 0, this.flagC);
        res = tmp[0]; cOut = tmp[1]; vOut = tmp[2];
        break;
      case 8:
        res = (rnVal & op2) >>> 0;
        writeRd = false;
        setFlags = true;
        break;
      case 9:
        res = (rnVal ^ op2) >>> 0;
        writeRd = false;
        setFlags = true;
        break;
      case 10:
        tmp = addWithCarry32(rnVal, (~op2) >>> 0, 1);
        res = tmp[0]; cOut = tmp[1]; vOut = tmp[2];
        writeRd = false;
        setFlags = true;
        break;
      case 11:
        tmp = addWithCarry32(rnVal, op2, 0);
        res = tmp[0]; cOut = tmp[1]; vOut = tmp[2];
        writeRd = false;
        setFlags = true;
        break;
      case 12:
        res = (rnVal | op2) >>> 0;
        break;
      case 13:
        res = op2 >>> 0;
        break;
      case 14:
        res = (rnVal & (~op2)) >>> 0;
        break;
      case 15:
        res = (~op2) >>> 0;
        break;
    }
    if (setFlags && rd !== 15) {
      this.flagN = (res >>> 31) & 1;
      this.flagZ = res === 0 ? 1 : 0;
      this.flagC = cOut;
      this.flagV = vOut;
    }
    if (writeRd) {
      if (rd === 15) {
        this.setBranch(res | (this.thumb ? 1 : 0));
      } else {
        this.regs[rd] = res >>> 0;
      }
    }
  };

  ArmMicroEmulator.prototype.stepArm = function () {
    var pc = this.regs[15] >>> 0;
    var w = this.readU32(pc);
    var cond = w >>> 28;
    if (cond === 0xf) {
      if (((w & 0xfe000000) >>> 0) === 0xfa000000) {
        var hbit = (w >>> 24) & 1;
        var imm24b = signExtend(w & 0x00ffffff, 24);
        var tgt = (pc + 8 + (imm24b << 2) + (hbit << 1)) >>> 0;
        this.regs[14] = (pc + 4) >>> 0;
        this.thumb = true;
        this.regs[15] = tgt & ~1;
        return;
      }
      this.regs[15] = (pc + 4) >>> 0;
      return;
    }
    this.regs[15] = (pc + 4) >>> 0;
    if (!this.checkCond(cond)) return;

    if ((w & 0x0ffffff0) === 0x012fff10 || (w & 0x0ffffff0) === 0x012fff30) {
      var rmB = w & 0xf;
      var targetB = rmB === 15 ? (pc + 8) >>> 0 : this.regs[rmB];
      if ((w & 0x30) === 0x30) this.regs[14] = (pc + 4) >>> 0;
      this.setBranch(targetB);
      return;
    }

    if ((w & 0x0fff0ff0) === 0x016f0f10) {
      var rdClz = (w >>> 12) & 0xf;
      var rmClz = w & 0xf;
      this.regs[rdClz] = Math.clz32(this.regs[rmClz]);
      return;
    }

    if (((w >>> 25) & 7) === 5) {
      var link = (w >>> 24) & 1;
      var imm24 = signExtend(w & 0x00ffffff, 24);
      var bTgt = (pc + 8 + (imm24 << 2)) >>> 0;
      if (link) this.regs[14] = (pc + 4) >>> 0;
      this.regs[15] = bTgt;
      return;
    }

    if ((w & 0x0fb00000) === 0x03000000) {
      var isMovt = ((w >>> 22) & 1) === 1;
      var imm16 = (((w >>> 16) & 0xf) << 12) | (w & 0xfff);
      var rdM = (w >>> 12) & 0xf;
      if (isMovt) {
        this.regs[rdM] = ((imm16 << 16) | (this.regs[rdM] & 0xffff)) >>> 0;
      } else {
        this.regs[rdM] = imm16 >>> 0;
      }
      return;
    }

    if (((w >>> 25) & 7) === 4) {
      var pM = (w >>> 24) & 1;
      var uM = (w >>> 23) & 1;
      var wM = (w >>> 21) & 1;
      var lM = (w >>> 20) & 1;
      var rnM = (w >>> 16) & 0xf;
      var rlist = w & 0xffff;
      var cnt = 0;
      for (var bit = 0; bit < 16; bit++) {
        if ((rlist >>> bit) & 1) cnt++;
      }
      var base = this.regs[rnM];
      var startAddr;
      var newBase;
      if (uM) {
        startAddr = pM ? (base + 4) >>> 0 : base;
        newBase = (base + cnt * 4) >>> 0;
      } else {
        startAddr = pM ? (base - cnt * 4) >>> 0 : (base - cnt * 4 + 4) >>> 0;
        newBase = (base - cnt * 4) >>> 0;
      }
      var addr = startAddr;
      for (var r = 0; r < 16; r++) {
        if ((rlist >>> r) & 1) {
          if (lM) {
            var loaded = this.readU32(addr);
            if (r === 15) {
              this.setBranch(loaded);
            } else {
              this.regs[r] = loaded;
            }
          } else {
            var valS = r === 15 ? (pc + 8) >>> 0 : this.regs[r];
            this.writeU32(addr, valS);
          }
          addr = (addr + 4) >>> 0;
        }
      }
      if (wM) this.regs[rnM] = newBase;
      return;
    }

    if ((w & 0x0fc000f0) === 0x00000090) {
      var acc = (w >>> 21) & 1;
      var sMul = (w >>> 20) & 1;
      var rdMul = (w >>> 16) & 0xf;
      var rnMul = (w >>> 12) & 0xf;
      var rsMul = (w >>> 8) & 0xf;
      var rmMul = w & 0xf;
      var prod = Math.imul(this.regs[rmMul], this.regs[rsMul]);
      if (acc) prod = (prod + (this.regs[rnMul] | 0)) | 0;
      var uprod = prod >>> 0;
      this.regs[rdMul] = uprod;
      if (sMul) {
        this.flagN = (uprod >>> 31) & 1;
        this.flagZ = uprod === 0 ? 1 : 0;
      }
      return;
    }

    if (((w >>> 25) & 7) === 0 && (w & 0x90) === 0x90 && (w & 0x60) !== 0) {
      var pH = (w >>> 24) & 1;
      var uH = (w >>> 23) & 1;
      var iH = (w >>> 22) & 1;
      var wH = (w >>> 21) & 1;
      var lH = (w >>> 20) & 1;
      var rnH = (w >>> 16) & 0xf;
      var rdH = (w >>> 12) & 0xf;
      var sh = (w >>> 5) & 3;
      var baseH = rnH === 15 ? (pc + 8) >>> 0 : this.regs[rnH];
      var offH = iH ? (((w >>> 4) & 0xf0) | (w & 0xf)) : this.regs[w & 0xf];
      if (!uH) offH = -offH;
      var ea = pH ? ((baseH + offH) >>> 0) : baseH;
      if (lH) {
        if (sh === 1) this.regs[rdH] = this.readU16(ea);
        else if (sh === 2) this.regs[rdH] = signExtend(this.readU8(ea), 8) >>> 0;
        else if (sh === 3) this.regs[rdH] = signExtend(this.readU16(ea), 16) >>> 0;
      } else if (sh === 1) {
        this.writeU16(ea, this.regs[rdH]);
      } else if (sh === 2 && (rdH & 1) === 0) {
        this.regs[rdH] = this.readU32(ea);
        this.regs[rdH + 1] = this.readU32((ea + 4) >>> 0);
      } else if (sh === 3 && (rdH & 1) === 0) {
        this.writeU32(ea, this.regs[rdH]);
        this.writeU32((ea + 4) >>> 0, this.regs[rdH + 1]);
      }
      if (!pH || wH) this.regs[rnH] = (baseH + offH) >>> 0;
      return;
    }

    if (((w >>> 26) & 3) === 0) {
      var iBit = (w >>> 25) & 1;
      var opcode = (w >>> 21) & 0xf;
      var sBit = (w >>> 20) & 1;
      var rn = (w >>> 16) & 0xf;
      var rd = (w >>> 12) & 0xf;
      var rnVal = rn === 15 ? (pc + 8) >>> 0 : this.regs[rn];
      var op2 = 0;
      var shCarry = this.flagC;
      if (iBit) {
        var imm8 = w & 0xff;
        var rot = ((w >>> 8) & 0xf) * 2;
        op2 = ror32(imm8, rot);
        if (rot !== 0) shCarry = (op2 >>> 31) & 1;
      } else {
        var rm = w & 0xf;
        var stype = (w >>> 5) & 3;
        var regShift = (w >>> 4) & 1;
        var rmVal = rm === 15 ? (pc + (regShift ? 12 : 8)) >>> 0 : this.regs[rm];
        var samount;
        if (regShift) {
          samount = this.regs[(w >>> 8) & 0xf] & 0xff;
          if (rn === 15) rnVal = (pc + 12) >>> 0;
        } else {
          samount = (w >>> 7) & 0x1f;
          if (samount === 0 && (stype === 1 || stype === 2)) samount = 32;
          if (samount === 0 && stype === 3) {
            op2 = ((this.flagC << 31) | (rmVal >>> 1)) >>> 0;
            shCarry = rmVal & 1;
            this._execAlu(opcode, rnVal, op2, shCarry, rd, sBit === 1);
            return;
          }
        }
        var shRes = shiftWithCarry(rmVal, stype, samount, this.flagC);
        op2 = shRes[0];
        shCarry = shRes[1];
      }
      this._execAlu(opcode, rnVal, op2, shCarry, rd, sBit === 1);
      return;
    }

    if (((w >>> 26) & 3) === 1) {
      var iL = (w >>> 25) & 1;
      var pL = (w >>> 24) & 1;
      var uL = (w >>> 23) & 1;
      var bL = (w >>> 22) & 1;
      var wL = (w >>> 21) & 1;
      var lL = (w >>> 20) & 1;
      var rnL = (w >>> 16) & 0xf;
      var rdL = (w >>> 12) & 0xf;
      var baseL = rnL === 15 ? (pc + 8) >>> 0 : this.regs[rnL];
      var offL;
      if (iL === 0) {
        offL = w & 0xfff;
      } else {
        var rmL = w & 0xf;
        var stL = (w >>> 5) & 3;
        var saL = (w >>> 7) & 0x1f;
        if (saL === 0 && (stL === 1 || stL === 2)) saL = 32;
        offL = shiftWithCarry(this.regs[rmL], stL, saL, this.flagC)[0];
      }
      if (!uL) offL = -offL;
      var eaL = pL ? ((baseL + offL) >>> 0) : baseL;
      if (lL) {
        var vL = bL ? this.readU8(eaL) : this.readU32(eaL);
        if (rdL === 15) this.setBranch(vL);
        else this.regs[rdL] = vL >>> 0;
      } else {
        var sV = rdL === 15 ? (pc + 8) >>> 0 : this.regs[rdL];
        if (bL) this.writeU8(eaL, sV);
        else this.writeU32(eaL, sV);
      }
      if ((!pL || wL) && rnL !== 15) {
        this.regs[rnL] = (baseL + offL) >>> 0;
      }
    }
  };

  ArmMicroEmulator.prototype._advanceIt = function () {
    if ((this.itState & 0xf) === 0) return true;
    var cond = (this.itState >>> 4) & 0xf;
    var ok = this.checkCond(cond);
    var low5 = this.itState & 0x1f;
    var nextLow5 = (low5 << 1) & 0x1f;
    if ((nextLow5 & 0xf) === 0) {
      this.itState = 0;
    } else {
      var nextFirstCond = (this.itState >>> 4) & 0xe;
      var bit4 = (nextLow5 >>> 4) & 1;
      this.itState = ((nextFirstCond | bit4) << 4) | (nextLow5 & 0xf);
    }
    return ok;
  };

  ArmMicroEmulator.prototype.stepThumb32 = function (pc, hw1, hw2) {
    this.regs[15] = (pc + 4) >>> 0;
    if (!this._advanceIt()) return;

    if ((hw1 & 0xf800) === 0xf000 && (hw2 & 0x8000) === 0x8000) {
      var sB = (hw1 >>> 10) & 1;
      var j1 = (hw2 >>> 13) & 1;
      var j2 = (hw2 >>> 11) & 1;
      var bit14 = (hw2 >>> 14) & 1;
      var bit12 = (hw2 >>> 12) & 1;

      if (bit14 === 1 && bit12 === 1) {
        var i1 = ((~(j1 ^ sB)) & 1);
        var i2 = ((~(j2 ^ sB)) & 1);
        var imm25 = (sB << 24) | (i1 << 23) | (i2 << 22) | ((hw1 & 0x3ff) << 12) | ((hw2 & 0x7ff) << 1);
        this.regs[14] = ((pc + 4) | 1) >>> 0;
        this.regs[15] = (pc + 4 + signExtend(imm25, 25)) >>> 0;
        return;
      }
      if (bit14 === 1 && bit12 === 0) {
        var i1x = ((~(j1 ^ sB)) & 1);
        var i2x = ((~(j2 ^ sB)) & 1);
        var imm25x = (sB << 24) | (i1x << 23) | (i2x << 22) | ((hw1 & 0x3ff) << 12) | ((hw2 & 0x7fe) << 1);
        this.regs[14] = ((pc + 4) | 1) >>> 0;
        var baseAligned = (pc + 4) & ~3;
        this.thumb = false;
        this.regs[15] = (baseAligned + signExtend(imm25x, 25)) >>> 0;
        return;
      }
      if (bit14 === 0 && bit12 === 1) {
        var i1w = ((~(j1 ^ sB)) & 1);
        var i2w = ((~(j2 ^ sB)) & 1);
        var imm25w = (sB << 24) | (i1w << 23) | (i2w << 22) | ((hw1 & 0x3ff) << 12) | ((hw2 & 0x7ff) << 1);
        this.regs[15] = (pc + 4 + signExtend(imm25w, 25)) >>> 0;
        return;
      }
      if (bit14 === 0 && bit12 === 0 && ((hw1 >>> 6) & 0xf) < 14) {
        var cc = (hw1 >>> 6) & 0xf;
        if (this.checkCond(cc)) {
          var imm21 = (sB << 20) | (j2 << 19) | (j1 << 18) | ((hw1 & 0x3f) << 12) | ((hw2 & 0x7ff) << 1);
          this.regs[15] = (pc + 4 + signExtend(imm21, 21)) >>> 0;
        }
        return;
      }
      return;
    }

    if ((hw1 & 0xfb70) === 0xf240 && (hw2 & 0x8000) === 0) {
      var isMovt2 = ((hw1 >>> 7) & 1) === 1;
      var i4 = hw1 & 0xf;
      var ib = (hw1 >>> 10) & 1;
      var i3 = (hw2 >>> 12) & 7;
      var rd2 = (hw2 >>> 8) & 0xf;
      var i8 = hw2 & 0xff;
      var imm16t = (i4 << 12) | (ib << 11) | (i3 << 8) | i8;
      if (isMovt2) {
        this.regs[rd2] = ((imm16t << 16) | (this.regs[rd2] & 0xffff)) >>> 0;
      } else {
        this.regs[rd2] = imm16t >>> 0;
      }
      return;
    }

    if ((hw1 & 0xfb00) === 0xf200 && (hw2 & 0x8000) === 0) {
      var opPlain = (hw1 >>> 4) & 0x1f;
      var ibP = (hw1 >>> 10) & 1;
      var rnP = hw1 & 0xf;
      var imm12P = (ibP << 11) | (((hw2 >>> 12) & 7) << 8) | (hw2 & 0xff);
      var rdP = (hw2 >>> 8) & 0xf;
      var rnValP = rnP === 15 ? ((pc + 4) & ~3) >>> 0 : this.regs[rnP];
      if (opPlain === 0) {
        this.regs[rdP] = (rnValP + imm12P) >>> 0;
        return;
      }
      if (opPlain === 0x0a) {
        this.regs[rdP] = (rnValP - imm12P) >>> 0;
        return;
      }
    }

    if ((hw1 & 0xfa00) === 0xf000 && (hw2 & 0x8000) === 0) {
      var opT = (hw1 >>> 5) & 0xf;
      var sT = (hw1 >>> 4) & 1;
      var rnT = hw1 & 0xf;
      var rdT = (hw2 >>> 8) & 0xf;
      var imm12T = (((hw1 >>> 10) & 1) << 11) | (((hw2 >>> 12) & 7) << 8) | (hw2 & 0xff);
      var immRes = thumbExpandImmC(imm12T, this.flagC);
      var op2T = immRes[0];
      var scT = immRes[1];
      var rnValT = rnT === 15 ? 0 : this.regs[rnT];
      var mapOp = -1;
      if (opT === 0) mapOp = rdT === 15 ? 8 : 0;
      else if (opT === 1) mapOp = 14;
      else if (opT === 2) mapOp = rnT === 15 ? 13 : 12;
      else if (opT === 3) mapOp = rnT === 15 ? 15 : -2;
      else if (opT === 4) mapOp = rdT === 15 ? 9 : 1;
      else if (opT === 8) mapOp = rdT === 15 ? 11 : 4;
      else if (opT === 10) mapOp = 5;
      else if (opT === 11) mapOp = 6;
      else if (opT === 13) mapOp = rdT === 15 ? 10 : 2;
      else if (opT === 14) mapOp = 3;
      if (mapOp === -2) {
        this._execAlu(12, rnValT, (~op2T) >>> 0, scT, rdT, sT === 1);
      } else if (mapOp >= 0) {
        this._execAlu(mapOp, rnValT, op2T, scT, rdT, sT === 1);
      }
      return;
    }

    if ((hw1 & 0xfe00) === 0xea00) {
      var opS = (hw1 >>> 5) & 0xf;
      var sS = (hw1 >>> 4) & 1;
      var rnS = hw1 & 0xf;
      var rdS = (hw2 >>> 8) & 0xf;
      var rmS = hw2 & 0xf;
      var stS = (hw2 >>> 4) & 3;
      var saS = (((hw2 >>> 12) & 7) << 2) | ((hw2 >>> 6) & 3);
      if (saS === 0 && (stS === 1 || stS === 2)) saS = 32;
      var rnValS = rnS === 15 ? 0 : this.regs[rnS];
      var op2SRes = (saS === 0 && stS === 3)
        ? [((this.flagC << 31) | (this.regs[rmS] >>> 1)) >>> 0, this.regs[rmS] & 1]
        : shiftWithCarry(this.regs[rmS], stS, saS, this.flagC);
      var op2S = op2SRes[0];
      var scS = op2SRes[1];
      var mapOpS = -1;
      if (opS === 0) mapOpS = rdS === 15 ? 8 : 0;
      else if (opS === 1) mapOpS = 14;
      else if (opS === 2) mapOpS = rnS === 15 ? 13 : 12;
      else if (opS === 3) mapOpS = rnS === 15 ? 15 : -2;
      else if (opS === 4) mapOpS = rdS === 15 ? 9 : 1;
      else if (opS === 8) mapOpS = rdS === 15 ? 11 : 4;
      else if (opS === 10) mapOpS = 5;
      else if (opS === 11) mapOpS = 6;
      else if (opS === 13) mapOpS = rdS === 15 ? 10 : 2;
      else if (opS === 14) mapOpS = 3;
      if (mapOpS === -2) {
        this._execAlu(12, rnValS, (~op2S) >>> 0, scS, rdS, sS === 1);
      } else if (mapOpS >= 0) {
        this._execAlu(mapOpS, rnValS, op2S, scS, rdS, sS === 1);
      }
      return;
    }

    if ((hw1 & 0xffc0) === 0xe880 || (hw1 & 0xffc0) === 0xe900) {
      var uB = ((hw1 >>> 8) & 1) === 0;
      var lB = ((hw1 >>> 4) & 1) === 1;
      var wB = ((hw1 >>> 5) & 1) === 1;
      var rnB = hw1 & 0xf;
      var rlistB = hw2 & 0xffff;
      var cntB = 0;
      for (var k = 0; k < 16; k++) {
        if ((rlistB >>> k) & 1) cntB++;
      }
      var baseB = this.regs[rnB];
      var addrB = uB ? baseB : (baseB - cntB * 4) >>> 0;
      var curB = addrB;
      for (var reg = 0; reg < 16; reg++) {
        if ((rlistB >>> reg) & 1) {
          if (lB) {
            var lv = this.readU32(curB);
            if (reg === 15) this.setBranch(lv);
            else this.regs[reg] = lv;
          } else {
            this.writeU32(curB, this.regs[reg]);
          }
          curB = (curB + 4) >>> 0;
        }
      }
      if (wB) this.regs[rnB] = uB ? ((baseB + cntB * 4) >>> 0) : addrB;
      return;
    }

    if ((hw1 & 0xfe40) === 0xe840 || (hw1 & 0xfe40) === 0xe940) {
      var uD = (hw1 >>> 7) & 1;
      var pD = (hw1 >>> 8) & 1;
      var wD = (hw1 >>> 5) & 1;
      var lD = (hw1 >>> 4) & 1;
      var rnD = hw1 & 0xf;
      var rtD = (hw2 >>> 12) & 0xf;
      var rt2D = (hw2 >>> 8) & 0xf;
      var offD = (hw2 & 0xff) * 4;
      if (!uD) offD = -offD;
      var baseD = rnD === 15 ? ((pc + 4) & ~3) >>> 0 : this.regs[rnD];
      var eaD = pD ? ((baseD + offD) >>> 0) : baseD;
      if (lD) {
        this.regs[rtD] = this.readU32(eaD);
        this.regs[rt2D] = this.readU32((eaD + 4) >>> 0);
      } else {
        this.writeU32(eaD, this.regs[rtD]);
        this.writeU32((eaD + 4) >>> 0, this.regs[rt2D]);
      }
      if (!pD || wD) this.regs[rnD] = (baseD + offD) >>> 0;
      return;
    }

    if ((hw1 & 0xfff0) === 0xfab0 && (hw2 & 0xf0f0) === 0xf080) {
      var rmC = hw1 & 0xf;
      var rdC = (hw2 >>> 8) & 0xf;
      this.regs[rdC] = Math.clz32(this.regs[rmC]);
      return;
    }

    if ((hw1 & 0xff00) === 0xf800 || (hw1 & 0xff00) === 0xf900) {
      var lS = (hw1 >>> 4) & 1;
      var szS = (hw1 >>> 5) & 3;
      var signS = (hw1 >>> 8) & 1;
      var rnLs = hw1 & 0xf;
      var rtLs = (hw2 >>> 12) & 0xf;
      var uImm12 = (hw1 >>> 7) & 1;
      var baseLs = rnLs === 15 ? ((pc + 4) & ~3) >>> 0 : this.regs[rnLs];
      var eaLs = baseLs;
      var doWriteback = false;
      var newBaseLs = baseLs;
      if (rnLs === 15) {
        var offLit = hw2 & 0xfff;
        eaLs = uImm12 ? ((baseLs + offLit) >>> 0) : ((baseLs - offLit) >>> 0);
      } else if (uImm12) {
        eaLs = (baseLs + (hw2 & 0xfff)) >>> 0;
      } else if ((hw2 & 0x0800) !== 0) {
        var pB = (hw2 >>> 10) & 1;
        var uB2 = (hw2 >>> 9) & 1;
        var wB2 = (hw2 >>> 8) & 1;
        var imm8Ls = hw2 & 0xff;
        var dOff = uB2 ? imm8Ls : -imm8Ls;
        eaLs = pB ? ((baseLs + dOff) >>> 0) : baseLs;
        doWriteback = wB2 === 1 || pB === 0;
        newBaseLs = (baseLs + dOff) >>> 0;
      } else if ((hw2 & 0x0fc0) === 0) {
        var rmLs = hw2 & 0xf;
        var shLs = (hw2 >>> 4) & 3;
        eaLs = (baseLs + ((this.regs[rmLs] << shLs) >>> 0)) >>> 0;
      }
      if (lS) {
        var valR = 0;
        if (szS === 0) valR = signS ? (signExtend(this.readU8(eaLs), 8) >>> 0) : this.readU8(eaLs);
        else if (szS === 1) valR = signS ? (signExtend(this.readU16(eaLs), 16) >>> 0) : this.readU16(eaLs);
        else valR = this.readU32(eaLs);
        if (rtLs === 15) this.setBranch(valR);
        else this.regs[rtLs] = valR;
      } else {
        var valW = this.regs[rtLs];
        if (szS === 0) this.writeU8(eaLs, valW);
        else if (szS === 1) this.writeU16(eaLs, valW);
        else this.writeU32(eaLs, valW);
      }
      if (doWriteback) this.regs[rnLs] = newBaseLs;
    }
  };

  ArmMicroEmulator.prototype.stepThumb = function () {
    var pc = this.regs[15] >>> 0;
    var hw1 = this.readU16(pc);
    if ((hw1 & 0xf800) >= 0xe800) {
      var hw2 = this.readU16((pc + 2) >>> 0);
      this.stepThumb32(pc, hw1, hw2);
      return;
    }
    this.regs[15] = (pc + 2) >>> 0;

    if ((hw1 & 0xff00) === 0xbf00) {
      if (hw1 !== 0xbf00) {
        this.itState = hw1 & 0xff;
      }
      return;
    }

    var inIt = (this.itState & 0xf) !== 0;
    var condOk = this._advanceIt();
    if (inIt && !condOk) return;
    var updateFlags = !inIt;

    var top3 = hw1 >>> 13;
    if (top3 === 0) {
      var op0 = (hw1 >>> 11) & 3;
      var rm0 = (hw1 >>> 3) & 7;
      var rd0 = hw1 & 7;
      if (op0 < 3) {
        var imm5 = (hw1 >>> 6) & 0x1f;
        var a0 = imm5;
        if (a0 === 0 && (op0 === 1 || op0 === 2)) a0 = 32;
        var sh0 = shiftWithCarry(this.regs[rm0], op0, a0, this.flagC);
        this.regs[rd0] = sh0[0];
        if (updateFlags) {
          this.flagN = (sh0[0] >>> 31) & 1;
          this.flagZ = sh0[0] === 0 ? 1 : 0;
          this.flagC = sh0[1];
        }
        return;
      }
      var subOp = (hw1 >>> 9) & 3;
      var rn0 = (hw1 >>> 3) & 7;
      var rhs0 = (subOp >= 2) ? ((hw1 >>> 6) & 7) : this.regs[(hw1 >>> 6) & 7];
      var isSub = (subOp & 1) === 1;
      this._execAlu(isSub ? 2 : 4, this.regs[rn0], rhs0, this.flagC, rd0, updateFlags);
      return;
    }

    if (top3 === 1) {
      var op1 = (hw1 >>> 11) & 3;
      var r1 = (hw1 >>> 8) & 7;
      var imm8 = hw1 & 0xff;
      if (op1 === 0) this._execAlu(13, 0, imm8, this.flagC, r1, updateFlags);
      else if (op1 === 1) this._execAlu(10, this.regs[r1], imm8, this.flagC, r1, true);
      else if (op1 === 2) this._execAlu(4, this.regs[r1], imm8, this.flagC, r1, updateFlags);
      else this._execAlu(2, this.regs[r1], imm8, this.flagC, r1, updateFlags);
      return;
    }

    if (top3 === 2) {
      if ((hw1 & 0xfc00) === 0x4000) {
        var aluOp = (hw1 >>> 6) & 0xf;
        var rdA = hw1 & 7;
        var rmA = (hw1 >>> 3) & 7;
        var rVal = this.regs[rdA];
        var mVal = this.regs[rmA];
        if (aluOp === 2 || aluOp === 3 || aluOp === 4 || aluOp === 7) {
          var amt = mVal & 0xff;
          var stM = aluOp === 2 ? 0 : (aluOp === 3 ? 1 : (aluOp === 4 ? 2 : 3));
          var srM = shiftWithCarry(rVal, stM, amt, this.flagC);
          this.regs[rdA] = srM[0];
          if (updateFlags) {
            this.flagN = (srM[0] >>> 31) & 1;
            this.flagZ = srM[0] === 0 ? 1 : 0;
            if (amt > 0) this.flagC = srM[1];
          }
          return;
        }
        if (aluOp === 9) {
          this._execAlu(3, mVal, 0, this.flagC, rdA, updateFlags);
          return;
        }
        if (aluOp === 13) {
          var p = Math.imul(rVal, mVal) >>> 0;
          this.regs[rdA] = p;
          if (updateFlags) {
            this.flagN = (p >>> 31) & 1;
            this.flagZ = p === 0 ? 1 : 0;
          }
          return;
        }
        var mapT1 = [0, 1, -1, -1, -1, 5, 6, -1, 8, -1, 10, 11, 12, -1, 14, 15][aluOp];
        if (mapT1 >= 0) this._execAlu(mapT1, rVal, mVal, this.flagC, rdA, updateFlags);
        return;
      }

      if ((hw1 & 0xfc00) === 0x4400) {
        var hOp = (hw1 >>> 8) & 3;
        var rmH = (hw1 >>> 3) & 0xf;
        var rdH = (((hw1 >>> 7) & 1) << 3) | (hw1 & 7);
        var rmValH = rmH === 15 ? (pc + 4) >>> 0 : this.regs[rmH];
        if (hOp === 3) {
          var linkH = ((hw1 >>> 7) & 1) === 1;
          if (linkH) this.regs[14] = ((pc + 2) | 1) >>> 0;
          this.setBranch(rmValH);
        } else if (hOp === 2) {
          if (rdH === 15) this.setBranch(rmValH | 1);
          else this.regs[rdH] = rmValH;
        } else if (hOp === 1) {
          this._execAlu(10, this.regs[rdH], rmValH, this.flagC, rdH, true);
        } else {
          var rdValH = rdH === 15 ? (pc + 4) >>> 0 : this.regs[rdH];
          var sumH = (rdValH + rmValH) >>> 0;
          if (rdH === 15) this.setBranch(sumH | 1);
          else this.regs[rdH] = sumH;
        }
        return;
      }

      if ((hw1 & 0xf800) === 0x4800) {
        var rtPc = (hw1 >>> 8) & 7;
        var litAddr = (((pc + 4) & ~3) + ((hw1 & 0xff) * 4)) >>> 0;
        this.regs[rtPc] = this.readU32(litAddr);
        return;
      }

      var rOp = (hw1 >>> 9) & 7;
      var rmR = (hw1 >>> 6) & 7;
      var rnR = (hw1 >>> 3) & 7;
      var rtR = hw1 & 7;
      var eaR = (this.regs[rnR] + this.regs[rmR]) >>> 0;
      if (rOp === 0) this.writeU32(eaR, this.regs[rtR]);
      else if (rOp === 1) this.writeU16(eaR, this.regs[rtR]);
      else if (rOp === 2) this.writeU8(eaR, this.regs[rtR]);
      else if (rOp === 3) this.regs[rtR] = signExtend(this.readU8(eaR), 8) >>> 0;
      else if (rOp === 4) this.regs[rtR] = this.readU32(eaR);
      else if (rOp === 5) this.regs[rtR] = this.readU16(eaR);
      else if (rOp === 6) this.regs[rtR] = this.readU8(eaR);
      else this.regs[rtR] = signExtend(this.readU16(eaR), 16) >>> 0;
      return;
    }

    if (top3 === 3) {
      var b3 = (hw1 >>> 12) & 1;
      var l3 = (hw1 >>> 11) & 1;
      var imm5_3 = (hw1 >>> 6) & 0x1f;
      var rn3 = (hw1 >>> 3) & 7;
      var rt3 = hw1 & 7;
      var ea3 = (this.regs[rn3] + (b3 ? imm5_3 : imm5_3 * 4)) >>> 0;
      if (l3) this.regs[rt3] = b3 ? this.readU8(ea3) : this.readU32(ea3);
      else if (b3) this.writeU8(ea3, this.regs[rt3]);
      else this.writeU32(ea3, this.regs[rt3]);
      return;
    }

    if (top3 === 4) {
      if ((hw1 & 0xf000) === 0x8000) {
        var l4 = (hw1 >>> 11) & 1;
        var off4 = ((hw1 >>> 6) & 0x1f) * 2;
        var rn4 = (hw1 >>> 3) & 7;
        var rt4 = hw1 & 7;
        var ea4 = (this.regs[rn4] + off4) >>> 0;
        if (l4) this.regs[rt4] = this.readU16(ea4);
        else this.writeU16(ea4, this.regs[rt4]);
        return;
      }
      var lSp = (hw1 >>> 11) & 1;
      var rtSp = (hw1 >>> 8) & 7;
      var eaSp = (this.regs[13] + (hw1 & 0xff) * 4) >>> 0;
      if (lSp) this.regs[rtSp] = this.readU32(eaSp);
      else this.writeU32(eaSp, this.regs[rtSp]);
      return;
    }

    if (top3 === 5) {
      if ((hw1 & 0xf000) === 0xa000) {
        var spSrc = (hw1 >>> 11) & 1;
        var rd5 = (hw1 >>> 8) & 7;
        var base5 = spSrc ? this.regs[13] : ((pc + 4) & ~3) >>> 0;
        this.regs[rd5] = (base5 + (hw1 & 0xff) * 4) >>> 0;
        return;
      }
      if ((hw1 & 0xff00) === 0xb000) {
        var subSp = (hw1 >>> 7) & 1;
        var immSp = (hw1 & 0x7f) * 4;
        this.regs[13] = subSp ? ((this.regs[13] - immSp) >>> 0) : ((this.regs[13] + immSp) >>> 0);
        return;
      }
      if ((hw1 & 0xf500) === 0xb100) {
        var nonzero = ((hw1 >>> 11) & 1) === 1;
        var iCbz = ((hw1 >>> 9) & 1) << 6 | (((hw1 >>> 3) & 0x1f) << 1);
        var rnCbz = hw1 & 7;
        if (nonzero ? (this.regs[rnCbz] !== 0) : (this.regs[rnCbz] === 0)) {
          this.regs[15] = (pc + 4 + iCbz) >>> 0;
        }
        return;
      }
      if ((hw1 & 0xf600) === 0xb400) {
        var isPop = ((hw1 >>> 11) & 1) === 1;
        var extra = ((hw1 >>> 8) & 1) === 1;
        var mask = (hw1 & 0xff) | (extra ? (1 << (isPop ? 15 : 14)) : 0);
        if (isPop) {
          var spAddr = this.regs[13];
          for (var rP = 0; rP < 16; rP++) {
            if ((mask >>> rP) & 1) {
              var pv = this.readU32(spAddr);
              spAddr = (spAddr + 4) >>> 0;
              if (rP === 15) this.setBranch(pv);
              else this.regs[rP] = pv;
            }
          }
          this.regs[13] = spAddr;
        } else {
          var pcnt = 0;
          for (var rQ = 0; rQ < 16; rQ++) {
            if ((mask >>> rQ) & 1) pcnt++;
          }
          var newSp = (this.regs[13] - pcnt * 4) >>> 0;
          var wAddr = newSp;
          for (var rW = 0; rW < 16; rW++) {
            if ((mask >>> rW) & 1) {
              this.writeU32(wAddr, this.regs[rW]);
              wAddr = (wAddr + 4) >>> 0;
            }
          }
          this.regs[13] = newSp;
        }
        return;
      }
      if ((hw1 & 0xff00) === 0xb200) {
        var exOp = (hw1 >>> 6) & 3;
        var rmEx = (hw1 >>> 3) & 7;
        var rdEx = hw1 & 7;
        var ev = this.regs[rmEx];
        if (exOp === 0) this.regs[rdEx] = signExtend(ev & 0xffff, 16) >>> 0;
        else if (exOp === 1) this.regs[rdEx] = signExtend(ev & 0xff, 8) >>> 0;
        else if (exOp === 2) this.regs[rdEx] = ev & 0xffff;
        else this.regs[rdEx] = ev & 0xff;
      }
      return;
    }

    if (top3 === 6) {
      if ((hw1 & 0xf000) === 0xc000) {
        var l6 = (hw1 >>> 11) & 1;
        var rn6 = (hw1 >>> 8) & 7;
        var mask6 = hw1 & 0xff;
        var a6 = this.regs[rn6];
        for (var r6 = 0; r6 < 8; r6++) {
          if ((mask6 >>> r6) & 1) {
            if (l6) this.regs[r6] = this.readU32(a6);
            else this.writeU32(a6, this.regs[r6]);
            a6 = (a6 + 4) >>> 0;
          }
        }
        if (!(l6 && ((mask6 >>> rn6) & 1))) this.regs[rn6] = a6;
        return;
      }
      var cc6 = (hw1 >>> 8) & 0xf;
      if (cc6 < 14 && this.checkCond(cc6)) {
        var offB = signExtend(hw1 & 0xff, 8) << 1;
        this.regs[15] = (pc + 4 + offB) >>> 0;
      }
      return;
    }

    if ((hw1 & 0xf800) === 0xe000) {
      var offU = signExtend(hw1 & 0x7ff, 11) << 1;
      this.regs[15] = (pc + 4 + offU) >>> 0;
    }
  };

  ArmMicroEmulator.prototype.executeGetParams = function (getParamsVa, bufSize, maxSteps) {
    bufSize = bufSize || 0x600;
    maxSteps = maxSteps || 800;
    this.resetScratch();
    var written = {};
    this.activeWriteHook = function (off, size, value) {
      if (off >= 0 && off < bufSize) {
        written[off] = [size, value >>> 0];
      }
    };

    var clean = (getParamsVa & ~1) >>> 0;
    var localLo = (clean - 0x400) >>> 0;
    var localHi = (clean + 0x900) >>> 0;

    this.regs[0] = PARAMS_ADDR;
    this.regs[13] = (STACK_ADDR + 0x8000) >>> 0;
    this.regs[14] = RET_SENTINEL;
    this.thumb = (getParamsVa & 1) !== 0;
    this.regs[15] = clean;

    for (var step = 0; step < maxSteps; step++) {
      var pc = this.regs[15] >>> 0;
      if (pc === RET_SENTINEL || pc === (RET_SENTINEL & ~1)) break;

      if (pc < localLo || pc > localHi) {
        var r0 = this.regs[0] >>> 0;
        var r1 = this.regs[1] >>> 0;
        var r2 = this.regs[2] >>> 0;
        var sp = this.regs[13] >>> 0;
        var lr = this.regs[14] >>> 0;
        var lrClean = (lr & ~1) >>> 0;
        if (lrClean >= this.baseAddress + 8 && lrClean <= this.endAddress) {
          if (this.readU32((lrClean - 8) >>> 0) === 0xe52de004) {
            this.regs[13] = (sp + 4) >>> 0;
          }
        }
        if (r0 >= PARAMS_ADDR && r0 < PARAMS_ADDR + bufSize && r1 === 0 && r2 >= 0x40 && r2 <= bufSize) {
          var clrOff = r0 - PARAMS_ADDR;
          for (var z = 0; z < r2 && clrOff + z < bufSize; z++) {
            this.paramsBuf[clrOff + z] = 0;
          }
        } else if (r0 >= PARAMS_ADDR && r0 < PARAMS_ADDR + bufSize && this.isReadable(r1) && r2 > 0 && r2 <= bufSize) {
          var dstO = r0 - PARAMS_ADDR;
          for (var c = 0; c < r2 && dstO + c < bufSize; c++) {
            this.paramsBuf[dstO + c] = this.readU8((r1 + c) >>> 0);
          }
        }
        this.setBranch(lr);
        continue;
      }

      if (this.thumb) this.stepThumb();
      else this.stepArm();
    }

    var rawCopy = this.paramsBuf.slice(0, bufSize);
    this.activeWriteHook = null;
    return { raw: rawCopy, written: written };
  };

  ArmMicroEmulator.prototype.executeWithUtilTraps = function (setUtilVa, targetVa, maxSteps, windowRadius) {
    maxSteps = maxSteps || 20000;
    windowRadius = windowRadius || 0x2400;
    this.resetScratch();
    var self = this;
    var events = [];
    var fnLo = 0;
    var fnHi = 0;
    var allowedHelpers = [];
    var pcCounts = new Map();

    function inAllowedCode(addr) {
      if (addr >= fnLo && addr <= fnHi) return true;
      for (var i = 0; i < allowedHelpers.length; i++) {
        if (addr >= allowedHelpers[i][0] && addr <= allowedHelpers[i][1]) return true;
      }
      return false;
    }

    function runFrom(entryVa, stepsLimit) {
      self.thumb = (entryVa & 1) !== 0;
      self.regs[15] = (entryVa & ~1) >>> 0;
      var targetClean = (targetVa & ~1) >>> 0;

      for (var step = 0; step < stepsLimit; step++) {
        var pc = self.regs[15] >>> 0;
        if (pc === RET_SENTINEL || pc === (RET_SENTINEL & ~1)) break;

        if (pc >= TRAP_BASE_ADDR && pc < TRAP_BASE_ADDR + 512) {
          var slotIdx = (pc - TRAP_BASE_ADDR) >>> 2;
          var slotOff = slotIdx * 4;
          var r0 = self.regs[0] >>> 0;
          var r1 = self.regs[1] >>> 0;
          var r2 = self.regs[2] >>> 0;
          var r3 = self.regs[3] >>> 0;
          var lr = self.regs[14] >>> 0;

          var arg0Words = [];
          var arg2Bytes = [];
          var arg1Bytes = [];
          var decodedTable = { version: "NONE", ops: [] };

          if (r1 <= 255 && (r3 === 0 || r3 === 1) && self.isReadable(r2)) {
            for (var b = 0; b < r1; b++) arg2Bytes.push(self.readU8((r2 + b) >>> 0));
          }
          if (r1 >= 1 && r1 <= 32 && (r2 === 0 || r2 === 1) && self.isReadable(r0)) {
            for (var w = 0; w < r1; w++) arg0Words.push(self.readU32((r0 + w * 4) >>> 0));
          }
          if (r2 >= 1 && r2 <= 32 && r0 <= 0xff && self.isReadable(r1)) {
            for (var b2 = 0; b2 < r2; b2++) arg1Bytes.push(self.readU8((r1 + b2) >>> 0));
          }
          if (slotOff === 0x24 || slotOff === 0x48) {
            var opsV3 = tryDecodeSettingTableV3(self.data, self.baseAddress, r0, r1);
            if (opsV3.length >= 2) {
              decodedTable = { version: "V3", ops: opsV3 };
            } else {
              decodedTable = decodeSettingTable(self.data, self.baseAddress, r0, r1);
            }
          } else if (slotOff === 0x28 || slotOff === 0x50) {
            var opsV2 = tryDecodeSettingTableV2(self.data, self.baseAddress, r0, r1);
            if (opsV2.length >= 2) {
              decodedTable = { version: "V2", ops: opsV2 };
            } else {
              decodedTable = decodeSettingTable(self.data, self.baseAddress, r0, r1);
            }
          } else if (self.isReadable(r0) && r1 >= 1 && r1 <= 1024 && (r2 === 0 || r2 === 1 || r2 === 2)) {
            decodedTable = decodeSettingTable(self.data, self.baseAddress, r0, r1);
          }

          events.push({
            kind: "UTIL_SLOT",
            slotOffset: slotOff,
            targetVa: pc,
            callSite: (lr & ~1) >>> 0,
            args: [r0, r1, r2, r3],
            arg0Words: arg0Words,
            arg2Bytes: arg2Bytes,
            arg1Bytes: arg1Bytes,
            tableV3Ops: decodedTable.version === "V3" ? decodedTable.ops : [],
            tableV2Ops: decodedTable.version === "V2" ? decodedTable.ops : [],
            tableOps: decodedTable.ops,
            tableVersion: decodedTable.version
          });
          self.regs[0] = 0;
          self.setBranch(lr);
          continue;
        }

        var cnt = (pcCounts.get(pc) || 0) + 1;
        pcCounts.set(pc, cnt);
        if (cnt > 2000) {
          self.regs[0] = 0;
          self.setBranch(self.regs[14]);
          continue;
        }

        if (!inAllowedCode(pc)) {
          var xr0 = self.regs[0] >>> 0;
          var xr1 = self.regs[1] >>> 0;
          var xr2 = self.regs[2] >>> 0;
          var xr3 = self.regs[3] >>> 0;
          var xsp = self.regs[13] >>> 0;
          var xlr = self.regs[14] >>> 0;

          if (
            xr0 >= self.baseAddress &&
            xr0 < self.endAddress &&
            xr1 >= 1 &&
            xr1 <= 1024 &&
            Math.abs(pc - targetClean) <= windowRadius
          ) {
            allowedHelpers.push([(pc - 0x40) >>> 0, (pc + 0x200) >>> 0]);
            if (self.thumb) self.stepThumb();
            else self.stepArm();
            continue;
          }

          var isMcount = false;
          var xlrClean = (xlr & ~1) >>> 0;
          if (xlrClean >= self.baseAddress + 8 && xlrClean <= self.endAddress) {
            if (self.readU32((xlrClean - 8) >>> 0) === 0xe52de004) {
              self.regs[13] = (xsp + 4) >>> 0;
              isMcount = true;
            }
          }

          if (!isMcount) {
            if (xr1 === UTIL_SRC_ADDR && xr2 >= 0x20 && xr2 <= 0x200) {
              for (var m = 0; m < xr2; m++) self.writeU8((xr0 + m) >>> 0, self.readU8((xr1 + m) >>> 0));
            } else if (
              xr0 >= 0x10000 &&
              xr1 >= 0x10000 &&
              self.isReadable(xr1) &&
              xr2 >= 1 &&
              xr2 <= 0x200 &&
              ((xr0 >= self.baseAddress && xr0 < self.endAddress) ||
                (xr0 >= STACK_ADDR && xr0 < STACK_ADDR + 0x10000) ||
                self.dirtyPages.has((xr0 & 0xffff0000) >>> 0))
            ) {
              for (var k = 0; k < xr2; k++) self.writeU8((xr0 + k) >>> 0, self.readU8((xr1 + k) >>> 0));
            } else {
              events.push({
                kind: "EXTERNAL_CALL",
                slotOffset: null,
                targetVa: pc,
                callSite: xlrClean,
                args: [xr0, xr1, xr2, xr3],
                arg0Words: [],
                arg2Bytes: [],
                arg1Bytes: []
              });
            }
          }
          self.setBranch(xlr);
          continue;
        }

        if (self.thumb) self.stepThumb();
        else self.stepArm();
      }
    }

    if (setUtilVa) {
      var suClean = (setUtilVa & ~1) >>> 0;
      fnLo = (suClean - 0x40) >>> 0;
      fnHi = (suClean + 0x180) >>> 0;
      this.regs[0] = UTIL_SRC_ADDR;
      this.regs[13] = (STACK_ADDR + 0x8000) >>> 0;
      this.regs[14] = RET_SENTINEL;
      runFrom(setUtilVa, 300);
      events = [];
      pcCounts.clear();
    }

    var tClean = (targetVa & ~1) >>> 0;
    fnLo = (tClean - 0x300) >>> 0;
    fnHi = (tClean + 0x400) >>> 0;
    this.regs[13] = (STACK_ADDR + 0x8000) >>> 0;
    this.regs[14] = RET_SENTINEL;
    runFrom(targetVa, maxSteps);
    return events;
  };

  function resolvePointerLiterals(data, baseAddr, fnVa, maxBytes) {
    maxBytes = maxBytes || 0x400;
    var isThumb = (fnVa & 1) !== 0;
    var clean = (fnVa & ~1) >>> 0;
    var startOff = (clean - baseAddr) >>> 0;
    if (startOff >= data.length) return [];
    var endOff = Math.min(data.length, startOff + maxBytes);
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    var vals = [];
    if (isThumb) {
      var pos = startOff;
      var movwVals = new Uint32Array(16);
      while (pos + 2 <= endOff) {
        var hw1 = dv.getUint16(pos, true);
        if ((hw1 & 0xf800) >= 0xe800 && pos + 4 <= endOff) {
          var hw2 = dv.getUint16(pos + 2, true);
          if ((hw1 & 0xfb50) === 0xf240 && (hw2 & 0x8000) === 0) {
            var rd = (hw2 >>> 8) & 0xf;
            var imm16 = ((hw1 & 0xf) << 12) | (((hw1 >>> 10) & 1) << 11) | (((hw2 >>> 12) & 7) << 8) | (hw2 & 0xff);
            if (((hw1 >>> 7) & 1) === 1) {
              var full = ((imm16 << 16) | (movwVals[rd] & 0xffff)) >>> 0;
              vals.push(full);
            } else {
              movwVals[rd] = imm16;
              if (imm16 > 0xff && imm16 <= 0xffffff) vals.push(imm16);
            }
          } else if (hw1 === 0xe8bd && (hw2 & 0x8000) !== 0) {
            break;
          }
          pos += 4;
          continue;
        }
        if ((hw1 & 0xf800) === 0x4800) {
          var curPc = (baseAddr + pos) >>> 0;
          var litAddr = (((curPc + 4) & ~3) + ((hw1 & 0xff) * 4)) >>> 0;
          var litOff = (litAddr - baseAddr) >>> 0;
          if (litOff + 4 <= data.length) {
            var lval = dv.getUint32(litOff, true);
            vals.push(lval);
            var pcrel = (((curPc + 4) & ~3) + lval) >>> 0;
            if (pcrel >= baseAddr && pcrel < baseAddr + data.length) vals.push(pcrel);
            var baserel = (baseAddr + lval) >>> 0;
            if (baserel >= baseAddr && baserel < baseAddr + data.length) vals.push(baserel);
          }
        } else if ((hw1 & 0xfe00) === 0xbc00 && (hw1 & 0x0100) !== 0) {
          break;
        }
        pos += 2;
      }
    } else {
      var movwA = new Uint32Array(16);
      for (var off = startOff; off + 4 <= endOff; off += 4) {
        var w = dv.getUint32(off, true);
        if ((w & 0x0fb00000) === 0x03000000) {
          var rdA = (w >>> 12) & 0xf;
          var i16A = (((w >>> 16) & 0xf) << 12) | (w & 0xfff);
          if (((w >>> 22) & 1) === 1) {
            vals.push(((i16A << 16) | (movwA[rdA] & 0xffff)) >>> 0);
          } else {
            movwA[rdA] = i16A;
            if (i16A > 0xff && i16A <= 0xffffff) vals.push(i16A);
          }
        } else if ((w & 0x0fff0000) === 0x059f0000) {
          var litA = (off + 8 + (w & 0xfff)) >>> 0;
          if (litA + 4 <= data.length) {
            var lvalA = dv.getUint32(litA, true);
            vals.push(lvalA);
            var pcrelA = (baseAddr + off + 8 + lvalA) >>> 0;
            if (pcrelA >= baseAddr && pcrelA < baseAddr + data.length) vals.push(pcrelA);
            var baserelA = (baseAddr + lvalA) >>> 0;
            if (baserelA >= baseAddr && baserelA < baseAddr + data.length) vals.push(baserelA);
          }
        } else if ((w & 0x0fff0fff) === 0x012fff1e || ((w & 0x0fff8000) === 0x08bd8000)) {
          break;
        }
      }
    }
    return vals;
  }

  function decodePackedCmdqWords(words, sourceAddr) {
    var ops = [];
    var idx = 0;
    while (idx < words.length) {
      var w = words[idx] >>> 0;
      var dtype = (w >>> 8) & 0xff;
      if (dtype === 0x05 || dtype === 0x15 || dtype === 0x03 || dtype === 0x13 || dtype === 0x23) {
        var cmd = (w >>> 16) & 0xff;
        var p0 = (w >>> 24) & 0xff;
        ops.push({
          opType: (dtype === 0x05 || dtype === 0x15) ? "DCS_WRITE" : "GENERIC_WRITE",
          cmd: cmd,
          params: (dtype === 0x15 || dtype === 0x23) ? [p0] : [],
          delayValue: null,
          pinOrRail: null,
          pinLevel: null,
          sourceAddress: sourceAddr,
          status: "CONFIRMED",
          rawEncoding: "0x" + w.toString(16).padStart(8, "0")
        });
        idx += 1;
      } else if (dtype === 0x37) {
        var maxRet = (w >>> 16) & 0xffff;
        ops.push({
          opType: "PACKET_CMDQ",
          cmd: 0x37,
          params: [maxRet & 0xff, (maxRet >>> 8) & 0xff],
          delayValue: null,
          pinOrRail: null,
          pinLevel: null,
          sourceAddress: sourceAddr,
          status: "CONFIRMED",
          rawEncoding: "SET_MAX_RETURN_PACKET_SIZE(" + maxRet + ")"
        });
        idx += 1;
      } else if (dtype === 0x39 || dtype === 0x29) {
        var wc = (w >>> 16) & 0xffff;
        var wordCnt = ((wc + 3) / 4) | 0;
        var payload = [];
        for (var j = 1; j <= wordCnt && idx + j < words.length; j++) {
          var pw = words[idx + j] >>> 0;
          payload.push(pw & 0xff, (pw >>> 8) & 0xff, (pw >>> 16) & 0xff, (pw >>> 24) & 0xff);
        }
        payload = payload.slice(0, wc);
        if (payload.length > 0) {
          ops.push({
            opType: dtype === 0x39 ? "DCS_WRITE" : "GENERIC_WRITE",
            cmd: payload[0],
            params: payload.slice(1),
            delayValue: null,
            pinOrRail: null,
            pinLevel: null,
            sourceAddress: sourceAddr,
            status: "CONFIRMED",
            rawEncoding: "0x" + w.toString(16).padStart(8, "0")
          });
        }
        idx += 1 + wordCnt;
      } else {
        ops.push({
          opType: "PACKET_CMDQ",
          cmd: null,
          params: [w & 0xff, (w >>> 8) & 0xff, (w >>> 16) & 0xff, (w >>> 24) & 0xff],
          delayValue: null,
          pinOrRail: null,
          pinLevel: null,
          sourceAddress: sourceAddr,
          status: "INFERRED",
          rawEncoding: "0x" + w.toString(16).padStart(8, "0")
        });
        idx += 1;
      }
    }
    return ops;
  }

  function tryDecodeSettingTableV3(data, baseAddr, tableVa, maxCount) {
    var off = Number(BigInt.asUintN(64, BigInt(tableVa)) - BigInt.asUintN(64, BigInt(baseAddr))) >>> 0;
    if (off < 0 || off + 64 > data.length) return [];
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    maxCount = maxCount || 400;

    var candidateConfigs = [
      { stride: 67, hdr: "byte", paramOff: 3, maxPayload: 64 },
      { stride: 68, hdr: "byte", paramOff: 3, maxPayload: 64 },
      { stride: 68, hdr: "byte_pad", paramOff: 4, maxPayload: 64 },
      { stride: 68, hdr: "short", paramOff: 4, maxPayload: 64 },
      { stride: 72, hdr: "byte", paramOff: 4, maxPayload: 64 },
      { stride: 72, hdr: "short_pad", paramOff: 8, maxPayload: 64 },
      { stride: 76, hdr: "dword", paramOff: 12, maxPayload: 64 },
      { stride: 80, hdr: "dword", paramOff: 12, maxPayload: 64 },
      { stride: 131, hdr: "byte", paramOff: 3, maxPayload: 128 },
      { stride: 132, hdr: "byte", paramOff: 3, maxPayload: 128 },
      { stride: 132, hdr: "short", paramOff: 4, maxPayload: 128 },
      { stride: 136, hdr: "short_pad", paramOff: 8, maxPayload: 128 },
      { stride: 140, hdr: "dword", paramOff: 12, maxPayload: 128 },
      { stride: 144, hdr: "dword", paramOff: 12, maxPayload: 128 }
    ];

    var bestOps = [];
    var bestScore = 0;

    for (var ci = 0; ci < candidateConfigs.length; ci++) {
      var cfg = candidateConfigs[ci];
      var stride = cfg.stride;
      var ops = [];
      var valid = true;
      var foundEnd = false;
      var consecutiveZeroes = 0;
      var strictV3Matches = 0;

      for (var k = 0; k < maxCount; k++) {
        var eOff = off + k * stride;
        if (eOff + stride > data.length) break;

        var id, cmd, cnt;
        if (cfg.hdr === "dword") {
          id = dv.getUint32(eOff, true);
          cmd = dv.getUint32(eOff + 4, true);
          cnt = dv.getUint32(eOff + 8, true);
        } else if (cfg.hdr === "short" || cfg.hdr === "short_pad") {
          id = data[eOff];
          cmd = data[eOff + 1];
          cnt = data[eOff + 2] | (data[eOff + 3] << 8);
        } else {
          id = data[eOff];
          cmd = data[eOff + 1];
          cnt = data[eOff + 2];
        }

        if (id === 0 && cmd === 0 && cnt === 0) {
          consecutiveZeroes++;
          if (consecutiveZeroes >= 2 && ops.length >= 2) {
            foundEnd = true;
            break;
          }
          if (consecutiveZeroes >= 3) {
            valid = false;
            break;
          }
          continue;
        }
        consecutiveZeroes = 0;

        if (id === 0xfffd || id === 0xfd || (id === 0 && (cmd === 0xfd || cmd === 0xfffd))) {
          foundEnd = true;
          strictV3Matches++;
          break;
        } else if (id === 0xff && cmd === 0xff) {
          foundEnd = true;
          strictV3Matches++;
          break;
        } else if (id === 0x00 && (cmd === 0xff || cmd === 0xfe || cmd === 0xfc || cmd === 0xee)) {
          var dval = cnt > 0 ? cnt : (data[eOff + cfg.paramOff] | (data[eOff + cfg.paramOff + 1] << 8));
          ops.push({
            opType: "DELAY_MS",
            cmd: null,
            params: [],
            delayValue: Math.max(1, dval),
            pinOrRail: null,
            pinLevel: null,
            sourceAddress: (tableVa + k * stride) >>> 0,
            status: "CONFIRMED",
            tableVersion: "V3",
            rawEncoding: "V3_DELAY_" + dval + "ms"
          });
          strictV3Matches++;
        } else if (id === 0xfe || id === 0xfffe) {
          var dval2 = Math.max(1, cnt || cmd);
          ops.push({
            opType: "DELAY_MS",
            cmd: null,
            params: [],
            delayValue: dval2,
            pinOrRail: null,
            pinLevel: null,
            sourceAddress: (tableVa + k * stride) >>> 0,
            status: "CONFIRMED",
            tableVersion: "V3",
            rawEncoding: "V3_DELAY"
          });
          strictV3Matches++;
        } else if (id === 0x39 || id === 0x15 || id === 0x05 || id === 0x29 || id === 0x03 || id === 0x13 || id === 0x23) {
          if ((id === 0x05 || id === 0x03) && cnt !== 0) { valid = false; break; }
          if ((id === 0x15 || id === 0x13) && cnt !== 1) { valid = false; break; }
          if (id === 0x23 && cnt !== 2) { valid = false; break; }
          if ((id === 0x39 || id === 0x29) && (cnt < 2 || cnt > cfg.maxPayload)) { valid = false; break; }
          if (cnt <= cfg.maxPayload && eOff + cfg.paramOff + cnt <= data.length) {
            var plist = [];
            for (var p = 0; p < cnt; p++) plist.push(data[eOff + cfg.paramOff + p]);
            ops.push({
              opType: (id === 0x03 || id === 0x13 || id === 0x23 || id === 0x29) ? "GENERIC_WRITE" : "DCS_WRITE",
              cmd: cmd & 0xff,
              params: plist,
              delayValue: null,
              pinOrRail: null,
              pinLevel: null,
              sourceAddress: (tableVa + k * stride) >>> 0,
              status: "CONFIRMED",
              tableVersion: "V3",
              rawEncoding: "V3_0x" + (cmd & 0xff).toString(16)
            });
            strictV3Matches++;
          } else {
            valid = false;
            break;
          }
        } else {
          valid = false;
          break;
        }
      }

      if (valid && (foundEnd || ops.length >= 3) && strictV3Matches >= 2) {
        var dcsCount = ops.filter(function (o) { return o.opType === "DCS_WRITE" || o.opType === "GENERIC_WRITE"; }).length;
        var score = dcsCount * 10 + (foundEnd ? 50 : 0);
        if (score > bestScore) {
          bestScore = score;
          bestOps = ops;
        }
      }
    }

    return bestOps;
  }

  function tryDecodeSettingTableV2(data, baseAddr, tableVa, maxCount) {
    var off = Number(BigInt.asUintN(64, BigInt(tableVa)) - BigInt.asUintN(64, BigInt(baseAddr))) >>> 0;
    if (off < 0 || off + 64 > data.length) return [];
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    maxCount = maxCount || 400;

    var candidateStrides = [72, 136];
    var bestOps = [];
    var bestScore = 0;

    for (var si = 0; si < candidateStrides.length; si++) {
      var stride = candidateStrides[si];
      var ops = [];
      var valid = true;
      var foundEnd = false;
      var consecutiveZeroes = 0;

      for (var k = 0; k < maxCount; k++) {
        var eOff = off + k * stride;
        if (eOff + stride > data.length) break;

        var wCmd = dv.getUint32(eOff, true);
        var bCnt = data[eOff + 4];

        if (wCmd === 0 && bCnt === 0) {
          consecutiveZeroes++;
          if (consecutiveZeroes >= 2 && ops.length >= 2) {
            foundEnd = true;
            break;
          }
          if (consecutiveZeroes >= 3) {
            valid = false;
            break;
          }
          continue;
        }
        consecutiveZeroes = 0;

        if (wCmd === 0xfffd || wCmd === 0xfff || wCmd === 0xfd) {
          foundEnd = true;
          break;
        } else if (wCmd === 0xfffe || wCmd === 0xffe || wCmd === 0xfe) {
          var dval2 = bCnt > 0 && bCnt < 5000 ? bCnt : (dv.getUint32(eOff + 4, true) || 1);
          if (dval2 > 5000) dval2 = 10;
          ops.push({
            opType: "DELAY_MS",
            cmd: null,
            params: [],
            delayValue: dval2,
            pinOrRail: null,
            pinLevel: null,
            sourceAddress: (tableVa + k * stride) >>> 0,
            status: "CONFIRMED",
            tableVersion: "V2",
            rawEncoding: "REGFLAG_DELAY"
          });
        } else if (wCmd === 0xfffc || wCmd === 0xfc) {
          ops.push({
            opType: "RESET_PIN",
            cmd: null,
            params: [],
            delayValue: null,
            pinOrRail: "RESET",
            pinLevel: bCnt & 1,
            sourceAddress: (tableVa + k * stride) >>> 0,
            status: "CONFIRMED",
            tableVersion: "V2",
            rawEncoding: "REGFLAG_RESET_PIN"
          });
        } else if (wCmd <= 0xff) {
          var pLen = Math.min(bCnt, stride - 5);
          var pl4 = [];
          for (var p4 = 0; p4 < pLen; p4++) pl4.push(data[eOff + 5 + p4]);
          ops.push({
            opType: "DCS_WRITE",
            cmd: wCmd,
            params: pl4,
            delayValue: null,
            pinOrRail: null,
            pinLevel: null,
            sourceAddress: (tableVa + k * stride) >>> 0,
            status: "CONFIRMED",
            tableVersion: "V2",
            rawEncoding: "V2_0x" + wCmd.toString(16)
          });
        } else {
          valid = false;
          break;
        }
      }

      if (valid && (foundEnd || ops.length >= 2)) {
        var dcsCount = ops.filter(function (o) { return o.opType === "DCS_WRITE"; }).length;
        var score = dcsCount * 10 + (foundEnd ? 50 : 0);
        if (score > bestScore) {
          bestScore = score;
          bestOps = ops;
        }
      }
    }

    return bestOps;
  }

  function decodeSettingTable(data, baseAddr, tableVa, maxCount) {
    var v3 = tryDecodeSettingTableV3(data, baseAddr, tableVa, maxCount);
    if (v3.length >= 2) return { version: "V3", ops: v3 };
    var v2 = tryDecodeSettingTableV2(data, baseAddr, tableVa, maxCount);
    if (v2.length >= 2) return { version: "V2", ops: v2 };
    var v1 = tryDecodeStaticSettingTable(data, baseAddr, tableVa);
    if (v1.length >= 2) return { version: "V1", ops: v1 };
    return { version: "NONE", ops: [] };
  }

  function tryDecodeStaticSettingTable(data, baseAddr, tableVa) {
    var off = (tableVa - baseAddr) >>> 0;
    if (tableVa < baseAddr || off + 72 > data.length) return [];
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    var strides32 = [72, 132];
    for (var s = 0; s < strides32.length; s++) {
      var stride = strides32[s];
      var cap = stride - 8;
      var ops = [];
      var valid = true;
      var foundEnd = false;
      for (var k = 0; k < 400; k++) {
        var eOff = off + k * stride;
        if (eOff + stride > data.length) break;
        var cmd = dv.getUint32(eOff, true);
        var cnt = data[eOff + 4];
        if (cmd === 0xfff) {
          foundEnd = true;
          ops.push({ opType: "END_OF_TABLE", cmd: 0xfff, params: [], delayValue: null, pinOrRail: null, pinLevel: null, sourceAddress: (tableVa + k * stride) >>> 0, status: "CONFIRMED", rawEncoding: "REGFLAG_END_OF_TABLE" });
          break;
        }
        if (cmd === 0xffe) {
          for (var p = 5; p < stride; p++) {
            if (data[eOff + p] !== 0) { valid = false; break; }
          }
          if (!valid) break;
          ops.push({ opType: "DELAY_MS", cmd: null, params: [], delayValue: cnt, pinOrRail: null, pinLevel: null, sourceAddress: (tableVa + k * stride) >>> 0, status: "CONFIRMED", rawEncoding: "REGFLAG_DELAY" });
        } else if (cmd <= 0xff && cnt <= cap) {
          for (var t = 5 + cnt; t < stride; t++) {
            if (data[eOff + t] !== 0) { valid = false; break; }
          }
          if (!valid) break;
          var plist = [];
          for (var i = 0; i < cnt; i++) plist.push(data[eOff + 5 + i]);
          ops.push({ opType: "DCS_WRITE", cmd: cmd, params: plist, delayValue: null, pinOrRail: null, pinLevel: null, sourceAddress: (tableVa + k * stride) >>> 0, status: "CONFIRMED", rawEncoding: "static_table_" + stride });
        } else {
          valid = false;
          break;
        }
      }
      if (valid && foundEnd && ops.length >= 2) return ops;
    }

    var strides8 = [66, 130];
    for (var s2 = 0; s2 < strides8.length; s2++) {
      var st8 = strides8[s2];
      var cap8 = st8 - 2;
      var ops8 = [];
      var val8 = true;
      var end8 = false;
      for (var k8 = 0; k8 < 400; k8++) {
        var o8 = off + k8 * st8;
        if (o8 + st8 > data.length) break;
        var cmd8 = data[o8];
        var cnt8 = data[o8 + 1];
        if (cmd8 === 0xff && cnt8 === 0) {
          end8 = true;
          ops8.push({ opType: "END_OF_TABLE", cmd: 0xff, params: [], delayValue: null, pinOrRail: null, pinLevel: null, sourceAddress: (tableVa + k8 * st8) >>> 0, status: "CONFIRMED", rawEncoding: "REGFLAG_END_OF_TABLE" });
          break;
        }
        if (cmd8 === 0xfe) {
          ops8.push({ opType: "DELAY_MS", cmd: null, params: [], delayValue: cnt8, pinOrRail: null, pinLevel: null, sourceAddress: (tableVa + k8 * st8) >>> 0, status: "CONFIRMED", rawEncoding: "REGFLAG_DELAY" });
        } else if (cnt8 <= cap8) {
          var p8 = [];
          for (var j8 = 0; j8 < cnt8; j8++) p8.push(data[o8 + 2 + j8]);
          ops8.push({ opType: "DCS_WRITE", cmd: cmd8, params: p8, delayValue: null, pinOrRail: null, pinLevel: null, sourceAddress: (tableVa + k8 * st8) >>> 0, status: "CONFIRMED", rawEncoding: "static_table_" + st8 });
        } else {
          val8 = false;
          break;
        }
      }
      if (val8 && end8 && ops8.length >= 2) return ops8;
    }
    return [];
  }

  function findStaticSettingTable(data, baseAddr, fnVa) {
    var vals = resolvePointerLiterals(data, baseAddr, fnVa, 0x500);
    for (var i = 0; i < vals.length; i++) {
      var v3Ops = tryDecodeSettingTableV3(data, baseAddr, vals[i], 400);
      if (v3Ops.length >= 2) return v3Ops;
      var v2Ops = tryDecodeSettingTableV2(data, baseAddr, vals[i], 400);
      if (v2Ops.length >= 2) return v2Ops;
      var ops = tryDecodeStaticSettingTable(data, baseAddr, vals[i]);
      if (ops.length >= 2) return ops;
    }
    return [];
  }

  function extractExpectedIdsStatic(data, baseAddr, fnVa) {
    var vals = resolvePointerLiterals(data, baseAddr, fnVa, 0x400);
    var out = [];
    for (var i = 0; i < vals.length; i++) {
      var v = vals[i] >>> 0;
      if (v > 0xff && v <= 0xffffff && v < baseAddr) {
        if (out.indexOf(v) === -1) out.push(v);
      }
    }
    return out;
  }

  function analyzeArm64FunctionFlow(data, baseAddr, fnVa, maxBytes) {
    maxBytes = maxBytes || 0x8000;
    var baseLo = BigInt.asUintN(64, BigInt(baseAddr));
    var startOff = Number(BigInt(fnVa) - baseLo);
    if (startOff < 0 || startOff + 4 > data.length) return { calls: [], insnCount: 0, lastVa: fnVa };
    var dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    var endOff = Math.min(data.length, startOff + maxBytes);
    var regs = new Array(32).fill(null);
    regs[31] = 0n;
    var calls = [];
    var adrpPtrs = [];
    var insnCount = 0;
    var maxFwdOff = startOff;
    var lastVa = BigInt(fnVa);

    for (var off = startOff; off + 4 <= endOff && insnCount < 6000; off += 4) {
      insnCount++;
      var w = dv.getUint32(off, true);
      var pc = baseLo + BigInt(off);
      lastVa = pc;

      if (((w & 0x9f000000) >>> 0) === 0x90000000) {
        var rdA = w & 0x1f;
        var immlo = (w >>> 29) & 3;
        var immhi = (w >>> 5) & 0x7ffff;
        var simm = BigInt(signExtend((immhi << 2) | immlo, 21)) << 12n;
        var page = (pc & ~0xfffn) + simm;
        if (rdA !== 31) regs[rdA] = page;
      } else if (((w & 0xff000000) >>> 0) === 0x91000000) {
        var rdI = w & 0x1f;
        var rnI = (w >>> 5) & 0x1f;
        var imm12 = BigInt((w >>> 10) & 0xfff);
        var sh = (w >>> 22) & 1;
        if (sh) imm12 <<= 12n;
        if (rdI !== 31) {
          regs[rdI] = regs[rnI] !== null ? regs[rnI] + imm12 : null;
          if (regs[rdI] !== null) {
            var rel = regs[rdI] - baseLo;
            if (rel >= 0n && rel < BigInt(data.length)) adrpPtrs.push(regs[rdI]);
          }
        }
      } else if ((w & 0x7fe0ffe0) === 0x2a0003e0) {
        var rdM = w & 0x1f;
        var rmM = (w >>> 16) & 0x1f;
        if (rdM !== 31) {
          if (rmM === 31) regs[rdM] = 0n;
          else regs[rdM] = regs[rmM];
        }
      } else if ((w & 0x7f800000) === 0x52800000) {
        var rdZ = w & 0x1f;
        var hwZ = BigInt((w >>> 21) & 3) * 16n;
        var imm16Z = BigInt((w >>> 5) & 0xffff);
        if (rdZ !== 31) regs[rdZ] = imm16Z << hwZ;
      } else if ((w & 0x7f800000) === 0x72800000) {
        var rdK = w & 0x1f;
        var hwK = BigInt((w >>> 21) & 3) * 16n;
        var imm16K = BigInt((w >>> 5) & 0xffff);
        if (rdK !== 31) {
          var cur = regs[rdK] !== null ? regs[rdK] : 0n;
          var maskK = ~(0xffffn << hwK);
          regs[rdK] = (cur & maskK) | (imm16K << hwK);
        }
      } else if (((w & 0xfc000000) >>> 0) === 0x94000000) {
        var bOff = BigInt(signExtend(w & 0x03ffffff, 26)) << 2n;
        var tgt = pc + bOff;
        calls.push({
          address: pc,
          target: tgt,
          args: [regs[0], regs[1], regs[2], regs[3]]
        });
        regs[0] = null;
      } else if ((w & 0xfc000000) === 0x14000000) {
        var bo = signExtend(w & 0x03ffffff, 26) * 4;
        var tOff = off + bo;
        if (tOff >= startOff && tOff < endOff && tOff > maxFwdOff) maxFwdOff = tOff;
        if (off >= maxFwdOff && (tOff < startOff || tOff >= endOff)) break;
      } else if ((w & 0xff000010) === 0x54000000 || (w & 0x7e000000) === 0x34000000 || (w & 0x7e000000) === 0x36000000) {
        var imm19 = (w & 0xff000010) === 0x54000000 ? signExtend((w >>> 5) & 0x7ffff, 19) : ((w & 0x7e000000) === 0x34000000 ? signExtend((w >>> 5) & 0x7ffff, 19) : signExtend((w >>> 5) & 0x3fff, 14));
        var ctOff = off + imm19 * 4;
        if (ctOff >= startOff && ctOff < endOff && ctOff > maxFwdOff) maxFwdOff = ctOff;
      } else if (w === 0xd65f03c0) {
        if (off >= maxFwdOff) break;
      }
    }
    return { calls: calls, adrpPtrs: adrpPtrs, insnCount: insnCount, size: Number(lastVa - BigInt(fnVa)) + 4 };
  }

  var api = {
    PARAMS_ADDR: PARAMS_ADDR,
    UTIL_SRC_ADDR: UTIL_SRC_ADDR,
    TRAP_BASE_ADDR: TRAP_BASE_ADDR,
    STACK_ADDR: STACK_ADDR,
    RET_SENTINEL: RET_SENTINEL,
    ArmMicroEmulator: ArmMicroEmulator,
    resolvePointerLiterals: resolvePointerLiterals,
    decodePackedCmdqWords: decodePackedCmdqWords,
    tryDecodeStaticSettingTable: tryDecodeStaticSettingTable,
    tryDecodeSettingTableV3: tryDecodeSettingTableV3,
    tryDecodeSettingTableV2: tryDecodeSettingTableV2,
    decodeSettingTable: decodeSettingTable,
    findStaticSettingTable: findStaticSettingTable,
    extractExpectedIdsStatic: extractExpectedIdsStatic,
    analyzeArm64FunctionFlow: analyzeArm64FunctionFlow
  };

  if (typeof module !== "undefined" && module.exports) {
    module.exports = api;
  }
  global.ArmEmulator = api;
})(typeof window !== "undefined" ? window : globalThis);
