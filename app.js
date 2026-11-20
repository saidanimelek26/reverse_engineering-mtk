(function () {
  "use strict";

  var fileInput = document.getElementById("fileInput");
  var dropZone = document.getElementById("dropZone");
  var downloadZipBtn = document.getElementById("downloadZipBtn");
  var downloadReportBtn = document.getElementById("downloadReportBtn");
  var statusText = document.getElementById("statusText");

  var summarySection = document.getElementById("summarySection");
  var outputSection = document.getElementById("outputSection");

  var sumFile = document.getElementById("sumFile");
  var sumFormat = document.getElementById("sumFormat");
  var sumArch = document.getElementById("sumArch");
  var sumBase = document.getElementById("sumBase");
  var sumFw = document.getElementById("sumFw");
  var sumActive = document.getElementById("sumActive");
  var sumBat = document.getElementById("sumBat");
  var sumLkConfig = document.getElementById("sumLkConfig");

  var driverSelect = document.getElementById("driverSelect");
  var driverQuickMeta = document.getElementById("driverQuickMeta");
  var tabBar = document.getElementById("tabBar");

  var reportPre = document.getElementById("reportPre");
  var lkPre = document.getElementById("lkPre");
  var kernelPre = document.getElementById("kernelPre");
  var drmPre = document.getElementById("drmPre");
  var initPre = document.getElementById("initPre");
  var batTable = document.querySelector("#batTable tbody");
  var batteryDtsiPre = document.getElementById("batteryDtsiPre");
  var batteryHdrPre = document.getElementById("batteryHdrPre");
  var batteryRepPre = document.getElementById("batteryRepPre");

  var lkConfigTable = document.querySelector("#lkConfigTable tbody");
  var lkConfigEnvPre = document.getElementById("lkConfigEnvPre");
  var lkConfigHdrPre = document.getElementById("lkConfigHdrPre");
  var lkConfigReportPre = document.getElementById("lkConfigReportPre");

  var sumLkHandoff = document.getElementById("sumLkHandoff");
  var hdProtocol = document.getElementById("hdProtocol");
  var hdDtbo = document.getElementById("hdDtbo");
  var hdDtbAddr = document.getElementById("hdDtbAddr");
  var hdDtboPart = document.getElementById("hdDtboPart");
  var hdFb = document.getElementById("hdFb");
  var hdBat = document.getElementById("hdBat");
  var hdRegs = document.getElementById("hdRegs");
  var lkPartsTable = document.querySelector("#lkPartsTable tbody");
  var lkHandoffReportPre = document.getElementById("lkHandoffReportPre");
  var lkHandoffHdrPre = document.getElementById("lkHandoffHdrPre");
  var lkPartitionsEnvPre = document.getElementById("lkPartitionsEnvPre");

  var fnTbody = document.querySelector("#fnTable tbody");
  var paramTbody = document.querySelector("#paramTable tbody");
  var filesTbody = document.querySelector("#filesTable tbody");

  var currentResult = null;
  var currentZipBlob = null;

  function triggerDownload(blob, fileName) {
    var url = URL.createObjectURL(blob);
    var a = document.createElement("a");
    a.href = url;
    a.download = fileName;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    setTimeout(function () { URL.revokeObjectURL(url); }, 1000);
  }

  function renderSelectedDriver() {
    if (!currentResult || !currentResult.drivers.length) {
      fnTbody.innerHTML = "";
      paramTbody.innerHTML = "";
      lkPre.textContent = "No drivers recovered.";
      kernelPre.textContent = "No drivers recovered.";
      drmPre.textContent = "No drivers recovered.";
      initPre.textContent = "No drivers recovered.";
      driverQuickMeta.textContent = "";
      return;
    }
    var idx = Number(driverSelect.value) || 0;
    var drv = currentResult.drivers[idx] || currentResult.drivers[0];
    var base = currentResult.architecture.baseAddress;
    var clen = currentResult.payload.primaryCode ? currentResult.payload.primaryCode.length : 0;
    var foff = currentResult.payload.codeFileOffset || 0;

    var w = drv.timings.width ? drv.timings.width.value : "?";
    var h = drv.timings.height ? drv.timings.height.value : "?";
    driverQuickMeta.textContent = "struct=" + window.LcmEngine.toHex(drv.structAddress) + " | " + w + "x" + h + " | table=" + (drv.tableVersion || "V2") + " | init_ops=" + drv.initSequence.length;

    fnTbody.innerHTML = "";
    Object.values(drv.functions)
      .sort(function (a, b) { return (a.slotIndex !== null ? a.slotIndex : 999) - (b.slotIndex !== null ? b.slotIndex : 999); })
      .forEach(function (fn) {
        var tr = document.createElement("tr");
        tr.innerHTML =
          "<td class=\"mono\">" + (fn.slotIndex !== null ? fn.slotIndex : "-") + "</td>" +
          "<td class=\"mono\">" + fn.role + "</td>" +
          "<td class=\"mono\">" + window.LcmEngine.toHex(fn.address) + "</td>" +
          "<td class=\"mono\">" + window.LcmEngine.vaToFileOff(fn.address, base, clen, foff) + "</td>" +
          "<td>" + fn.mode + "</td>" +
          "<td class=\"mono\">0x" + fn.size.toString(16) + "</td>";
        fnTbody.appendChild(tr);
      });

    paramTbody.innerHTML = "";
    Object.keys(drv.timings).concat(Object.keys(drv.dsiConfig)).forEach(function (k) {
      var ev = drv.timings[k] || drv.dsiConfig[k];
      var tr = document.createElement("tr");
      tr.innerHTML =
        "<td class=\"mono\">" + k + "</td>" +
        "<td class=\"mono\">" + ev.value + "</td>" +
        "<td class=\"mono\">" + ev.location + "</td>" +
        "<td class=\"mono\">" + window.LcmEngine.toHex(ev.sourceAddress) + "</td>" +
        "<td>" + ev.status + "</td>";
      paramTbody.appendChild(tr);
    });

    lkPre.textContent = drv.generated ? drv.generated.lkC : "";
    kernelPre.textContent = drv.generated ? drv.generated.kernelC : "";
    drmPre.textContent = drv.generated ? (drv.generated.drmC + "\n" + drv.generated.dtsi) : "";
    initPre.textContent = drv.generated ? drv.generated.initTable : "";
  }

  function renderBattery(res) {
    if (!batTable) return;
    batTable.innerHTML = "";
    var b = res.battery;
    if (!b || !b.discovered) {
      if (sumBat) sumBat.textContent = "Not present in input binary (display only / LK image)";
      var tr = document.createElement("tr");
      tr.innerHTML = "<td colspan=\"3\">No battery or fuel gauge subsystem found in this input. Supply a kernel (boot.img, vmlinux, zImage) or DTB file to extract battery parameters.</td>";
      batTable.appendChild(tr);
      if (batteryDtsiPre) batteryDtsiPre.textContent = "No battery parameters discovered.";
      if (batteryHdrPre) batteryHdrPre.textContent = "No battery parameters discovered.";
      if (batteryRepPre) batteryRepPre.textContent = "No battery parameters discovered.";
      return;
    }

    var desc = [];
    if (b.capacityMah) desc.push(b.capacityMah + " mAh");
    if (b.cvVoltageUv) desc.push((b.cvVoltageUv / 1000) + " mV CV");
    if (b.acChargerCurrentUa) desc.push((b.acChargerCurrentUa / 1000) + " mA AC");
    desc.push(b.source);
    if (sumBat) sumBat.textContent = desc.join(" | ");

    var items = [
      ["Nominal Design Capacity", b.capacityMah ? (b.capacityMah + " mAh") : "N/A", "Design capacity of cell"],
      ["Battery Chemistry / Mfr", b.manufacturer || "Standard Li-Ion", "Manufacturer or chemistry identifier"],
      ["Model Name", b.model || "Generic Li-Ion / Polymer", "Cell model name"],
      ["Constant Voltage Limit (CV)", b.cvVoltageUv ? ((b.cvVoltageUv / 1000) + " mV (" + (b.cvVoltageUv / 1000000).toFixed(2) + " V)") : "N/A", "Max charging termination voltage"],
      ["Cutoff / UVLO Shutdown", b.cutoffVoltageUv ? ((b.cutoffVoltageUv / 1000) + " mV (" + (b.cutoffVoltageUv / 1000000).toFixed(2) + " V)") : "N/A", "Low battery shutdown threshold"],
      ["AC Fast Charge Current", b.acChargerCurrentUa ? ((b.acChargerCurrentUa / 1000) + " mA") : "N/A", "Normal wall charger rate"],
      ["AC Input Limit Current", b.acInputCurrentUa ? ((b.acInputCurrentUa / 1000) + " mA") : "N/A", "Max adapter draw limit"],
      ["USB Standard Current", b.usbChargerCurrentUa ? ((b.usbChargerCurrentUa / 1000) + " mA") : "N/A", "Standard USB port rate"],
      ["Pump Express / Turbo Current", b.turboChargerCurrentUa ? ((b.turboChargerCurrentUa / 1000) + " mA") : "N/A", "Fast charging / PE peak rate"],
      ["Non-Standard Charger Current", b.nonStdChargerCurrentUa ? ((b.nonStdChargerCurrentUa / 1000) + " mA") : "N/A", "Legacy or unconfigured charger rate"],
      ["Shunt Sense Resistor (R_FG)", b.senseResistorMohm !== null ? (b.senseResistorMohm + " mOhm") : "N/A", "Coulomb counter sense resistor"],
      ["Meter Internal Resistance", b.meterResistanceMohm !== null ? (b.meterResistanceMohm + " mOhm") : "N/A", "Gauge meter internal resistance"],
      ["Coulomb Counter Tune (CAR)", b.carTuneValue !== null ? String(b.carTuneValue) : "N/A", "Hardware calibration tune factor"],
      ["Temperature Steps", b.temperatures && b.temperatures.length ? ("[" + b.temperatures.join(" C, ") + " C]") : "N/A", "Operating temperature thresholds"],
      ["OCV-SOC Profile Curves", Object.keys(b.ocvSocProfiles || {}).length ? (Object.keys(b.ocvSocProfiles).length + " curve table(s)") : "N/A", "Multi-temperature lookup curves"]
    ];

    items.forEach(function (it) {
      var r = document.createElement("tr");
      r.innerHTML = "<td class=\"mono\">" + it[0] + "</td><td class=\"mono\">" + it[1] + "</td><td>" + it[2] + "</td>";
      batTable.appendChild(r);
    });

    var fDtsi = res.outFiles.find(function (f) { return f.path.indexOf("battery_profile.dtsi") !== -1; });
    var fHdr = res.outFiles.find(function (f) { return f.path.indexOf("cust_battery_meter.h") !== -1; });
    var fRep = res.outFiles.find(function (f) { return f.path.indexOf("BATTERY_REPORT.md") !== -1; });

    if (batteryDtsiPre) batteryDtsiPre.textContent = fDtsi ? String(fDtsi.content) : "No DTSI generated.";
    if (batteryHdrPre) batteryHdrPre.textContent = fHdr ? String(fHdr.content) : "No C Header generated.";
    if (batteryRepPre) batteryRepPre.textContent = fRep ? String(fRep.content) : "No report generated.";
  }

  function renderLkConfig(res) {
    if (!lkConfigTable) return;
    lkConfigTable.innerHTML = "";
    var cfg = res.lkConfig;
    if (!cfg || !cfg.addresses || Object.keys(cfg.addresses).length === 0) {
      if (sumLkConfig) sumLkConfig.textContent = "Not applicable for this target";
      var tr = document.createElement("tr");
      tr.innerHTML = "<td colspan=\"4\">No LK bootloader configuration addresses found. Upload an LK binary (lk.bin, lk.img) or bootloader image to discover BootShim / NovaOS symbols.</td>";
      lkConfigTable.appendChild(tr);
      if (lkConfigEnvPre) lkConfigEnvPre.textContent = "No LK config generated.";
      if (lkConfigHdrPre) lkConfigHdrPre.textContent = "No LK config generated.";
      if (lkConfigReportPre) lkConfigReportPre.textContent = "No LK config report generated.";
      return;
    }

    var keys = Object.keys(cfg.addresses).sort();
    if (sumLkConfig) sumLkConfig.textContent = cfg.chipset + " (" + keys.length + " addresses discovered)";

    keys.forEach(function (k) {
      var r = document.createElement("tr");
      var va = "0x" + cfg.addresses[k].toString(16).toUpperCase().padStart(8, "0");
      var conf = Math.round((cfg.confidence[k] || 0.90) * 100) + "%";
      var ev = cfg.evidence[k] || "Autonomous structural analysis";
      r.innerHTML = "<td class=\"mono\">CONFIG_" + k.toUpperCase() + "_ADDRESS</td><td class=\"mono\">" + va + "</td><td class=\"mono\">" + conf + "</td><td>" + ev + "</td>";
      lkConfigTable.appendChild(r);
    });

    if (lkConfigEnvPre) lkConfigEnvPre.textContent = cfg.env || "";
    if (lkConfigHdrPre) lkConfigHdrPre.textContent = cfg.header || "";
    if (lkConfigReportPre) lkConfigReportPre.textContent = cfg.reportMd || "";
  }

  function renderLkHandoff(res) {
    if (!hdProtocol) return;
    var parts = res.partitions ? res.partitions.list : [];
    var hd = res.lkHandoff;

    if (sumLkHandoff) {
      if (parts.length > 0 || (hd && hd.discovered)) {
        sumLkHandoff.textContent = parts.length + " Partitions Discovered | Protocol: " + (hd ? hd.protocol : "N/A") + " | DTBO Overlay Ready";
      } else {
        sumLkHandoff.textContent = "Not applicable / Not an LK binary";
      }
    }

    if (hd && hd.discovered) {
      hdProtocol.textContent = hd.protocol + " (" + hd.protocolName + ")";
      hdDtbo.textContent = hd.dtboEngine.discovered ? ("Supported (" + hd.dtboEngine.headerMagic + ", " + hd.dtboEngine.overlayFunction + ")") : "N/A";
      hdDtbAddr.textContent = hd.dtbLoadAddress || "0x40000000";
      hdDtboPart.textContent = hd.dtboEngine.discovered ? hd.dtboEngine.targetPartitions.join(", ") : "N/A";
      hdFb.textContent = hd.fbHandoff.discovered ? "Discovered (atag,videolfb base_h/l + vramSize + reserved-memory)" : "N/A";
      hdBat.textContent = hd.batHandoff.discovered ? "Discovered (atag,boot_voltage + fg_swocv + shutdown_time)" : "N/A";
      hdRegs.textContent = hd.regState ? (hd.regState.reg0 + " | " + hd.regState.reg1 + " | " + hd.regState.reg2 + (hd.regState.reg3 ? (" | " + hd.regState.reg3) : "") + " | Mode: " + hd.regState.cpuMode) : "N/A";
      if (lkHandoffReportPre) lkHandoffReportPre.textContent = hd.reportMd || "";
      if (lkHandoffHdrPre) lkHandoffHdrPre.textContent = hd.header || "";
    } else {
      hdProtocol.textContent = "N/A";
      hdDtbo.textContent = "N/A";
      hdDtbAddr.textContent = "N/A";
      hdDtboPart.textContent = "N/A";
      hdFb.textContent = "N/A";
      hdBat.textContent = "N/A";
      hdRegs.textContent = "N/A";
      if (lkHandoffReportPre) lkHandoffReportPre.textContent = "No LK kernel handoff report generated.";
      if (lkHandoffHdrPre) lkHandoffHdrPre.textContent = "No LK kernel handoff header generated.";
    }

    if (lkPartsTable) {
      lkPartsTable.innerHTML = "";
      if (parts.length > 0) {
        parts.forEach(function (p) {
          var tr = document.createElement("tr");
          var tdIdx = document.createElement("td");
          tdIdx.textContent = String(p.index);
          var tdName = document.createElement("td");
          tdName.className = "mono";
          var b = document.createElement("strong");
          b.textContent = p.name;
          tdName.appendChild(b);
          var tdCat = document.createElement("td");
          tdCat.textContent = p.category;
          var tdTgt = document.createElement("td");
          tdTgt.className = "mono";
          tdTgt.textContent = p.target;
          var tdSrc = document.createElement("td");
          tdSrc.className = "mono";
          tdSrc.textContent = p.source;
          tr.appendChild(tdIdx);
          tr.appendChild(tdName);
          tr.appendChild(tdCat);
          tr.appendChild(tdTgt);
          tr.appendChild(tdSrc);
          lkPartsTable.appendChild(tr);
        });
      } else {
        var trEmpty = document.createElement("tr");
        trEmpty.innerHTML = "<td colspan=\"5\">No hardcoded storage partitions discovered in this binary.</td>";
        lkPartsTable.appendChild(trEmpty);
      }
    }

    if (lkPartitionsEnvPre) {
      lkPartitionsEnvPre.textContent = (res.partitions && res.partitions.env) ? res.partitions.env : "No partitions env generated.";
    }
  }

    function renderFileList(outFiles) {
    filesTbody.innerHTML = "";
    outFiles.forEach(function (f) {
      var tr = document.createElement("tr");
      var tdPath = document.createElement("td");
      tdPath.className = "mono";
      tdPath.textContent = f.path;
      var tdLen = document.createElement("td");
      tdLen.className = "mono";
      var byteLen = (f.content instanceof Uint8Array) ? f.content.length : new TextEncoder().encode(String(f.content)).length;
      tdLen.textContent = String(byteLen);
      var tdAct = document.createElement("td");
      var btn = document.createElement("button");
      btn.type = "button";
      btn.textContent = "Download";
      btn.addEventListener("click", function () {
        var b = f.content instanceof Uint8Array
          ? new Blob([f.content], { type: "application/octet-stream" })
          : new Blob([String(f.content)], { type: "text/plain;charset=utf-8" });
        var baseName = f.path.split("/").pop();
        triggerDownload(b, baseName);
      });
      tdAct.appendChild(btn);
      tr.appendChild(tdPath);
      tr.appendChild(tdLen);
      tr.appendChild(tdAct);
      filesTbody.appendChild(tr);
    });
  }

  async function processFile(file) {
    if (!file) return;
    downloadZipBtn.disabled = true;
    downloadReportBtn.disabled = true;
    currentResult = null;
    currentZipBlob = null;
    statusText.textContent = "Analyzing " + file.name + " (" + file.size + " bytes)...";

    try {
      var t0 = performance.now();
      var buf = new Uint8Array(await file.arrayBuffer());
      var res = await window.LcmEngine.analyzeBinaryAndBuildOut(file.name, buf);
      var zb = new window.ZipBuilder();
      res.outFiles.forEach(function (f) { zb.addFile(f.path, f.content); });
      var zipBytes = zb.buildUint8Array();
      var elapsed = ((performance.now() - t0) / 1000).toFixed(2);

      currentResult = res;
      currentZipBlob = new Blob([zipBytes], { type: "application/zip" });

      sumFile.textContent = res.inputName + " (" + res.rawSize + " B)";
      sumFormat.textContent = res.payload.formatType;
      sumArch.textContent = res.architecture.architecture;
      sumBase.textContent = window.LcmEngine.toHex(res.architecture.baseAddress) + " (" + res.architecture.baseStatus + ")";
      sumFw.textContent = res.framework;
      sumActive.textContent = res.activeDriverName ? (res.activeDriverName + " (" + res.drivers.length + " total)") : ("NONE (" + res.drivers.length + " total)");

      driverSelect.innerHTML = "";
      res.drivers.forEach(function (d, i) {
        var opt = document.createElement("option");
        opt.value = String(i);
        opt.textContent = d.name + " [" + (d.tableVersion || "V2") + "]" + (d.isActive ? " [ACTIVE]" : "");
        if (d.isActive) opt.selected = true;
        driverSelect.appendChild(opt);
      });

      reportPre.textContent = res.addressesReportTxt;
      renderSelectedDriver();
      renderBattery(res);
      renderLkConfig(res);
      renderLkHandoff(res);
      renderFileList(res.outFiles);

      summarySection.classList.remove("hidden");
      outputSection.classList.remove("hidden");
      downloadZipBtn.disabled = false;
      downloadReportBtn.disabled = false;
      statusText.textContent = "Done in " + elapsed + "s: found " + res.drivers.length + " driver(s), generated " + res.outFiles.length + " file(s) inside out.zip (" + Math.round(zipBytes.length / 1024) + " KB).";
    } catch (err) {
      statusText.textContent = "Error: " + (err && err.message ? err.message : String(err));
    }
  }

  fileInput.addEventListener("change", function () {
    if (fileInput.files && fileInput.files[0]) processFile(fileInput.files[0]);
  });

  dropZone.addEventListener("dragover", function (e) {
    e.preventDefault();
    dropZone.classList.add("dragover");
  });

  dropZone.addEventListener("dragleave", function () {
    dropZone.classList.remove("dragover");
  });

  dropZone.addEventListener("drop", function (e) {
    e.preventDefault();
    dropZone.classList.remove("dragover");
    if (e.dataTransfer && e.dataTransfer.files && e.dataTransfer.files[0]) {
      processFile(e.dataTransfer.files[0]);
    }
  });

  driverSelect.addEventListener("change", renderSelectedDriver);

  downloadZipBtn.addEventListener("click", function () {
    if (!currentZipBlob || !currentResult) return;
    var stem = currentResult.inputName.replace(/\.[^.]+$/, "");
    triggerDownload(currentZipBlob, stem + "_out.zip");
  });

  downloadReportBtn.addEventListener("click", function () {
    if (!currentResult) return;
    triggerDownload(new Blob([currentResult.addressesReportTxt], { type: "text/plain;charset=utf-8" }), "ADDRESSES_REPORT.txt");
  });

  tabBar.addEventListener("click", function (e) {
    var btn = e.target;
    if (!btn.classList.contains("tab")) return;
    var target = btn.getAttribute("data-tab");
    document.querySelectorAll(".tab").forEach(function (t) { t.classList.remove("active"); });
    btn.classList.add("active");
    document.querySelectorAll(".tab-pane").forEach(function (p) { p.classList.add("hidden"); });
    document.getElementById("tab-" + target).classList.remove("hidden");
  });

  document.querySelectorAll(".copy-btn").forEach(function (btn) {
    btn.addEventListener("click", function () {
      var id = btn.getAttribute("data-copy");
      var el = document.getElementById(id);
      if (el && navigator.clipboard) {
        navigator.clipboard.writeText(el.textContent);
        btn.textContent = "Copied";
        setTimeout(function () { btn.textContent = "Copy"; }, 1200);
      }
    });
  });
})();
