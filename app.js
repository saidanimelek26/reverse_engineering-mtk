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

  var driverSelect = document.getElementById("driverSelect");
  var driverQuickMeta = document.getElementById("driverQuickMeta");
  var tabBar = document.getElementById("tabBar");

  var reportPre = document.getElementById("reportPre");
  var lkPre = document.getElementById("lkPre");
  var kernelPre = document.getElementById("kernelPre");
  var drmPre = document.getElementById("drmPre");
  var initPre = document.getElementById("initPre");

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
    driverQuickMeta.textContent = "struct=" + window.LcmEngine.toHex(drv.structAddress) + " | " + w + "x" + h + " | init_ops=" + drv.initSequence.length;

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
        opt.textContent = d.name + (d.isActive ? " [ACTIVE]" : "");
        if (d.isActive) opt.selected = true;
        driverSelect.appendChild(opt);
      });

      reportPre.textContent = res.addressesReportTxt;
      renderSelectedDriver();
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
