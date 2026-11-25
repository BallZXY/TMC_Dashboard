// Universal Dynamic Google Sheets Dashboard Engine (รองรับทุก Sheet, ทุก Tab, ทุกจำนวนคอลัมน์และแถวอัตโนมัติ)

function doGet(e) {
  const lock = LockService.getScriptLock();
  lock.tryLock(5000);
  try {
    const ss = SpreadsheetApp.getActiveSpreadsheet();
    const allSheets = ss.getSheets();
    const sheetNames = allSheets.map(s => s.getName());

    const requestedSheet = (e && e.parameter && e.parameter.sheet) ? String(e.parameter.sheet) : "";
    let sheet = requestedSheet ? ss.getSheetByName(requestedSheet) : allSheets[0];
    if (!sheet) sheet = allSheets[0];

    const values = sheet.getDataRange().getDisplayValues();
    if (!values || values.length === 0) {
      return jsonResponse_({
        status: "success",
        sheetName: sheet.getName(),
        availableSheets: sheetNames,
        headers: [],
        data: [],
        updatedAt: new Date().toISOString()
      });
    }

    const rawHeaders = values[0];
    const headers = [];
    const seen = {};
    rawHeaders.forEach((h, idx) => {
      let clean = String(h || "").trim();
      if (!clean) clean = "Column_" + (idx + 1);
      if (seen[clean]) {
        seen[clean] += 1;
        clean = clean + "_" + seen[clean];
      } else {
        seen[clean] = 1;
      }
      headers.push(clean);
    });

    const data = [];
    for (let r = 1; r < values.length; r++) {
      const rowVals = values[r];
      const hasAnyValue = rowVals.some(cell => String(cell || "").trim() !== "");
      if (!hasAnyValue) continue;

      let obj = { _rowIndex: r + 1 };
      headers.forEach((h, cIdx) => {
        obj[h] = rowVals[cIdx] !== undefined ? rowVals[cIdx] : "";
      });
      data.push(obj);
    }

    return jsonResponse_({
      status: "success",
      sheetName: sheet.getName(),
      availableSheets: sheetNames,
      headers: headers,
      data: data,
      updatedAt: new Date().toISOString()
    });
  } catch (err) {
    return jsonResponse_({ status: "error", message: err.toString() });
  } finally {
    lock.releaseLock();
  }
}

function doPost(e) {
  const lock = LockService.getScriptLock();
  lock.waitLock(10000);
  try {
    const ss = SpreadsheetApp.getActiveSpreadsheet();
    const body = JSON.parse(e.postData.contents);
    const action = body.action;
    const sheetName = body.sheetName || "";
    const payload = body.payload || {};

    let sheet = sheetName ? ss.getSheetByName(sheetName) : ss.getSheets()[0];
    if (!sheet) sheet = ss.getSheets()[0];

    const values = sheet.getDataRange().getDisplayValues();
    const rawHeaders = values.length > 0 ? values[0] : [];
    const headers = rawHeaders.map((h, idx) => String(h || "").trim() || ("Column_" + (idx + 1)));

    if (action === "addRow") {
      let targetHeaders = headers;
      if (targetHeaders.length === 0) {
        targetHeaders = Object.keys(payload).filter(k => !k.startsWith("_"));
        sheet.appendRow(targetHeaders);
      }
      const newRow = targetHeaders.map(h => formatCellVal_(payload[h]));
      sheet.appendRow(newRow);
      return jsonResponse_({ status: "ok", action: "addRow" });
    }

    if (action === "updateCell") {
      const rowIndex = Number(payload._rowIndex);
      const colName = String(payload.column || "");
      const colIndex = headers.indexOf(colName);
      if (rowIndex >= 2 && colIndex !== -1) {
        sheet.getRange(rowIndex, colIndex + 1).setValue(formatCellVal_(payload.value));
        return jsonResponse_({ status: "ok", action: "updateCell" });
      }
      return jsonResponse_({ status: "error", message: "Invalid row or column" });
    }

    if (action === "updateRow") {
      const rowIndex = Number(payload._rowIndex);
      if (rowIndex >= 2 && rowIndex <= sheet.getLastRow()) {
        const updatedRow = headers.map(h => formatCellVal_(payload[h]));
        sheet.getRange(rowIndex, 1, 1, headers.length).setValues([updatedRow]);
        return jsonResponse_({ status: "ok", action: "updateRow" });
      }
      return jsonResponse_({ status: "error", message: "Row not found" });
    }

    if (action === "deleteRow") {
      const rowIndex = Number(payload._rowIndex);
      if (rowIndex >= 2 && rowIndex <= sheet.getLastRow()) {
        sheet.deleteRow(rowIndex);
        return jsonResponse_({ status: "ok", action: "deleteRow" });
      }
      return jsonResponse_({ status: "error", message: "Row not found" });
    }

    return jsonResponse_({ status: "error", message: "Unknown action: " + action });
  } catch (err) {
    return jsonResponse_({ status: "error", message: err.toString() });
  } finally {
    lock.releaseLock();
  }
}

function formatCellVal_(val) {
  if (val === undefined || val === null) return "";
  const str = String(val);
  if (/^\d{4}-\d{2}-\d{2}$/.test(str)) return "'" + str;
  return str;
}

function jsonResponse_(obj) {
  return ContentService.createTextOutput(JSON.stringify(obj))
    .setMimeType(ContentService.MimeType.JSON);
}
