#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use std::{
    collections::HashMap,
    fs,
    io::Read,
    path::{Path, PathBuf},
    process::Command,
};
use tauri::{AppHandle, Manager, WebviewUrl, WebviewWindowBuilder};

// Runs inside the lookup window on orbispatches.com / prosperopatches.com only.
// It waits for the page to render (the sites are JavaScript-driven), reads the game
// name and the patch versions from the DOM/network payloads, and hands the result back
// through the URL fragment (#psa=...), which Rust reads.
const INIT_JS: &str = r#"
(function () {
  if (window.top !== window) return;
  if (!/(^|\.)(orbispatches|prosperopatches)\.com$/.test(location.hostname)) return;
  var t0 = Date.now(), done = false, reqs = [], captured = [], reqLog = [], nudged = false;
  var boots = 0, lastErr = '';
  function noteErr(x) { x = String(x).slice(0, 160); if (lastErr.indexOf(x.slice(0, 50)) < 0) lastErr = (lastErr ? lastErr + ' | ' : '') + x; lastErr = lastErr.slice(0, 420); }
  try {
    var st0 = +sessionStorage.getItem('psa_t0') || 0;
    if (!st0 || Date.now() - st0 > 120000) { st0 = Date.now(); sessionStorage.setItem('psa_t0', String(st0)); sessionStorage.setItem('psa_boots', '0'); }
    boots = (+sessionStorage.getItem('psa_boots') || 0) + 1; sessionStorage.setItem('psa_boots', String(boots)); t0 = st0;
  } catch (e) {}
  var DIAG = !!window.__PSA_DIAG, htmlCands = [], directLog = [], directTried = false, tvSnip = [];
  function T() { return Math.round((Date.now() - t0) / 100) / 10 + 's'; } // set by the app for the "test one Title ID" button: slower, full diagnostics
  var tid = ((location.pathname.match(/(CUSA|PPSA)\d{5}/i) || [''])[0]).toUpperCase();
  function put(o) {
    try {
      var s = encodeURIComponent(JSON.stringify(o));
      var d = o.debug ? String(o.debug) : '';
      while (s.length > 22000 && d.length > 400) { d = d.slice(0, Math.floor(d.length * 0.7)); o.debug = d + ' ...[cut]'; s = encodeURIComponent(JSON.stringify(o)); }
      location.hash = 'psa=' + s;
    } catch (e) { noteErr('put: ' + e); }
  }
  function keep(url, text, meta) {
    meta = meta || {};
    try { reqLog.push({ m: meta.m || '', u: String(url).slice(0, 120), s: meta.s || 0, n: text ? String(text).length : 0, t: Date.now() - t0, b: meta.b ? String(meta.b).slice(0, 200) : '' }); } catch (e) {}
    try { reqs.push(String(url).slice(0, 100)); } catch (e) {}
    if (/loadpatches/i.test(String(url)) && text) captured.push({ url: String(url).slice(0, 100), text: String(text).slice(0, 30000) });
  }
  function patchCaptured() { return captured.some(function (c) { return /loadpatches/i.test(c.url); }); }
  var of = window.fetch, rawFetch = window.fetch ? window.fetch.bind(window) : null;
  if (of) window.fetch = function (input, init) {
    var url = (input && input.url) || input, method = (init && init.method) || (input && input.method) || 'GET', body = init && typeof init.body === 'string' ? init.body : '';
    var p = of.apply(this, arguments);
    try { p.then(function (r) { try { var st = r.status; r.clone().text().then(function (tx) { keep(url, tx, { m: method, s: st, b: body }); }, function () { keep(url, '', { m: method, s: st, b: body }); }); } catch (e) {} }, function () {}); } catch (e) {}
    return p;
  };
  var ox = XMLHttpRequest.prototype.open, os = XMLHttpRequest.prototype.send;
  XMLHttpRequest.prototype.open = function (m, u) { this.__psa = u; this.__psm = m; return ox.apply(this, arguments); };
  XMLHttpRequest.prototype.send = function (body) {
    var x = this, b = typeof body === 'string' ? body : '';
    x.addEventListener('loadend', function () { try { keep(x.__psa, (x.responseType === '' || x.responseType === 'text') ? x.responseText : '', { m: x.__psm, s: x.status, b: b }); } catch (e) {} });
    return os.apply(this, arguments);
  };
  function versionsFrom(text) {
    var out = [];
    function walk(o, key) {
      if (o == null) return;
      if (typeof o === 'string' || typeof o === 'number') {
        var s = String(o);
        // PS4 site: "version":"01.57"; PS5 site: "content_ver":"01.002.001" (three parts)
        if (/^(app_?ver(sion)?|patch_?ver(sion)?|content_?ver(sion)?|version|ver)$/i.test(key || '') && /^\d{1,3}(\.\d{1,3}){1,3}$/.test(s)) out.push(s);
        return;
      }
      if (Array.isArray(o)) { o.forEach(function (x) { walk(x, key); }); return; }
      if (typeof o === 'object') for (var k in o) walk(o[k], k);
    }
    try { walk(JSON.parse(text)); } catch (e) {}
    return out;
  }
  function uniq(a) { return a.filter(function (v, i) { return a.indexOf(v) === i; }); }
  function cleanName(s) {
    s = String(s || '').replace(/\s+/g, ' ').trim();
    if (tid) s = s.split(tid).join('');
    s = s.replace(/(ORBIS|PROSPERO)\s*Patches/ig, '');
    s = s.replace(/(ORBIS|PROSPERO)Patches?\.?com/ig, '');
    s = s.replace(/\bPatch Installer\b/ig, '');
    s = s.replace(/^[\s\-|–—:()\[\]]+|[\s\-|–—:()\[\]]+$/g, '');
    return s.trim();
  }
  // whole-string junk only (a real game may start with "Home" or "Patches")
  var BAD = /^(404|not found|page not found|just a moment|attention required)\b/i, BADEXACT = /^(home|patches|patch installer|error)$/i;
  function addCandidate(list, src, v, weight) {
    v = cleanName(v);
    if (!v || v.length < 2 || v.length > 160 || BAD.test(v) || BADEXACT.test(v)) return;
    list.push({ src: src, name: v, weight: weight || 0 });
  }
  function walkStrings(o, cb, key) {
    if (o == null) return;
    if (typeof o === 'string' || typeof o === 'number') { cb(String(o), key || ''); return; }
    if (Array.isArray(o)) { o.forEach(function (x) { walkStrings(x, cb, key); }); return; }
    if (typeof o === 'object') for (var k in o) walkStrings(o[k], cb, k);
  }
  function parseJsonText(text, src, weight, out) {
    try {
      var o = JSON.parse(text);
      walkStrings(o, function (s, key) {
        if (/^(name|title|headline|game|gamename|displayname|alternateName)$/i.test(key) && /[A-Z]{4}\d{5}/i.test(tid + ' ' + s)) {
          addCandidate(out, src + ':' + key, s, weight + 2);
        } else if (/^(name|title|headline|game|gamename|displayname|alternateName)$/i.test(key)) {
          addCandidate(out, src + ':' + key, s, weight + 1);
        }
      });
    } catch (e) {}
  }
  function candidates(doc) {
    doc = doc || document;
    var c = [];
    function add(src, v, weight) { addCandidate(c, src, v, weight); }
    var selectors = [
      ['h3.h3-title, .h3-title', 30],
      ['h1', 28],
      ['h2', 24],
      ['.game-title', 25],
      ['.page-title', 20],
      ['[class*="title"]', 10]
    ];
    selectors.forEach(function (pair) {
      var nodes = doc.querySelectorAll(pair[0]);
      for (var i = 0; i < nodes.length && i < 6; i++) add(pair[0], nodes[i].textContent, pair[1] - i);
    });
    var og = doc.querySelector('meta[property="og:title"]'); if (og) add('og:title', og.getAttribute('content'), 18);
    var tw = doc.querySelector('meta[name="twitter:title"]'); if (tw) add('twitter:title', tw.getAttribute('content'), 16);
    add('title', doc.title, 4);
    var ld = doc.querySelectorAll('script[type="application/ld+json"]');
    for (var i = 0; i < ld.length && i < 6; i++) parseJsonText(ld[i].textContent || '', 'ld+json[' + i + ']', 22 - i, c);
    var next = doc.getElementById('__NEXT_DATA__'); if (next) parseJsonText(next.textContent || '', '__NEXT_DATA__', 24, c);
    return c.sort(function (a, b) {
      if (b.weight !== a.weight) return b.weight - a.weight;
      return a.name.length - b.name.length;
    });
  }
  function around(re, n, w) { return aroundIn((document.documentElement && document.documentElement.outerHTML) || '', re, n, w); }
  function aroundIn(h, re, n, w) {
    var out = [], m, rx = new RegExp(re.source, 'ig'), cnt = 0;
    while ((m = rx.exec(h)) && cnt < n) { out.push(h.slice(Math.max(0, m.index - w / 2), m.index + w / 2).replace(/\s+/g, ' ')); cnt++; rx.lastIndex = m.index + w; }
    return out;
  }
  function diag(cands, vs, full) {
    var d = 'url=' + location.pathname + ' title=' + document.title + '\nrequests=' + JSON.stringify(reqs.slice(-12)) +
      '\ncandidates=' + JSON.stringify(cands.slice(0, 8)) + '\nversions=' + JSON.stringify(vs) + '\ndirect=' + JSON.stringify(directLog);
    if (captured.length) d += '\ncaptured=' + captured.slice(0, 2).map(function (c) { return c.url + ' => ' + c.text.slice(0, full ? 1500 : 200); }).join(' | ');
    if (full) {
      var perf = [];
      try { perf = performance.getEntriesByType('resource').filter(function (e) { return !/^(img|css|link)$/.test(e.initiatorType) && !/\.(png|jpe?g|gif|svg|webp|woff2?|css|ico)(\?|$)/i.test(e.name); }).slice(-20).map(function (e) { return e.initiatorType + ':' + e.name.slice(0, 90); }); } catch (e) {}
      var ifr = [].map.call(document.querySelectorAll('iframe'), function (f) { return (f.src || '').slice(0, 80); });
      var scr = [].map.call(document.querySelectorAll('script[src]'), function (x) { return x.src.slice(0, 80); }).slice(0, 12);
      d += '\nreqLog=' + JSON.stringify(reqLog.slice(-15)).slice(0, 1600) + '\nperf=' + JSON.stringify(perf).slice(0, 1000) +
        '\niframes=' + JSON.stringify(ifr) + '\nscripts=' + JSON.stringify(scr) +
        '\ntext=' + ((document.body && document.body.innerText) || '').slice(0, 1200).replace(/\s+/g, ' ') +
        '\nhtmlLen=' + ((document.body && document.body.innerHTML) || '').length + '\nhex64=' + JSON.stringify(aroundIn((document.documentElement && document.documentElement.outerHTML) || '', /[a-f0-9]{64}/i, 4, 200)) + '\ntitleview=' + JSON.stringify(tvSnip) + '\naround=' + JSON.stringify(around(/patch|version|changelog/i, 2, 400));
    }
    return d.slice(0, full ? 10000 : 700);
  }
  // The page itself asks for the patch list ~20 s after load (ads/consent scripts go first). We make the same
  // request right away: read the page HTML, find the per-title key (64 hex chars), POST {titleid, key}.
  function directFetch() {
    if (!tid || directTried || !rawFetch) { directLog.push('not started: tid=' + tid + ' rawFetch=' + !!rawFetch); return; }
    directTried = true; directLog.push('start@' + T());
    try {
      rawFetch(location.pathname, { credentials: 'same-origin' }).then(function (r) { return r.text(); }).then(function (html) {
        try { htmlCands = candidates(new DOMParser().parseFromString(html, 'text/html')); } catch (e) {}
        var keys = uniq((html.match(/\b[a-f0-9]{64}\b/gi) || []).map(function (k) { return k.toLowerCase(); })).slice(0, 4);
        directLog.push('html@' + T() + ' keys=' + keys.length + ' len=' + html.length);
        (function next(i) {
          if (i >= keys.length) return;
          var st = 0;
          rawFetch('/api/internal/loadpatches', { method: 'POST', credentials: 'same-origin', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ titleid: tid, key: keys[i] }) })
            .then(function (r) { st = r.status; return r.text(); }).then(function (tx) {
              var j = null; try { j = JSON.parse(tx); } catch (e) {}
              var good = !!(j && j.success && Array.isArray(j.patches));
              directLog.push('key' + i + '@' + T() + ':' + (good ? 'ok(' + j.patches.length + ')' : 'HTTP ' + st + ' ' + String(tx).slice(0, 80)));
              if (good) keep('/api/internal/loadpatches#direct', tx, { m: 'POST', s: 200, b: 'direct' }); else next(i + 1);
            }, function (e) { directLog.push('key' + i + ':error ' + String(e).slice(0, 60)); next(i + 1); });
        })(0);
      }, function (e) { directLog.push('html fetch failed: ' + String(e).slice(0, 60)); });
    } catch (e) { directLog.push('direct error: ' + String(e).slice(0, 60)); }
    // diagnostics only: how does the site's own script decide when/how to ask for the patch list?
    if (DIAG) try { rawFetch('/assets/js/titleview.js').then(function (r) { return r.text(); }).then(function (tx) { tvSnip = aroundIn(tx, /loadpatches|keyset|data-key|turnstile/i, 4, 700); }, function () {}); } catch (e) {}
  }
  function isChall() {
    var tx = ((document.body && document.body.innerText) || '').slice(0, 3000);
    return /just a moment|verify you are human|checking your browser|cf-turnstile/i.test(document.title + ' ' + tx) || !!document.querySelector('iframe[src*="challenges.cloudflare.com"]');
  }
  function safeDiag(c, v, f) { var head = 'boots=' + boots + ' err=' + lastErr + '\n'; try { return head + diag(c, v, f); } catch (e) { return head + 'diag failed: ' + String(e).slice(0, 120); } }
  function scan() {
    if (done) return;
    try { scanInner(); } catch (e) { noteErr('scan: ' + (e && e.message || e)); setTimeout(scan, 500); }
  }
  function scanInner() {
    if (done) return;
    var el = Date.now() - t0;
    var txt = ((document.body && document.body.innerText) || '').slice(0, 3000);
    var chall = /just a moment|verify you are human|checking your browser|cf-turnstile/i.test(document.title + ' ' + txt) ||
      !!document.querySelector('iframe[src*="challenges.cloudflare.com"]');
    if (chall && el > 3000) put({ status: 'challenge' });
    var vs = [];
    captured.forEach(function (c) { vs = vs.concat(versionsFrom(c.text)); });
    vs = uniq(vs);
    var cands = candidates().concat(htmlCands).sort(function (a, b) { return b.weight - a.weight || a.name.length - b.name.length; });
    // some pages only start loading the patch list after a scroll: nudge once
    if (!nudged && el > 3000 && !patchCaptured()) { nudged = true; try { window.scrollTo(0, (document.body || {}).scrollHeight || 0); window.dispatchEvent(new Event('scroll')); setTimeout(function () { window.scrollTo(0, 0); }, 300); } catch (e) {} }
    var need = patchCaptured() || el > 35000;
    if (cands.length && !chall && need) {
      done = true;
      put({ status: 'ok', name: cands[0].name, versions: vs, noVersions: vs.length === 0, debug: safeDiag(cands, vs, DIAG || vs.length === 0) });
      return;
    }
    if (el > 45000 && !chall) {
      done = true;
      put({ status: 'notfound', debug: safeDiag(cands, vs, true) });
      return;
    }
    setTimeout(scan, 400);
  }
  function start() { put({ status: 'boot' }); scan(); }
  directFetch();
  // Whatever happens, answer before the app's own timeout (50 s). Skipped while a human check is on screen.
  (function arm() {
    setTimeout(function () {
      if (done) return;
      var chall = false; try { chall = isChall(); } catch (e) {}
      if (chall) { arm(); return; }
      done = true;
      var cands = [], vs = [];
      try { cands = candidates().concat(htmlCands); captured.forEach(function (c) { vs = vs.concat(versionsFrom(c.text)); }); vs = uniq(vs); } catch (e) { noteErr('watchdog: ' + e); }
      put({ status: cands.length ? 'ok' : 'notfound', name: cands.length ? cands[0].name : undefined, versions: vs, noVersions: vs.length === 0,
        debug: 'WATCHDOG readyState=' + document.readyState + ' ' + safeDiag(cands, vs, true) });
    }, Math.max(1000, 38000 - (Date.now() - t0)));
  })();
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start); else start();
})();
"#;
#[derive(Serialize, Deserialize, Default, Clone)]
#[serde(default)]
struct LookupResult {
    status: String,
    name: Option<String>,
    versions: Vec<String>,
    debug: Option<String>,
}

fn read_report(win: &tauri::WebviewWindow, tid: &str) -> Option<LookupResult> {
    let url = win.url().ok()?;
    // ignore the previous title's page while the new one is still loading
    if !url.path().to_uppercase().ends_with(tid) {
        return None;
    }
    let enc = url.fragment()?.strip_prefix("psa=")?;
    let json = percent_encoding::percent_decode_str(enc).decode_utf8().ok()?;
    serde_json::from_str::<LookupResult>(&json).ok()
}

#[tauri::command]
async fn lookup_title(app: AppHandle, tid: String, visible: Option<bool>, diag: Option<bool>) -> Result<LookupResult, String> {
    let visible = visible.unwrap_or(false);
    let init_script = format!("window.__PSA_DIAG={};\n{}", diag.unwrap_or(false), INIT_JS);
    let tid = tid.to_uppercase();
    let valid = tid.is_ascii()
        && tid.len() == 9
        && (tid.starts_with("CUSA") || tid.starts_with("PPSA"))
        && tid[4..].chars().all(|c| c.is_ascii_digit());
    if !valid {
        return Err("invalid title id".into());
    }

    let host = if tid.starts_with("CUSA") { "orbispatches.com" } else { "prosperopatches.com" };
    let target = format!("https://{}/{}", host, tid);
    let parsed = tauri::Url::parse(&target).map_err(|e| e.to_string())?;
    let label = format!("lookup-{}-{}", tid, SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_millis());

    let win = WebviewWindowBuilder::new(&app, &label, WebviewUrl::External(parsed))
        .title("بررسی آنلاین — اگر تأیید انسانی خواست، یک‌بار انجامش دهید")
        .inner_size(900.0, 700.0)
        .visible(visible)
        .initialization_script(init_script.clone())
        .build()
        .map_err(|e| e.to_string())?;

    let start = Instant::now();
    let mut limit = Duration::from_secs(35);
    let mut challenge_seen = false;
    let mut shown_by_us = false; // opened only to let the user pass a check -> hide again afterwards
    let mut saw_boot = false; // did our script ever run + could we read its message back?
    loop {
        tokio::time::sleep(Duration::from_millis(400)).await;
        if let Some(rep) = read_report(&win, &tid) {
            match rep.status.as_str() {
                "boot" => saw_boot = true,
                "challenge" => {
                    saw_boot = true;
                    if !challenge_seen {
                        challenge_seen = true;
                        if !visible {
                            let _ = win.show();
                            let _ = win.set_focus();
                            shown_by_us = true;
                        }
                        limit = start.elapsed() + Duration::from_secs(240);
                    }
                }
                _ => {
                    if shown_by_us { let _ = win.hide(); }
                    let _ = win.close();
                    return Ok(rep);
                }
            }
        }
        if start.elapsed() > limit {
            if shown_by_us { let _ = win.hide(); }
            let last_url = win.url().map(|u| u.to_string()).unwrap_or_default();
            let note = if saw_boot {
                "script_ran=true (page loaded, but no final result before the time limit)"
            } else {
                "script_ran=false (our script never reported back: blocked page, no navigation, or the result channel does not work)"
            };
            let _ = win.close();
            return Ok(LookupResult {
                status: "timeout".into(),
                debug: Some(format!("{note}; last_url={}", &last_url.chars().take(160).collect::<String>())),
                ..Default::default()
            });
        }
    }
}
#[tauri::command]
fn open_url(url: String) -> Result<(), String> {
    if !(url.starts_with("https://orbispatches.com/") || url.starts_with("https://prosperopatches.com/")) {
        return Err("blocked".into());
    }
    #[cfg(target_os = "windows")]
    let r = std::process::Command::new("explorer").arg(&url).spawn();
    #[cfg(target_os = "macos")]
    let r = std::process::Command::new("open").arg(&url).spawn();
    #[cfg(all(unix, not(target_os = "macos")))]
    let r = std::process::Command::new("xdg-open").arg(&url).spawn();
    r.map(|_| ()).map_err(|e| e.to_string())
}

#[tauri::command]
fn save_csv(app: AppHandle, filename: String, contents: String) -> Result<String, String> {
    let dir = app.path().download_dir().map_err(|e| e.to_string())?;
    let safe: String = filename
        .chars()
        .filter(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '-' || *c == '.')
        .collect();
    let path = dir.join(if safe.is_empty() { "export.csv".to_string() } else { safe });
    std::fs::write(&path, contents.as_bytes()).map_err(|e| e.to_string())?;
    Ok(path.display().to_string())
}


#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ArchiveFile {
    path: String,
    relative_path: String,
    name: String,
    size: u64,
    mtime_ms: u64,
    cid: Option<String>,
    file_type: Option<String>,
}

/// On Windows `canonicalize` returns verbatim paths (`\\?\C:\...`). Shell APIs such as
/// WScript.Shell and explorer.exe handle those badly, so strip the prefix.
fn plain_path(p: &Path) -> PathBuf {
    let s = p.to_string_lossy();
    if let Some(rest) = s.strip_prefix(r"\\?\UNC\") {
        return PathBuf::from(format!(r"\\{}", rest));
    }
    if let Some(rest) = s.strip_prefix(r"\\?\") {
        return PathBuf::from(rest.to_string());
    }
    p.to_path_buf()
}

fn supported_archive(path: &Path) -> bool {
    path.extension()
        .and_then(|v| v.to_str())
        .map(|v| matches!(v.to_ascii_lowercase().as_str(), "pkg" | "zip" | "rar" | "7z" | "iso" | "bin" | "exfat"))
        .unwrap_or(false)
}

fn inspect_pkg(path: &Path) -> (Option<String>, Option<String>) {
    if !path.extension().and_then(|v| v.to_str()).map(|v| v.eq_ignore_ascii_case("pkg")).unwrap_or(false) {
        return (None, None);
    }
    let mut file = match fs::File::open(path) {
        Ok(f) => f,
        Err(_) => return (None, None),
    };
    let mut bytes = [0u8; 0x80];
    if file.read_exact(&mut bytes).is_err() || u32::from_be_bytes(bytes[0..4].try_into().unwrap()) != 0x7F434E54 {
        return (None, None);
    }

    let cid: String = bytes[0x40..0x64]
        .iter()
        .copied()
        .filter(|b| *b != 0)
        .map(char::from)
        .collect();
    let cid = if cid.is_empty() { None } else { Some(cid) };
    let kind = u32::from_be_bytes(bytes[0x74..0x78].try_into().unwrap());
    let file_type = match kind {
        0x1A => Some("Base Game".to_string()),
        0x1B | 0x1C => Some("DLC/Add-on".to_string()),
        0x1D => Some("Update".to_string()),
        _ => None,
    };
    (cid, file_type)
}

fn collect_archive_files(root: &Path, dir: &Path, output: &mut Vec<ArchiveFile>) -> Result<(), String> {
    let entries = fs::read_dir(dir).map_err(|e| format!("خواندن پوشه ممکن نشد: {} ({e})", dir.display()))?;
    for entry in entries {
        let entry = match entry {
            Ok(v) => v,
            Err(_) => continue,
        };
        let path = entry.path();
        let ft = match entry.file_type() {
            Ok(v) => v,
            Err(_) => continue,
        };
        // Do not follow symlinks: this avoids loops and keeps scanning within the selected folder.
        if ft.is_symlink() {
            continue;
        }
        if ft.is_dir() {
            if entry.file_name().to_string_lossy().eq_ignore_ascii_case("PS Archive Shortcuts") {
                continue;
            }
            let _ = collect_archive_files(root, &path, output);
            continue;
        }
        if !ft.is_file() || !supported_archive(&path) {
            continue;
        }
        let metadata = match entry.metadata() {
            Ok(v) => v,
            Err(_) => continue,
        };
        let relative = path.strip_prefix(root).unwrap_or(&path);
        let (cid, file_type) = inspect_pkg(&path);
        let mtime_ms = metadata.modified().unwrap_or(UNIX_EPOCH)
            .duration_since(UNIX_EPOCH).unwrap_or_default().as_millis().min(u64::MAX as u128) as u64;
        output.push(ArchiveFile {
            path: path.to_string_lossy().into_owned(),
            relative_path: relative.to_string_lossy().replace('\\', "/"),
            name: path.file_name().unwrap_or_default().to_string_lossy().into_owned(),
            size: metadata.len(),
            mtime_ms,
            cid,
            file_type,
        });
    }
    Ok(())
}

#[tauri::command]
async fn list_archive_files(root: String) -> Result<Vec<ArchiveFile>, String> {
    tauri::async_runtime::spawn_blocking(move || -> Result<Vec<ArchiveFile>, String> {
        let root = plain_path(&PathBuf::from(root).canonicalize().map_err(|e| format!("مسیر پوشه معتبر نیست: {e}"))?);
        if !root.is_dir() {
            return Err("مسیر انتخاب‌شده پوشه نیست".into());
        }
        let mut files = Vec::new();
        collect_archive_files(&root, &root, &mut files)?;
        files.sort_by(|a, b| a.relative_path.to_lowercase().cmp(&b.relative_path.to_lowercase()));
        Ok(files)
    })
    .await
    .map_err(|e| e.to_string())?
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ShortcutInput {
    source_path: String,
    relative_path: String,
    game_name: String,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ShortcutReport {
    created: usize,
    skipped: usize,
    errors: Vec<String>,
    output_dir: String,
}

/// WScript.Shell can only save shortcuts to paths made of characters in the system ANSI code page
/// (e.g. "METAL GEAR SOLID \u{394}" becomes "?"), so folder and shortcut names are folded to plain ASCII.
fn ascii_fold(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    for c in input.chars() {
        if c.is_ascii() { out.push(c); continue; }
        let rep = match c {
            'à' | 'á' | 'â' | 'ã' | 'ä' | 'å' | 'ā' => "a", 'À' | 'Á' | 'Â' | 'Ã' | 'Ä' | 'Å' | 'Ā' => "A",
            'ç' => "c", 'Ç' => "C", 'è' | 'é' | 'ê' | 'ë' | 'ē' => "e", 'È' | 'É' | 'Ê' | 'Ë' | 'Ē' => "E",
            'ì' | 'í' | 'î' | 'ï' | 'ī' => "i", 'Ì' | 'Í' | 'Î' | 'Ï' | 'Ī' => "I", 'ñ' => "n", 'Ñ' => "N",
            'ò' | 'ó' | 'ô' | 'õ' | 'ö' | 'ō' | 'ø' => "o", 'Ò' | 'Ó' | 'Ô' | 'Õ' | 'Ö' | 'Ō' | 'Ø' => "O",
            'ù' | 'ú' | 'û' | 'ü' | 'ū' => "u", 'Ù' | 'Ú' | 'Û' | 'Ü' | 'Ū' => "U",
            'ý' | 'ÿ' => "y", 'Ý' => "Y", 'ß' => "ss", 'æ' => "ae", 'Æ' => "AE", 'œ' => "oe", 'Œ' => "OE",
            'Δ' => "Delta", 'Σ' => "Sigma", 'Ω' => "Omega", 'α' => "alpha", 'β' => "beta", 'π' => "pi", 'λ' => "lambda", 'μ' => "mu",
            '™' | '®' | '©' | '“' | '”' | '«' | '»' => "", '’' | '‘' | '´' => "'", '–' | '—' | '−' => "-", '…' => "...", '×' => "x",
            '\u{00A0}' | '\u{2009}' | '\u{200B}' => " ",
            _ => "_",
        };
        out.push_str(rep);
    }
    out
}

fn safe_component(value: &str, max_chars: usize) -> String {
    let folded = ascii_fold(value);
    let mut result: String = folded.chars().map(|c| {
        if c.is_control() || matches!(c, '<' | '>' | ':' | '"' | '/' | '\\' | '|' | '?' | '*') { '_' } else { c }
    }).take(max_chars).collect();
    result = result.trim().trim_end_matches(|c: char| c == '.' || c.is_whitespace()).to_string();
    if result.is_empty() { result = "Unknown game".to_string(); }
    let reserved = ["CON", "PRN", "AUX", "NUL", "COM1", "COM2", "COM3", "COM4", "COM5", "COM6", "COM7", "COM8", "COM9", "LPT1", "LPT2", "LPT3", "LPT4", "LPT5", "LPT6", "LPT7", "LPT8", "LPT9"];
    let stem = result.split('.').next().unwrap_or("").to_ascii_uppercase();
    if reserved.contains(&stem.as_str()) { result.insert(0, '_'); }
    result
}

fn short_path_hash(value: &str) -> String {
    let mut hash: u64 = 0xcbf29ce484222325;
    for byte in value.as_bytes() {
        hash ^= *byte as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("{:08X}", (hash & 0xFFFF_FFFF) as u32)
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ShortcutEntry {
    target_path: String,
    shortcut_path: String,
    relative_path: String,
}

#[derive(Deserialize, Default)]
#[serde(rename_all = "camelCase")]
struct PowerShellShortcutError {
    relative_path: String,
    message: String,
}

#[derive(Deserialize, Default)]
#[serde(rename_all = "camelCase")]
struct PowerShellShortcutResult {
    created: usize,
    errors: Vec<PowerShellShortcutError>,
}

#[cfg(target_os = "windows")]
fn write_windows_shortcuts(output_dir: &Path, entries: &[ShortcutEntry]) -> Result<(usize, Vec<String>), String> {
    let mut created = 0usize;
    let mut errors: Vec<String> = Vec::new();
    for chunk in entries.chunks(200) {
        match write_windows_shortcuts_chunk(output_dir, chunk) {
            Ok((c, e)) => { created += c; errors.extend(e); }
            Err(e) => errors.push(e),
        }
    }
    Ok((created, errors))
}

#[cfg(target_os = "windows")]
fn write_windows_shortcuts_chunk(output_dir: &Path, entries: &[ShortcutEntry]) -> Result<(usize, Vec<String>), String> {
    if entries.is_empty() { return Ok((0, Vec::new())); }
    let stamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_nanos();
    let manifest = output_dir.join(format!(".psa-shortcuts-{}-{stamp}.json", std::process::id()));
    let payload = serde_json::to_vec(&serde_json::json!({ "items": entries })).map_err(|e| e.to_string())?;
    fs::write(&manifest, payload).map_err(|e| format!("ساخت فهرست شورتکات‌ها ناموفق بود: {e}"))?;

    // One PowerShell process creates all .lnk files in a batch, rather than launching
    // a new process for every archive item. Paths are read from a UTF-8 JSON manifest
    // so Persian and other Unicode folder/file names remain intact.
    let script = r#"$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$json = Get-Content -LiteralPath $env:PSA_MANIFEST_PATH -Raw -Encoding UTF8
$parsed = ConvertFrom-Json -InputObject $json
$items = @($parsed.items)
$shell = New-Object -ComObject WScript.Shell
$created = 0
$errors = @()
foreach ($item in $items) {
  try {
    $link = $shell.CreateShortcut([string]$item.shortcutPath)
    $link.TargetPath = [string]$item.targetPath
    # not Split-Path -LiteralPath -Parent: that combination fails on Windows PowerShell 5.1 ("Parameter set cannot be resolved")
    $link.WorkingDirectory = [System.IO.Path]::GetDirectoryName([string]$item.targetPath)
    $link.Description = 'PS Archive Manager shortcut'
    $link.Save()
    $created++
  } catch {
    $errors += [pscustomobject]@{ relativePath = [string]$item.relativePath; message = $_.Exception.Message }
  }
}
[pscustomobject]@{ created = $created; errors = @($errors) } | ConvertTo-Json -Depth 4 -Compress
"#;
    use std::os::windows::process::CommandExt;
    const CREATE_NO_WINDOW: u32 = 0x0800_0000; // run in the background, no console window flashing
    let result = Command::new("powershell.exe")
        .args(["-NoProfile", "-NonInteractive", "-ExecutionPolicy", "Bypass", "-Command", script])
        .env("PSA_MANIFEST_PATH", &manifest)
        .creation_flags(CREATE_NO_WINDOW)
        .output();
    let _ = fs::remove_file(&manifest);
    let output = result.map_err(|e| format!("اجرای PowerShell ممکن نشد: {e}"))?;
    if !output.status.success() {
        let detail = String::from_utf8_lossy(&output.stderr).trim().to_string();
        return Err(if detail.is_empty() { "ساخت شورتکات‌های ویندوز ناموفق بود".into() } else { detail });
    }
    let parsed: PowerShellShortcutResult = serde_json::from_slice(&output.stdout)
        .map_err(|e| format!("خواندن نتیجه ساخت شورتکات‌ها ناموفق بود: {e}; {}", String::from_utf8_lossy(&output.stdout)))?;
    let errors = parsed.errors.into_iter()
        .map(|e| format!("{}: {}", e.relative_path, e.message))
        .collect();
    Ok((parsed.created, errors))
}

#[cfg(not(target_os = "windows"))]
fn write_windows_shortcuts(_output_dir: &Path, _entries: &[ShortcutEntry]) -> Result<(usize, Vec<String>), String> {
    Err("ساخت شورتکات .lnk فقط در نسخه ویندوز پشتیبانی می‌شود".into())
}

#[tauri::command]
async fn create_game_shortcuts(root: String, items: Vec<ShortcutInput>) -> Result<ShortcutReport, String> {
    let root = plain_path(&PathBuf::from(root).canonicalize().map_err(|e| format!("مسیر آرشیو معتبر نیست: {e}"))?);
    if !root.is_dir() { return Err("مسیر آرشیو پوشه نیست".into()); }
    let output_dir = root.join("PS Archive Shortcuts");
    let mut report = ShortcutReport { created: 0, skipped: 0, errors: Vec::new(), output_dir: output_dir.to_string_lossy().into_owned() };
    if items.is_empty() { return Ok(report); }

    // .psa-index.json remembers which target each shortcut was created for, so two different
    // files with the same name never end up sharing (or silently skipping) a shortcut,
    // regardless of the order or subset of files in a given call.
    let index_path = output_dir.join(".psa-index.json");
    let mut index: HashMap<String, String> = fs::read(&index_path).ok()
        .and_then(|b| serde_json::from_slice(&b).ok()).unwrap_or_default();
    let mut planned: HashMap<String, String> = HashMap::new();
    let mut pending: Vec<ShortcutEntry> = Vec::new();

    for item in items {
        let game_name = item.game_name.trim();
        if game_name.is_empty() { report.skipped += 1; continue; }
        let source = match PathBuf::from(&item.source_path).canonicalize() {
            Ok(p) => plain_path(&p),
            Err(_) => { report.errors.push(format!("فایل پیدا نشد: {}", item.relative_path)); continue; }
        };
        if !source.starts_with(&root) || !source.is_file() || !supported_archive(&source) {
            report.errors.push(format!("مسیر فایل معتبر نیست: {}", item.relative_path));
            continue;
        }
        let game_dir = output_dir.join(safe_component(game_name, 60));
        let original_name = source.file_name().unwrap_or_default().to_string_lossy().into_owned();
        // Windows MAX_PATH: keep the whole .lnk path under 260 characters.
        let dir_len = game_dir.to_string_lossy().chars().count();
        let room = 258usize.saturating_sub(dir_len + 1 + 4 + 11);
        if room < 12 {
            report.errors.push(format!("مسیر برای شورتکات خیلی طولانی است: {}", item.relative_path));
            continue;
        }
        let base_name = safe_component(&original_name, room.min(120));
        let target = source.to_string_lossy().into_owned();
        let candidates = [
            game_dir.join(format!("{base_name}.lnk")),
            game_dir.join(format!("{base_name} [{}].lnk", short_path_hash(&item.relative_path))),
        ];
        let mut chosen: Option<(PathBuf, bool)> = None; // (link path, already exists for this target)
        for cand in candidates {
            let key = cand.to_string_lossy().to_lowercase();
            match planned.get(&key).or_else(|| index.get(&key)) {
                Some(t) if *t == target => { chosen = Some((cand, true)); break; }
                Some(_) => continue,
                // made before the index existed: assume it is the right one
                None if cand.exists() => { chosen = Some((cand, true)); break; }
                None => { chosen = Some((cand, false)); break; }
            }
        }
        let (link_path, already) = match chosen {
            Some(v) => v,
            None => { report.errors.push(format!("برخورد نام شورتکات: {}", item.relative_path)); continue; }
        };
        if already { report.skipped += 1; continue; }
        if let Err(e) = fs::create_dir_all(&game_dir) {
            report.errors.push(format!("ساخت پوشه بازی ناموفق بود: {game_name} ({e})"));
            continue;
        }
        planned.insert(link_path.to_string_lossy().to_lowercase(), target.clone());
        pending.push(ShortcutEntry {
            target_path: target,
            shortcut_path: link_path.to_string_lossy().into_owned(),
            relative_path: item.relative_path,
        });
    }

    match write_windows_shortcuts(&output_dir, &pending) {
        Ok((created, errors)) => {
            report.created = created;
            report.errors.extend(errors);
        }
        Err(e) => report.errors.push(e),
    }
    if !pending.is_empty() {
        for e in &pending {
            if Path::new(&e.shortcut_path).exists() {
                index.insert(e.shortcut_path.to_lowercase(), e.target_path.clone());
            }
        }
        if let Ok(bytes) = serde_json::to_vec(&index) { let _ = fs::write(&index_path, bytes); }
    }
    report.errors.truncate(10);
    Ok(report)
}


#[tauri::command]
fn open_shortcuts_folder(root: String) -> Result<(), String> {
    let root = plain_path(&PathBuf::from(root).canonicalize().map_err(|e| e.to_string())?);
    if !root.is_dir() { return Err("مسیر آرشیو پوشه نیست".into()); }
    let folder = root.join("PS Archive Shortcuts");
    if !folder.is_dir() { return Err("هنوز پوشه شورتکات‌ها ساخته نشده است".into()); }
    #[cfg(target_os = "windows")]
    let result = Command::new("explorer.exe").arg(&folder).spawn();
    #[cfg(target_os = "macos")]
    let result = Command::new("open").arg(&folder).spawn();
    #[cfg(all(unix, not(target_os = "macos")))]
    let result = Command::new("xdg-open").arg(&folder).spawn();
    result.map(|_| ()).map_err(|e| e.to_string())
}

fn main() {
    tauri::Builder::default()
        .plugin(tauri_plugin_dialog::init())
        .invoke_handler(tauri::generate_handler![lookup_title, open_url, save_csv, list_archive_files, create_game_shortcuts, open_shortcuts_folder])
        .on_window_event(|window, event| {
            if let tauri::WindowEvent::CloseRequested { .. } = event {
                if window.label() == "main" {
                    window.app_handle().exit(0);
                }
            }
        })
        .run(tauri::generate_context!())
        .expect("error while running application");
}
