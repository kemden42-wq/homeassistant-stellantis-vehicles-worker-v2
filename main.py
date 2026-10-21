"""
Stellantis OAuth worker (aangepaste versie voor MyPeugeot / Gigya-login)

Gebaseerd op andreadegiovine/homeassistant-stellantis-vehicles-worker-v2.
Wijzigingen:
  - Selectors één voor één, ALLE matches in ALLE frames, alleen zichtbare elementen
    (Gigya zet verborgen template-formulieren vóór het echte formulier).
  - Heuristische fallback: zoekt zelf een zichtbaar e-mail/tekstveld naast een
    zichtbaar wachtwoordveld (ook in iframes en shadow DOM).
  - Alleen de definitieve <scheme>://oauth2redirect...?code=... telt als OAuth-code,
    nooit een tussentijdse http(s)-URL met code= (gaf invalid_grant).
  - Consent-pagina (id-dcr.peugeot.com/index/authorize-consentments) met klik én
    JS requestSubmit()-fallback.
  - Herkent Gigya-foutmeldingen (fout wachtwoord e.d.) en SMS/OTP-schermen en geeft
    dan een duidelijke melding terug i.p.v. een timeout.
  - Volledige Chrome user-agent, nl-NL, minder "bot"-signalen.
  - Bug opgelost: het wachten op de code wachtte niet echt (asyncio.to_thread).
  - Debug bij fouten: URL, frames, lijst van invoervelden (zonder waarden) in de log,
    plus screenshot + HTML via /debug als env-var DEBUG_TOKEN is gezet.
    Wachtwoord, e-mail en OAuth-codes worden nooit gelogd.
"""

import os
import re
import time
import uuid
import asyncio
from urllib.parse import urlsplit, parse_qs

from fastapi import FastAPI, Request
from fastapi.responses import JSONResponse, HTMLResponse, Response, PlainTextResponse
from playwright.async_api import async_playwright

app = FastAPI()

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
)

DEBUG_DIR = "/tmp/sv-debug"
DEBUG_TOKEN = os.environ.get("DEBUG_TOKEN", "").strip()
ALWAYS_DEBUG = os.environ.get("WORKER_DEBUG", "").lower() in ("1", "true", "yes")

process_start = None
browser_start = None
browser_process_id = None
force_debug = False
ok_count = 0
ko_count = 0

playwright = None
browser = None
browser_lock = asyncio.Lock()

# --------------------------------------------------------------------------- #
# Selectors
# --------------------------------------------------------------------------- #

EMAIL_SELECTORS = [
    '#gigya-login-form input[name="username"]',
    '#gigya-login-form input[name="loginID"]',
    'form.gigya-login-form input[name="username"]',
    'form.gigya-login-form input[name="loginID"]',
    'input.gigya-input-text[name="username"]',
    'input.gigya-input-text[name="loginID"]',
    'input[name="username"]',
    'input[name="loginID"]',
    'input[name="email"]',
    'input[type="email"]',
    'input[autocomplete="username"]',
    'input[autocomplete="email"]',
    'input[id*="email" i]',
    'input[id*="login" i]',
]

PASSWORD_SELECTORS = [
    '#gigya-login-form input[name="password"]',
    'form.gigya-login-form input[name="password"]',
    'input.gigya-input-password',
    'input[name="password"]',
    'input[type="password"]',
]

SUBMIT_SELECTORS = [
    '#gigya-login-form button[type="submit"]',
    '#gigya-login-form input[type="submit"]',
    'form.gigya-login-form button[type="submit"]',
    'form.gigya-login-form input[type="submit"]',
    'input.gigya-input-submit',
    'button.gigya-input-submit',
    'form button[type="submit"]',
    'form input[type="submit"]',
]

CONSENT_SELECTORS = [
    '#consentbutton',
    '#cvs_from input[type="submit"]',
    '#cvs_from button[type="submit"]',
    '#cvs_form input[type="submit"]',
    '#cvs_form button[type="submit"]',
    'form[action*="/oauth2/authorize"] input[type="submit"]',
    'form[action*="/oauth2/authorize"] button[type="submit"]',
]

COOKIE_SELECTORS = [
    '#onetrust-reject-all-handler',
    '#onetrust-accept-btn-handler',
    '#didomi-notice-disagree-button',
    '#didomi-notice-agree-button',
    '#_psaihm_id_refuse_all_btn',
    '#_psaihm_id_accept_all_btn',
    'button[id*="refuse" i]',
    'button[id*="reject" i]',
]

GIGYA_ERROR_SELECTORS = [
    '.gigya-error-msg-active',
    '.gigya-form-error-msg.gigya-error-msg-active',
    '.gigya-error-display-active .gigya-error-msg',
]

OTP_SELECTORS = [
    'input[autocomplete="one-time-code"]',
    'input[name*="otp" i]',
    'input[name="code"]',
    'input[name*="verification" i]',
    'input[id*="otp" i]',
    'input.gigya-input-text[name="code"]',
]

# JS fallback: zoekt (ook in shadow DOM) een zichtbaar e-mail- of wachtwoordveld
# en markeert het met data-sv-pick zodat Playwright het kan vinden.
PICK_JS = r"""
(kind) => {
  const vis = (e) => {
    const r = e.getBoundingClientRect();
    const s = getComputedStyle(e);
    return r.width > 0 && r.height > 0 && s.visibility !== 'hidden' && s.display !== 'none' && s.opacity !== '0';
  };
  const all = [];
  const walk = (root) => {
    root.querySelectorAll('input, button').forEach((e) => all.push(e));
    root.querySelectorAll('*').forEach((e) => { if (e.shadowRoot) walk(e.shadowRoot); });
  };
  walk(document);
  all.forEach((e) => e.removeAttribute && e.removeAttribute('data-sv-' + kind));
  const pw = all.filter((e) => e.tagName === 'INPUT' && (e.type || '').toLowerCase() === 'password' && vis(e));
  if (kind === 'password') {
    if (pw[0]) { pw[0].setAttribute('data-sv-password', '1'); return true; }
    return false;
  }
  if (kind === 'email') {
    const cand = all.filter((e) => {
      if (e.tagName !== 'INPUT') return false;
      const t = (e.getAttribute('type') || 'text').toLowerCase();
      if (!['email', 'text', 'tel'].includes(t)) return false;
      const n = ((e.name || '') + ' ' + (e.id || '')).toLowerCase();
      if (/search|captcha|otp|zip|post/.test(n)) return false;
      return vis(e);
    });
    let pick = null;
    if (pw.length) {
      // zelfde <form> als het zichtbare wachtwoordveld, anders dichtstbijzijnde gemeenschappelijke container
      pick = cand.find((e) => e.form && e.form === pw[0].form);
      if (!pick) {
        let box = pw[0].parentElement;
        while (box && !pick) { pick = cand.find((e) => box.contains(e)); box = box.parentElement; }
      }
    }
    pick = pick || cand.find((e) => /mail|user|login|ident/i.test((e.name || '') + ' ' + (e.id || '') + ' ' + (e.autocomplete || '')));
    pick = pick || cand[0];
    if (pick) { pick.setAttribute('data-sv-email', '1'); return true; }
    return false;
  }
  return false;
}
"""

CONSENT_SUBMIT_JS = r"""
() => {
  const f = document.querySelector('#cvs_from') || document.querySelector('#cvs_form')
         || document.querySelector('form[action*="/oauth2/authorize"]');
  if (!f) return false;
  const b = f.querySelector('#consentbutton, [type="submit"]');
  try {
    if (f.requestSubmit) { b ? f.requestSubmit(b) : f.requestSubmit(); }
    else { f.submit(); }
    return true;
  } catch (e) {
    try { f.submit(); return true; } catch (e2) { return false; }
  }
}
"""

INPUTS_SUMMARY_JS = r"""
() => {
  const out = [];
  const vis = (e) => { const r = e.getBoundingClientRect(); const s = getComputedStyle(e);
    return r.width > 0 && r.height > 0 && s.visibility !== 'hidden' && s.display !== 'none'; };
  const walk = (root, depth) => {
    root.querySelectorAll('input, button, form, iframe').forEach((e) => {
      out.push({
        tag: e.tagName.toLowerCase(), type: e.getAttribute('type') || '', name: e.getAttribute('name') || '',
        id: e.id || '', cls: (e.className && e.className.toString ? e.className.toString() : '').slice(0, 60),
        form: (e.form && e.form.id) || '', visible: vis(e), shadow: depth > 0,
        src: e.tagName === 'IFRAME' ? (e.getAttribute('src') || '').slice(0, 120) : ''
      });
    });
    root.querySelectorAll('*').forEach((e) => { if (e.shadowRoot) walk(e.shadowRoot, depth + 1); });
  };
  walk(document, 0);
  return out.slice(0, 80);
}
"""

PROBE_JS = r"""
() => {
  const vis = (e) => { if (!e) return false; const r = e.getBoundingClientRect(); const s = getComputedStyle(e);
    return r.width > 0 && r.height > 0 && s.visibility !== 'hidden' && s.display !== 'none'; };
  let err = null;
  for (const e of document.querySelectorAll('.gigya-error-msg-active, .gigya-error-display-active .gigya-error-msg')) {
    if (vis(e) && e.innerText.trim()) { err = e.innerText.trim(); break; }
  }
  const consent = !!(document.querySelector('#consentbutton') || document.querySelector('#cvs_from')
     || document.querySelector('#cvs_form') || document.querySelector('form[action*="/oauth2/authorize"]'));
  let otp = false;
  for (const e of document.querySelectorAll('input[autocomplete="one-time-code"], input[name*="otp" i], input[name="code"], input[name*="verification" i]')) {
    if (vis(e)) { otp = true; break; }
  }
  return {err, consent, otp};
}
"""

CONSENT_CLICK_JS = r"""
() => {
  const b = document.querySelector('#consentbutton');
  const vis = (e) => { const r = e.getBoundingClientRect(); return r.width > 0 && r.height > 0; };
  if (b && vis(b)) { b.click(); return 'click'; }
  const f = document.querySelector('#cvs_from') || document.querySelector('#cvs_form')
         || document.querySelector('form[action*="/oauth2/authorize"]');
  if (!f) return null;
  const sb = f.querySelector('#consentbutton, [type="submit"]');
  try { if (f.requestSubmit) { sb ? f.requestSubmit(sb) : f.requestSubmit(); } else { f.submit(); } return 'requestSubmit'; }
  catch (e) { try { f.submit(); return 'submit'; } catch (e2) { return null; } }
}
"""

COOKIE_JS = r"""
() => {
  const ids = ['onetrust-reject-all-handler', 'onetrust-accept-btn-handler', 'didomi-notice-disagree-button',
               'didomi-notice-agree-button', '_psaihm_id_refuse_all_btn', '_psaihm_id_accept_all_btn'];
  for (const id of ids) { const b = document.getElementById(id);
    if (b) { const r = b.getBoundingClientRect(); if (r.width > 0 && r.height > 0) { b.click(); return id; } } }
  return null;
}
"""

STEALTH_JS = """
Object.defineProperty(navigator, 'webdriver', {get: () => undefined});
Object.defineProperty(navigator, 'languages', {get: () => ['nl-NL', 'nl', 'en']});
window.chrome = window.chrome || { runtime: {} };
"""

# --------------------------------------------------------------------------- #
# Logging
# --------------------------------------------------------------------------- #

def log_process(message, process_id, force=False):
    if force or force_debug or ALWAYS_DEBUG:
        print(f"[{process_id}] {message}", flush=True)


def redact(text, email=None):
    if not text:
        return text
    text = re.sub(r"(code|access_token|id_token|refresh_token|password)=([^&\s\"']+)", r"\1=***", text)
    if email:
        text = text.replace(email, "***@***")
    text = re.sub(r"[\w.+-]+@[\w-]+\.[\w.-]+", "***@***", text)
    return text


def log_start_process(process_id):
    global process_start
    process_start = time.perf_counter()
    log_process("Process start", process_id, True)


def log_end_process(process_id):
    if process_start:
        log_process(f"Process end: {time.perf_counter() - process_start:.2f}s", process_id, True)
        log_process(f"Totals OK: {ok_count}", process_id, True)
        log_process(f"Totals KO: {ko_count}", process_id, True)


# --------------------------------------------------------------------------- #
# Browser lifecycle
# --------------------------------------------------------------------------- #

async def start_browser():
    global playwright, browser, browser_start, browser_process_id
    playwright = await async_playwright().start()
    browser = await playwright.chromium.launch(
        headless=True,
        args=[
            "--no-sandbox",
            "--disable-dev-shm-usage",
            "--disable-gpu",
            "--disable-extensions",
            "--disable-background-networking",
            "--disable-sync",
            "--disable-translate",
            "--disable-notifications",
            "--disable-default-apps",
            "--disable-blink-features=AutomationControlled",
            "--mute-audio",
            "--no-first-run",
            "--no-zygote",
        ],
    )
    browser_process_id = uuid.uuid4().hex[:8]
    browser_start = time.perf_counter()
    log_process("Browser start", browser_process_id, True)


async def ensure_browser():
    global browser
    if browser is None or not browser.is_connected():
        try:
            if playwright:
                await playwright.stop()
        except Exception:
            pass
        await start_browser()


@app.on_event("startup")
async def startup():
    os.makedirs(DEBUG_DIR, exist_ok=True)
    async with browser_lock:
        await start_browser()


@app.on_event("shutdown")
async def shutdown():
    if browser:
        await browser.close()
    if playwright:
        await playwright.stop()
    if browser_start:
        log_process(f"Browser end: {time.perf_counter() - browser_start:.2f}s", browser_process_id, True)


def http_response(message, process_id, status=400):
    global ok_count, ko_count
    if status == 200:
        ok_count += 1
        body = {"code": message}
        log_process("Response: OAuth code returned", process_id, True)
    else:
        ko_count += 1
        body = {"message": f"{message} [{process_id}]", "code": status}
        log_process(f"Response: {message}", process_id, True)
    log_end_process(process_id)
    return JSONResponse(
        status_code=status,
        content=body,
        headers={
            "Access-Control-Allow-Origin": "*",
            "Access-Control-Allow-Methods": "POST",
            "Access-Control-Allow-Headers": "Content-Type",
        },
    )


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #

def extract_final_code(url):
    """Alleen <scheme>://oauth2redirect/...?code=... telt. Nooit http(s)."""
    if not url:
        return None
    low = url.lower()
    if low.startswith("http://") or low.startswith("https://"):
        return None
    if "oauth2redirect" not in low:
        return None
    # Code ONGEWIJZIGD teruggeven (nog percent-encoded), net als de originele worker;
    # de integratie zet hem zo in de query string van de token-aanvraag.
    m = re.search(r"[?&#]code=([^&#\s]+)", url)
    return m.group(1) if m else None


async def first_visible(page, selectors):
    """Probeer elke selector apart, alle matches, in alle frames; geef eerste zichtbare terug."""
    for frame in page.frames:
        for sel in selectors:
            try:
                loc = frame.locator(sel)
                n = await loc.count()
                for i in range(min(n, 25)):
                    el = loc.nth(i)
                    if await el.is_visible():
                        return el, sel, frame
            except Exception:
                continue
    return None, None, None


async def pick_with_js(page, kind):
    for frame in page.frames:
        try:
            if await frame.evaluate(PICK_JS, kind):
                el = frame.locator(f'[data-sv-{kind}="1"]').first
                if await el.count() and await el.is_visible():
                    return el, f"js-fallback:{kind}", frame
        except Exception:
            continue
    return None, None, None


async def wait_visible(page, selectors, timeout_ms, process_id, label, js_kind=None, js_first=False):
    deadline = time.monotonic() + timeout_ms / 1000
    while True:
        el = sel = frame = None
        if js_kind and js_first:
            el, sel, frame = await pick_with_js(page, js_kind)
        if not el:
            el, sel, frame = await first_visible(page, selectors)
        if not el and js_kind and not js_first:
            el, sel, frame = await pick_with_js(page, js_kind)
        if el:
            where = "main" if frame == page.main_frame else f"iframe {redact(frame.url)[:80]}"
            try:
                info = await el.evaluate("e => ({name: e.name || '', id: e.id || '', type: e.type || '', form: (e.form && e.form.id) || ''})")
            except Exception:
                info = {}
            log_process(f"{label} found via {sel} ({where}) {info}", process_id, True)
            return el
        if time.monotonic() > deadline:
            return None
        await asyncio.sleep(0.5)


async def dismiss_cookies(page, process_id):
    try:
        hit = await page.evaluate(COOKIE_JS)
        if hit:
            log_process(f"Cookie banner closed via #{hit}", process_id, True)
    except Exception:
        pass


async def visible_text(page, selectors):
    el, _, _ = await first_visible(page, selectors)
    if el:
        try:
            t = (await el.inner_text(timeout=2000)).strip()
            return t or None
        except Exception:
            return None
    return None


SET_VALUE_JS = """
(e, v) => {
  const proto = Object.getPrototypeOf(e);
  const setter = Object.getOwnPropertyDescriptor(proto, 'value').set;
  setter.call(e, v);
  e.dispatchEvent(new Event('input', {bubbles: true}));
  e.dispatchEvent(new Event('change', {bubbles: true}));
  e.dispatchEvent(new Event('blur', {bubbles: true}));
}
"""


async def safe_fill(el, value):
    """Snel en echt invullen: focus via JS, daarna één keer tekst invoegen via Chrome
    (zelfde echte input-events als plakken). Fallback: Playwright fill / typen / JS."""
    page = el.page
    t0 = time.perf_counter()
    try:
        await el.evaluate("e => { e.scrollIntoView({block: 'center'}); e.focus(); e.select && e.select(); }")
        await page.keyboard.insert_text(value)
    except Exception:
        pass
    ok = await _value_of(el) == value
    if not ok:
        try:
            await el.fill(value, force=True, timeout=5000)
        except Exception:
            pass
        ok = await _value_of(el) == value
    if not ok:
        try:
            await el.evaluate("e => { e.focus(); e.value = ''; }")
            await el.press_sequentially(value, delay=20, timeout=8000)
        except Exception:
            pass
        ok = await _value_of(el) == value
    if not ok:
        await el.evaluate(SET_VALUE_JS, value)
        ok = await _value_of(el) == value
    try:
        await el.evaluate("e => { e.dispatchEvent(new Event('change', {bubbles: true})); }")
    except Exception:
        pass
    print(f"[fill] {time.perf_counter() - t0:.1f}s ok={ok}", flush=True)
    return ok


async def _value_of(el):
    try:
        return await el.input_value(timeout=2000)
    except Exception:
        return None


async def dump_debug(page, process_id, reason, email=None):
    """Logt wat Chromium ziet, zonder credentials of tokens."""
    try:
        log_process(f"DEBUG reason: {reason}", process_id, True)
        log_process(f"DEBUG url: {redact(page.url, email)}", process_id, True)
        try:
            log_process(f"DEBUG title: {await page.title()}", process_id, True)
        except Exception:
            pass
        for i, frame in enumerate(page.frames):
            log_process(f"DEBUG frame[{i}]: {redact(frame.url, email)[:150]}", process_id, True)
            try:
                items = await frame.evaluate(INPUTS_SUMMARY_JS)
                for it in items:
                    if it["tag"] in ("input", "button", "iframe", "form"):
                        log_process(
                            f"DEBUG   <{it['tag']} type={it['type']!r} name={it['name']!r} id={it['id']!r} "
                            f"form={it['form']!r} visible={it['visible']} shadow={it['shadow']} "
                            f"class={it['cls']!r} src={it['src']!r}>",
                            process_id, True,
                        )
            except Exception as e:
                log_process(f"DEBUG   (frame niet leesbaar: {e})", process_id, True)
        try:
            body = await page.inner_text("body", timeout=3000)
            body = re.sub(r"\s+", " ", body)[:800]
            log_process(f"DEBUG body: {redact(body, email)}", process_id, True)
        except Exception:
            pass
        os.makedirs(DEBUG_DIR, exist_ok=True)
        try:
            await page.screenshot(path=f"{DEBUG_DIR}/last.png", full_page=True, timeout=10000)
        except Exception:
            pass
        try:
            html = await page.content()
            with open(f"{DEBUG_DIR}/last.html", "w", encoding="utf-8") as f:
                f.write(redact(html, email))
            with open(f"{DEBUG_DIR}/last.txt", "w", encoding="utf-8") as f:
                f.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} [{process_id}] {reason}\n{redact(page.url, email)}\n")
        except Exception:
            pass
        if DEBUG_TOKEN:
            log_process("DEBUG screenshot/HTML beschikbaar via /debug?token=...", process_id, True)
    except Exception as e:
        log_process(f"DEBUG dump failed: {e}", process_id, True)


# --------------------------------------------------------------------------- #
# Main endpoint
# --------------------------------------------------------------------------- #

async def _login(payload, process_id):
    """Volledige browser-login. Geeft (status, code_of_melding) terug."""
    global force_debug
    context = None
    page = None
    state = {"code": None}
    email = None

    def on_url(url, source):
        if state["code"]:
            return
        code = extract_final_code(url)
        if code:
            state["code"] = code
            log_process(f"Code captured ({source})", process_id, True)
        elif "code=" in (url or "") and "oauth2redirect" not in (url or ""):
            log_process(f"Ignored intermediate code URL ({source}): {redact(url)[:120]}", process_id)

    try:
        url = payload.get("url")
        email = payload.get("email")
        password = payload.get("password")
        timeout_page = int(payload.get("timeout_page", 60000))
        timeout_input = int(payload.get("timeout_input", 45000))
        force_debug = bool(payload.get("debug", False))

        if not url or not email or not password:
            return (400, "Missing required params")

        async with browser_lock:
            await ensure_browser()

            context = await browser.new_context(
                user_agent=USER_AGENT,
                viewport={"width": 1280, "height": 900},
                locale="nl-NL",
                timezone_id="Europe/Amsterdam",
                java_script_enabled=True,
                bypass_csp=True,
                ignore_https_errors=True,
            )
            await context.add_init_script(STEALTH_JS)

            context.on("request", lambda r: on_url(r.url, "request"))
            context.on("requestfailed", lambda r: on_url(r.url, "requestfailed"))

            def on_response(resp):
                try:
                    if 300 <= resp.status < 400:
                        loc = resp.headers.get("location", "")
                        if loc:
                            on_url(loc, "redirect-header")
                except Exception:
                    pass

            context.on("response", on_response)

            page = await context.new_page()

            # Zware/overbodige bestanden blokkeren via Chrome zelf (geen onderschepping,
            # zodat de mymap://-redirect zichtbaar blijft). Scheelt veel tijd op Render Free.
            try:
                cdp = await context.new_cdp_session(page)
                await cdp.send("Network.enable")
                await cdp.send("Network.setBlockedURLs", {"urls": [
                    "*.png*", "*.jpg*", "*.jpeg*", "*.gif*", "*.webp*", "*.svg*", "*.ico*",
                    "*.woff*", "*.ttf*", "*.otf*", "*.mp4*", "*.webm*",
                    "*google-analytics*", "*googletagmanager*", "*doubleclick*", "*facebook*",
                    "*hotjar*", "*clarity.ms*", "*contentsquare*", "*adobedtm*", "*demdex*",
                    "*omtrdc*", "*criteo*", "*tiktok*", "*linkedin*", "*bat.bing*",
                ]})
            except Exception as e:
                log_process(f"Resource blocking unavailable: {e}", process_id)

            page.on("framenavigated", lambda f: on_url(f.url, "navigated"))

            log_process(f"Navigating to login: {redact(url)}", process_id, True)
            await page.goto(url, wait_until="domcontentloaded", timeout=timeout_page)

            await dismiss_cookies(page, process_id)

            # ---------------- login ----------------
            # Eerst het zichtbare wachtwoordveld; het e-mailveld moet in HETZELFDE formulier zitten
            # (Peugeot heeft meerdere formulieren met input[name="username"] op de pagina).
            log_process("Waiting for login form...", process_id, True)
            pw_el = None
            try:
                cand = page.locator('input[type="password"] >> visible=true').first
                await cand.wait_for(state="visible", timeout=timeout_input)
                pw_el = cand
                log_process("Password field found (fast wait)", process_id, True)
            except Exception:
                pw_el = await wait_visible(page, PASSWORD_SELECTORS, 5000, process_id, "Password field", "password", js_first=True)

            email_el = None
            if pw_el:
                try:
                    form_inputs = pw_el.locator("xpath=ancestor::form[1]").locator(
                        'input[type="text"], input[type="email"], input:not([type])').locator("visible=true")
                    if await form_inputs.count():
                        email_el = form_inputs.first
                        log_process("Email field found in password form (fast)", process_id, True)
                except Exception:
                    email_el = None
            if email_el:
                pass
            elif pw_el:
                email_el = await wait_visible(page, EMAIL_SELECTORS, 10000, process_id, "Email field", "email", js_first=True)
            else:
                email_el = await wait_visible(page, EMAIL_SELECTORS, 10000, process_id, "Email field", "email")
            if not email_el:
                await dump_debug(page, process_id, "email field not found", email)
                raise Exception("Geen zichtbaar e-mailveld gevonden (zie DEBUG-regels in de log)")

            log_process("Filling credentials...", process_id, True)
            try:
                await safe_fill(email_el, email)
            except Exception as e:
                await dump_debug(page, process_id, f"fill email failed: {e}", email)
                raise Exception(f"E-mail invullen mislukt: {e}")

            if not pw_el:
                # Mogelijk tweestaps-login: eerst e-mail, dan "Volgende"
                log_process("No password field yet, trying two-step login", process_id, True)
                nxt, _, _ = await first_visible(page, SUBMIT_SELECTORS)
                if nxt:
                    await nxt.click(timeout=5000)
                else:
                    await email_el.press("Enter")
                pw_el = await wait_visible(page, PASSWORD_SELECTORS, timeout_input, process_id, "Password field", "password")
                if not pw_el:
                    await dump_debug(page, process_id, "password field not found", email)
                    raise Exception("Geen zichtbaar wachtwoordveld gevonden")

            try:
                await safe_fill(pw_el, password)
            except Exception as e:
                await dump_debug(page, process_id, f"fill password failed: {e}", email)
                raise Exception(f"Wachtwoord invullen mislukt: {e}")
            # Controle: staan beide waarden er nog (Gigya kan een veld resetten)?
            for _ in range(2):
                ok_email = await _value_of(email_el) == email
                ok_pw = await _value_of(pw_el) == password
                log_process(f"Field check: email ok={ok_email}, password ok={ok_pw}", process_id, True)
                if ok_email and ok_pw:
                    break
                if not ok_email:
                    await safe_fill(email_el, email)
                if not ok_pw:
                    await safe_fill(pw_el, password)
            await pw_el.evaluate("e => e.dispatchEvent(new Event('blur', {bubbles: true}))")

            log_process("Submitting login form...", process_id, True)
            submit_el = None
            sel = None
            try:
                same_form = pw_el.locator("xpath=ancestor::form[1]").locator('[type="submit"], button:not([type="button"])')
                for i in range(min(await same_form.count(), 10)):
                    if await same_form.nth(i).is_visible():
                        submit_el, sel = same_form.nth(i), "same form as password"
                        break
            except Exception:
                pass
            if not submit_el:
                submit_el, sel, _ = await first_visible(page, SUBMIT_SELECTORS)
            submitted = False
            if submit_el:
                try:
                    await submit_el.click(timeout=8000)
                    submitted = True
                    log_process(f"Submit clicked via {sel}", process_id, True)
                except Exception as e:
                    log_process(f"Submit click failed ({e}), trying JS click", process_id, True)
                    try:
                        await submit_el.evaluate("e => e.click()")
                        submitted = True
                    except Exception:
                        pass
            if not submitted:
                await pw_el.press("Enter")
                log_process("Submit via Enter key", process_id, True)

            # ---------------- na login: consent / fouten / code ----------------
            log_process("Waiting for consent page / redirect...", process_id, True)
            deadline = time.monotonic() + max(timeout_page, 60000) / 1000
            login_time = time.monotonic()
            last_consent_try = 0.0
            consent_tries = 0
            otp_reported = False

            while not state["code"] and time.monotonic() < deadline:
                await asyncio.sleep(0.8)
                if state["code"]:
                    break
                try:
                    probe = await page.evaluate(PROBE_JS)
                except Exception:
                    continue  # pagina navigeert net
                if state["code"]:
                    break

                if probe.get("err"):
                    await dump_debug(page, process_id, "gigya error message", email)
                    raise Exception(f"Login geweigerd door Peugeot: {redact(probe['err'], email)[:200]}")

                if probe.get("consent") and time.monotonic() - last_consent_try > 3:
                    last_consent_try = time.monotonic()
                    consent_tries += 1
                    try:
                        how = await page.evaluate(CONSENT_CLICK_JS)
                        log_process(f"Consent submitted via {how}", process_id, True)
                    except Exception as e:
                        log_process(f"Consent submit (navigatie bezig): {e}", process_id)
                    if consent_tries > 6:
                        await dump_debug(page, process_id, "consent page stuck", email)
                        raise Exception("Blijft hangen op de toestemmingspagina")
                    continue

                if probe.get("otp") and not otp_reported and time.monotonic() - login_time > 3:
                    otp_reported = True
                    await dump_debug(page, process_id, "OTP/SMS screen detected", email)
                    raise Exception(
                        "Peugeot vraagt een SMS/verificatiecode. Dat kan de worker niet automatisch; "
                        "gebruik de handmatige OAuth-code methode in de integratie"
                    )

            if not state["code"]:
                await dump_debug(page, process_id, "no oauth2redirect code after login", email)

            code = state["code"]
            await context.close()
            context = None

            if code:
                return (200, code)
            return (400, "Code not found (zie DEBUG-regels in de log)")

    except Exception as e:
        log_process(f"Error: {redact(str(e), email)}", process_id, True)
        if context:
            try:
                await context.close()
            except Exception:
                pass
        if state["code"]:
            return (200, state["code"])
        return (400, redact(str(e), email)[:500])


# --------------------------------------------------------------------------- #
# Wachtrij + code-cache
#
# Home Assistant (of de proxy ervoor) kapt de verbinding soms na ~60 s af, terwijl
# de login op Render Free langer duurt. Daarom:
#   - de login draait als losse taak en wordt afgemaakt, ook als HA al weg is;
#   - een tweede klik op "Verzenden" sluit aan bij de lopende login (geen nieuwe login);
#   - een verkregen code blijft CODE_TTL seconden bewaard en wordt direct teruggegeven.
# --------------------------------------------------------------------------- #

CODE_TTL = int(os.environ.get("CODE_TTL", "100"))
login_jobs = {}    # key -> asyncio.Task
code_cache = {}    # key -> (code, timestamp)


def _job_key(payload):
    import hashlib
    raw = f"{payload.get('url', '')}|{payload.get('email', '')}|{payload.get('password', '')}"
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def _cached_code(key):
    item = code_cache.get(key)
    if not item:
        return None
    code, ts = item
    if time.monotonic() - ts > CODE_TTL:
        code_cache.pop(key, None)
        return None
    return code


async def _run_job(key, payload, process_id):
    try:
        status, message = await _login(payload, process_id)
    except Exception as e:
        status, message = 400, str(e)
    if status == 200:
        # Code klaarzetten; precies ÉÉN aanvraag mag hem ophalen (een code is eenmalig).
        code_cache[key] = (message, time.monotonic())
    return status, message


ALREADY_DONE_MSG = (
    "De vorige poging is op de achtergrond al gelukt en heeft de code gebruikt. "
    "Sluit dit venster, wacht even en open de integratie / 'Opnieuw configureren' opnieuw"
)


@app.post("/")
async def fetch(request: Request):
    process_id = uuid.uuid4().hex[:8]
    log_start_process(process_id)
    try:
        payload = await request.json()
    except Exception:
        return http_response("Invalid JSON", process_id)

    if not payload.get("url") or not payload.get("email") or not payload.get("password"):
        return http_response("Missing required params", process_id)

    key = _job_key(payload)

    # Code van een login waarvan niemand de uitkomst heeft opgehaald (bijv. worker-herstart van HA)
    code = _cached_code(key)
    job = login_jobs.get(key)
    if code and (job is None or job.done()):
        code_cache.pop(key, None)
        log_process("Returning unclaimed OAuth code", process_id, True)
        return http_response(code, process_id, 200)

    joined = False
    if job and not job.done():
        joined = True
        log_process("Login for this account already running, joining it", process_id, True)
    else:
        code_cache.pop(key, None)
        job = asyncio.create_task(_run_job(key, payload, process_id))
        login_jobs[key] = job

    status, message = await asyncio.shield(job)

    if status != 200:
        return http_response(message, process_id, status)

    item = code_cache.pop(key, None)
    if item:
        if joined:
            log_process("Joined request claimed the code (first request was gone)", process_id, True)
        return http_response(item[0], process_id, 200)

    # Code is al door een eerdere aanvraag opgehaald; niet nogmaals uitgeven (invalid_grant).
    log_process("Code already claimed by earlier request", process_id, True)
    return http_response(ALREADY_DONE_MSG, process_id, 409)


# --------------------------------------------------------------------------- #
# Health & debug
# --------------------------------------------------------------------------- #

@app.get("/health")
async def healthcheck():
    process_id = uuid.uuid4().hex[:8]
    async with browser_lock:
        try:
            await ensure_browser()
            context = await asyncio.wait_for(browser.new_context(), timeout=10)
            page = await context.new_page()
            await page.goto("about:blank", timeout=10000)
            await context.close()
        except Exception as e:
            log_process(f"Restarting browser: {e}", process_id, True)
            try:
                if browser:
                    await browser.close()
            except Exception:
                pass
            try:
                if playwright:
                    await playwright.stop()
            except Exception:
                pass
            await start_browser()
    return {"status": "ok"}


def _debug_allowed(request: Request):
    return bool(DEBUG_TOKEN) and request.query_params.get("token") == DEBUG_TOKEN


@app.get("/debug")
async def debug_index(request: Request):
    if not _debug_allowed(request):
        return PlainTextResponse("Debug uitgeschakeld (zet env-var DEBUG_TOKEN en gebruik ?token=...)", status_code=404)
    t = request.query_params.get("token")
    info = ""
    try:
        with open(f"{DEBUG_DIR}/last.txt", encoding="utf-8") as f:
            info = f.read()
    except Exception:
        info = "Nog geen debug-gegevens."
    html = (
        "<html><body style='font-family:sans-serif;padding:12px'>"
        f"<pre style='white-space:pre-wrap'>{info.replace('<', '&lt;')}</pre>"
        f"<p><a href='/debug/page.html?token={t}'>HTML (als tekst)</a></p>"
        f"<img src='/debug/screenshot.png?token={t}&ts={int(time.time())}' style='max-width:100%;border:1px solid #ccc'>"
        "</body></html>"
    )
    return HTMLResponse(html)


@app.get("/debug/screenshot.png")
async def debug_png(request: Request):
    if not _debug_allowed(request):
        return PlainTextResponse("Not found", status_code=404)
    try:
        with open(f"{DEBUG_DIR}/last.png", "rb") as f:
            return Response(f.read(), media_type="image/png")
    except Exception:
        return PlainTextResponse("Geen screenshot", status_code=404)


@app.get("/debug/page.html")
async def debug_html(request: Request):
    if not _debug_allowed(request):
        return PlainTextResponse("Not found", status_code=404)
    try:
        with open(f"{DEBUG_DIR}/last.html", encoding="utf-8") as f:
            return PlainTextResponse(f.read())
    except Exception:
        return PlainTextResponse("Geen HTML", status_code=404)

# ---- einde van main.py (deze regel moet als laatste staan) ----
