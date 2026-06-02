#!/usr/bin/env python3
"""FormalRV lightweight API-documentation generator.

Parses the project's own `.lean` sources (NO Lean / mathlib build required) and
emits a small static HTML site documenting ONLY FormalRV's declarations:
their kind, source signature, and `/-- ... -/` docstring, grouped by concern
folder and module.

Usage:  python scripts/gen_docs.py [--src FormalRV] [--out site]
The whole thing runs in seconds and depends on nothing but the Python stdlib.
"""
import os, re, html, json, argparse, datetime

DECL_KW = ["theorem", "lemma", "def", "abbrev", "structure", "inductive",
           "instance", "class", "opaque", "axiom", "example"]
MODS = {"private", "protected", "noncomputable", "partial", "unsafe", "scoped", "local"}
KIND_LABEL = {"theorem": "theorem", "lemma": "lemma", "def": "def", "abbrev": "abbrev",
              "structure": "structure", "inductive": "inductive", "instance": "instance",
              "class": "class", "opaque": "opaque", "axiom": "axiom", "example": "example"}

def depths(lines):
    """Block-comment nesting depth at the START of each line."""
    out = []; d = 0
    for ln in lines:
        out.append(d)
        i = 0; n = len(ln)
        while i < n:
            two = ln[i:i+2]
            if two == "--" and d == 0:
                break
            if two == "/-":
                d += 1; i += 2; continue
            if two == "-/" and d > 0:
                d -= 1; i += 2; continue
            i += 1
    return out

def strip_doc(block):
    """Turn a /-- ... -/ (or /-! ... -/) block into plain text."""
    t = block.strip()
    for op in ("/--", "/-!", "/-"):
        if t.startswith(op):
            t = t[len(op):]; break
    if t.endswith("-/"):
        t = t[:-2]
    lines = [re.sub(r"^\s*\*?\s?", "", ln) for ln in t.split("\n")]
    return "\n".join(lines).strip()

def collect_block(lines, i):
    """From line i that opens a /- .. -/ comment, return (text, next_index)."""
    buf = []; d = 0; n = len(lines)
    while i < n:
        ln = lines[i]; buf.append(ln)
        j = 0
        while j < len(ln):
            two = ln[j:j+2]
            if two == "/-": d += 1; j += 2; continue
            if two == "-/":
                d -= 1; j += 2
                if d == 0:
                    return "\n".join(buf), i + 1
                continue
            j += 1
        i += 1
    return "\n".join(buf), i

def decl_name_kind(line):
    toks = re.findall(r"[A-Za-z_][A-Za-z0-9_'.!?]*", line)
    j = 0
    while j < len(toks) and toks[j] in MODS:
        j += 1
    if j < len(toks) and toks[j] in DECL_KW:
        kw = toks[j]
        name = toks[j+1] if j+1 < len(toks) and kw != "example" else "(example)"
        return name, kw
    return None, None

def capture_signature(lines, i):
    """Capture the declaration signature from line i up to ':=' / 'where' / body."""
    out = []; n = len(lines)
    for k in range(i, min(i + 12, n)):
        ln = lines[k]
        if k > i and ln and not ln[0].isspace():  # next top-level thing
            if re.match(r"^(/-|@\[|" + "|".join(DECL_KW) + r"|namespace|end|open|section|variable)", ln):
                break
        # cut at the proof / body marker
        m = re.search(r":=|\bwhere\b|\bby\b$", ln)
        seg = ln[:m.start()] if m else ln
        out.append(seg.rstrip())
        if m:
            break
        if ln.strip() == "" and out and "".join(out).strip():
            break
    sig = "\n".join(out).rstrip()
    sig = re.sub(r"\n\s*\n", "\n", sig)
    return sig.strip()

def parse_module(path):
    lines = open(path, encoding="utf-8").read().split("\n")
    dep = depths(lines)
    n = len(lines)
    module_doc = ""; decls = []; pending = None; i = 0
    seen_decl = False
    while i < n:
        ln = lines[i]; col0 = (len(ln) > 0 and not ln[0].isspace()); d = dep[i]
        if col0 and d == 0 and (ln.startswith("/--") or ln.startswith("/-!") or ln.startswith("/-")):
            block, nxt = collect_block(lines, i)
            txt = strip_doc(block)
            if ln.startswith("/--"):
                pending = txt
            else:  # /-! or /- : section/module doc
                if not seen_decl and not module_doc and txt:
                    module_doc = txt
            i = nxt; continue
        if col0 and d == 0:
            name, kw = decl_name_kind(ln)
            if kw:
                sig = capture_signature(lines, i)
                decls.append({"name": name, "kind": kw, "sig": sig, "doc": pending or "", "line": i + 1})
                seen_decl = True; pending = None
                i += 1; continue
            if not re.match(r"^(namespace|open|section|end|set_option|variable|universe|import|@\[)", ln):
                pending = None
        i += 1
    return module_doc, decls

# ---------- HTML rendering ----------
CSS = """
:root{--fg:#1b1b1f;--muted:#5a5a66;--bg:#fff;--card:#f7f7fa;--line:#e3e3ea;--accent:#3b5bdb;--mono:'SFMono-Regular',Consolas,'Liberation Mono',Menlo,monospace}
*{box-sizing:border-box}body{margin:0;font:15px/1.55 -apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,Helvetica,Arial,sans-serif;color:var(--fg);background:var(--bg)}
a{color:var(--accent);text-decoration:none}a:hover{text-decoration:underline}
header{position:sticky;top:0;background:var(--bg);border-bottom:1px solid var(--line);padding:14px 22px;display:flex;align-items:center;gap:16px;flex-wrap:wrap;z-index:5}
header h1{font-size:18px;margin:0}header h1 a{color:var(--fg)}
.layout{display:flex;align-items:flex-start}
nav.side{position:sticky;top:57px;align-self:flex-start;min-width:220px;max-height:calc(100vh - 57px);overflow:auto;padding:18px 14px;border-right:1px solid var(--line);font-size:14px}
nav.side a{display:block;padding:2px 6px;border-radius:5px;color:var(--muted)}nav.side a:hover{background:var(--card);color:var(--fg);text-decoration:none}
nav.side .grp{font-weight:600;color:var(--fg);margin-top:10px}
main{flex:1;min-width:0;padding:24px 30px;max-width:980px}
#q{flex:1;min-width:180px;padding:7px 11px;border:1px solid var(--line);border-radius:7px;font-size:14px}
.module{margin:0 0 30px}.module h2{font-size:20px;margin:26px 0 4px;padding-top:6px;border-top:2px solid var(--line)}
.modpath{font-family:var(--mono);font-size:12px;color:var(--muted)}
.mdoc{color:var(--muted);white-space:pre-wrap;margin:8px 0 14px}
.decl{background:var(--card);border:1px solid var(--line);border-radius:9px;padding:12px 14px;margin:10px 0}
.decl .hd{display:flex;gap:9px;align-items:baseline;flex-wrap:wrap}
.kind{font-family:var(--mono);font-size:11px;text-transform:uppercase;letter-spacing:.04em;padding:2px 7px;border-radius:5px;background:#e7ecff;color:#2c3e9e}
.kind.axiom{background:#ffe9e0;color:#a8410f}.kind.theorem,.kind.lemma{background:#e3f5e8;color:#1b7a3d}.kind.structure,.kind.inductive,.kind.class{background:#f3e8ff;color:#6b29b8}
.decl .nm{font-family:var(--mono);font-weight:600;font-size:15px}
.decl pre{font-family:var(--mono);font-size:13px;background:#fff;border:1px solid var(--line);border-radius:6px;padding:8px 10px;overflow:auto;margin:8px 0 0}
.decl .doc{white-space:pre-wrap;color:#333;margin-top:8px}
.count{color:var(--muted);font-size:12px;font-weight:400}
footer{color:var(--muted);font-size:12px;padding:30px;border-top:1px solid var(--line)}
.hidden{display:none}
"""

SEARCH_JS = """
const q=document.getElementById('q');
if(q){q.addEventListener('input',()=>{const t=q.value.trim().toLowerCase();
document.querySelectorAll('.decl').forEach(d=>{const n=d.dataset.name||'';d.classList.toggle('hidden',t&&!n.includes(t));});
document.querySelectorAll('.module').forEach(m=>{const any=[...m.querySelectorAll('.decl')].some(d=>!d.classList.contains('hidden'));m.classList.toggle('hidden',t&&!any);});});}
"""

def esc(s): return html.escape(s or "")

def page(title, body, depth, sidebar):
    rel = "../" * depth
    return f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{esc(title)} — FormalRV docs</title><link rel="stylesheet" href="{rel}style.css"></head>
<body><header><h1><a href="{rel}index.html">FormalRV</a></h1>
<input id="q" placeholder="filter declarations on this page…" autocomplete="off"></header>
<div class="layout"><nav class="side">{sidebar}</nav><main>{body}</main></div>
<footer>FormalRV API docs · generated by <code>scripts/gen_docs.py</code> from the Lean sources · {datetime.date.today().isoformat()}</footer>
<script src="{rel}search.js"></script></body></html>"""

def render_decl(d):
    k = d["kind"]
    doc = f'<div class="doc">{esc(d["doc"])}</div>' if d["doc"] else ""
    sig = esc(d["sig"]) if d["sig"] else esc(d["name"])
    return (f'<div class="decl" id="{esc(d["name"])}" data-name="{esc(d["name"].lower())}">'
            f'<div class="hd"><span class="kind {k}">{KIND_LABEL.get(k,k)}</span>'
            f'<span class="nm">{esc(d["name"])}</span></div>'
            f'<pre>{sig}</pre>{doc}</div>')

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default="FormalRV")
    ap.add_argument("--out", default="site")
    ap.add_argument("--root", default=".")
    a = ap.parse_args()
    base = os.path.abspath(a.root)
    srcdir = os.path.join(base, a.src)
    out = os.path.join(base, a.out)
    os.makedirs(out, exist_ok=True)

    # gather modules grouped by concern (top-level folder under FormalRV/)
    concerns = {}  # concern -> list of (modname, relpath, module_doc, decls)
    total_decls = 0
    for dp, _, fs in os.walk(srcdir):
        for fn in sorted(fs):
            if not fn.endswith(".lean"): continue
            full = os.path.join(dp, fn)
            rel = os.path.relpath(full, base).replace("\\", "/")        # FormalRV/Core/Gate.lean
            modname = rel[:-5].replace("/", ".")
            inner = os.path.relpath(full, srcdir).replace("\\", "/")     # Core/Gate.lean
            concern = inner.split("/")[0] if "/" in inner else "(top level)"
            mdoc, decls = parse_module(full)
            total_decls += len(decls)
            concerns.setdefault(concern, []).append((modname, rel, mdoc, decls))
    # also the root FormalRV.lean
    rootlean = os.path.join(base, a.src + ".lean")
    order = ["Core", "Arithmetic", "Shor", "QEC", "PPM", "LatticeSurgery",
             "System", "Framework", "Corpus", "Qualtran", "(top level)"]
    concern_names = [c for c in order if c in concerns] + [c for c in sorted(concerns) if c not in order]

    def sidebar(active):
        s = '<a class="grp" href="index.html" style="margin-top:0">Overview</a>'
        for c in concern_names:
            mods = len(concerns[c]); ds = sum(len(d) for *_, d in concerns[c])
            cur = ' style="color:var(--fg);font-weight:600"' if c == active else ""
            s += f'<a class="grp" href="{c}.html"{cur}>{esc(c)} <span class="count">({ds})</span></a>'
        return s

    # concern pages
    for c in concern_names:
        body = [f'<h1>{esc(c)} <span class="count">'
                f'{sum(len(d) for *_, d in concerns[c])} declarations in '
                f'{len(concerns[c])} modules</span></h1>']
        for modname, rel, mdoc, decls in sorted(concerns[c]):
            body.append('<section class="module">')
            body.append(f'<h2>{esc(modname)}</h2><div class="modpath">{esc(rel)}</div>')
            if mdoc: body.append(f'<div class="mdoc">{esc(mdoc)}</div>')
            if decls:
                for d in decls: body.append(render_decl(d))
            else:
                body.append('<div class="mdoc">(no documented top-level declarations)</div>')
            body.append('</section>')
        open(os.path.join(out, f"{c}.html"), "w", encoding="utf-8").write(
            page(c, "\n".join(body), 0, sidebar(c)))

    # index
    cards = []
    for c in concern_names:
        ds = sum(len(d) for *_, d in concerns[c]); ms = len(concerns[c])
        cards.append(f'<div class="decl"><div class="hd"><a class="nm" href="{c}.html">{esc(c)}</a>'
                     f'<span class="count">{ms} modules · {ds} declarations</span></div></div>')
    idx = (f'<h1>FormalRV — API documentation</h1>'
           f'<p class="mdoc">Declarations extracted from the FormalRV Lean sources '
           f'(this project only — mathlib is intentionally not included). '
           f'{total_decls} declarations across {sum(len(v) for v in concerns.values())} modules.</p>'
           f'<p>Start at <a href="Shor.html#Shor_correct_var">the main theorem</a>, '
           f'or browse by concern:</p>' + "\n".join(cards))
    open(os.path.join(out, "index.html"), "w", encoding="utf-8").write(
        page("Overview", idx, 0, sidebar(None)))
    open(os.path.join(out, "style.css"), "w", encoding="utf-8").write(CSS)
    open(os.path.join(out, "search.js"), "w", encoding="utf-8").write(SEARCH_JS)
    print(f"Wrote {len(concern_names)} concern pages + index to {out}/  "
          f"({total_decls} declarations, {sum(len(v) for v in concerns.values())} modules)")

if __name__ == "__main__":
    main()
