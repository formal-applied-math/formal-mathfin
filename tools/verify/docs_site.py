"""The library's documentation site, generated from the declaration index.

docs/specs/2026-11-05-library-practices-design.md §7: one page per module, its docstring and
every public declaration with statement, docstring, source link and the declarations that use
it (Metamath's used-by pages); a subject browse from the ``## Tags`` codes; the bibliography;
and a client-side search over names, docstrings and statements. Everything comes from
``decl-index.json`` (the Lean environment's own account) and the module docstrings, so the site
cannot drift from the library.

    python3 -m tools.verify.docs_site decl-index.json --out site

Pure stdlib. CI (`docs-site.yml`) builds it from main's `decl-index` artifact and publishes it
to GitHub Pages.
"""

from __future__ import annotations

import argparse
import html
import json
import re
from collections import defaultdict
from pathlib import Path

from . import doc_standard, library
from .decl_index import DeclIndex, IndexedDecl

REPO_URL = "https://github.com/formal-applied-math/formal-mathfin"
SKIP_KINDS = frozenset({"constructor", "recursor", "quot"})

CSS = """
:root { --bg:#fdfdfc; --fg:#1d1d1f; --muted:#6b6b70; --line:#e4e4e7; --code:#f4f4f5;
        --accent:#2f5aa8; }
@media (prefers-color-scheme: dark) {
  :root { --bg:#151517; --fg:#e8e8ea; --muted:#9a9aa2; --line:#2c2c31; --code:#1f1f23;
          --accent:#8fb0ec; } }
* { box-sizing: border-box; }
body { margin:0; background:var(--bg); color:var(--fg);
       font:16px/1.55 system-ui, -apple-system, "Segoe UI", sans-serif; }
header { border-bottom:1px solid var(--line); padding:12px 16px; display:flex; gap:16px;
         align-items:center; flex-wrap:wrap; }
header a { color:var(--fg); text-decoration:none; font-weight:600; }
header input { flex:1; min-width:180px; max-width:420px; padding:6px 10px; border-radius:6px;
               border:1px solid var(--line); background:var(--bg); color:var(--fg); }
main { max-width:960px; margin:0 auto; padding:16px; }
a { color:var(--accent); }
code, pre { font-family: ui-monospace, "JetBrains Mono", Menlo, monospace; font-size:.9em; }
code { background:var(--code); padding:0 3px; border-radius:3px; }
pre { background:var(--code); padding:10px 12px; border-radius:6px; overflow-x:auto;
      white-space:pre-wrap; word-break:break-word; }
.decl { border-top:1px solid var(--line); padding:14px 0; }
.kind { font-size:.75em; text-transform:uppercase; letter-spacing:.04em; color:var(--muted);
        margin-right:8px; }
.name { font-family: ui-monospace, Menlo, monospace; font-weight:600; word-break:break-all; }
.meta { color:var(--muted); font-size:.85em; }
.meta a { color:var(--muted); }
.subjects span { display:inline-block; border:1px solid var(--line); border-radius:10px;
                 padding:0 8px; margin:2px 4px 2px 0; font-size:.8em; color:var(--muted); }
ul.mods { list-style:none; padding:0; } ul.mods li { padding:3px 0; }
#results li { padding:4px 0; }
"""

SEARCH_JS = """
(async () => {
  const box = document.getElementById('q'); if (!box) return;
  const out = document.getElementById('results');
  let rows = null;
  async function load() {
    if (rows) return rows;
    const base = document.body.dataset.base;
    rows = await (await fetch(base + 'search.json')).json();
    return rows;
  }
  box.addEventListener('input', async () => {
    const terms = box.value.toLowerCase().split(/\\s+/).filter(Boolean);
    if (!out) { if (terms.length) location.href = document.body.dataset.base +
                 'index.html?q=' + encodeURIComponent(box.value); return; }
    out.innerHTML = '';
    if (!terms.length) return;
    const all = await load(); const base = document.body.dataset.base;
    const hits = all.filter(r => terms.every(t => r.h.includes(t))).slice(0, 80);
    for (const r of hits) {
      const li = document.createElement('li');
      const a = document.createElement('a');
      a.href = base + r.u; a.textContent = r.n; a.className = 'name';
      li.append(a, document.createTextNode(' — ' + r.d));
      out.append(li);
    }
  });
  const q = new URLSearchParams(location.search).get('q');
  if (q) { box.value = q; box.dispatchEvent(new Event('input')); }
})();
"""


# ------------------------------------------------------------------ markdown

def _inline(text: str) -> str:
    """Escape, then render `code`, **bold**, *italic*, [text][key] and [text](url)."""
    parts = re.split(r"(`[^`]*`)", text)
    out = []
    for p in parts:
        if p.startswith("`") and p.endswith("`") and len(p) > 1:
            out.append(f"<code>{html.escape(p[1:-1])}</code>")
            continue
        p = html.escape(p, quote=False)
        p = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", p)
        p = re.sub(r"(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])", r"<em>\1</em>", p)
        p = re.sub(r"\[([^\]]+)\]\[([^\]\s]+)\]",
                   r'\1 <a href="{base}references.html#\2">[\2]</a>', p)
        p = re.sub(r"\[([^\]]+)\]\((https?://[^)\s]+)\)", r'<a href="\2">\1</a>', p)
        out.append(p)
    return "".join(out)


def markdown(src: str, base: str) -> str:
    """The subset of Markdown the docstrings use: headings, bullets, fences, paragraphs."""
    lines = src.strip("\n").splitlines()
    out: list[str] = []
    para: list[str] = []
    items: list[str] = []

    def flush() -> None:
        if para:
            out.append(f"<p>{_inline(' '.join(s.strip() for s in para))}</p>")
            para.clear()
        if items:
            out.append("<ul>" + "".join(f"<li>{_inline(i)}</li>" for i in items) + "</ul>")
            items.clear()

    i = 0
    while i < len(lines):
        ln = lines[i]
        if ln.strip().startswith("```"):
            flush()
            j = i + 1
            while j < len(lines) and not lines[j].strip().startswith("```"):
                j += 1
            out.append("<pre>" + html.escape("\n".join(lines[i + 1:j])) + "</pre>")
            i = j + 1
            continue
        m = re.match(r"^(#{1,6})\s+(.*)$", ln)
        if m:
            flush()
            level = min(len(m.group(1)) + 1, 6)
            out.append(f"<h{level}>{_inline(m.group(2))}</h{level}>")
        elif re.match(r"^\s*[*-]\s+", ln):
            if para:
                flush()
            items.append(re.sub(r"^\s*[*-]\s+", "", ln))
        elif not ln.strip():
            flush()
        elif items and ln.startswith("  "):
            items[-1] += " " + ln.strip()
        else:
            if items:
                flush()
            para.append(ln)
        i += 1
    flush()
    return "\n".join(out).replace("{base}", base)


# ------------------------------------------------------------------ pages

def _page(title: str, body: str, base: str, search: bool = False) -> str:
    results = '<ul id="results"></ul>' if search else ""
    return (f'<!doctype html><html lang="en"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width, initial-scale=1">'
            f"<title>{html.escape(title)}</title><style>{CSS}</style></head>"
            f'<body data-base="{base}"><header><a href="{base}index.html">MathFin</a>'
            f'<a href="{base}subjects.html">Subjects</a>'
            f'<a href="{base}references.html">References</a>'
            f'<input id="q" type="search" placeholder="Search names, docstrings, statements">'
            f"</header><main>{results}{body}</main><script>{SEARCH_JS}</script></body></html>")


def _module_url(module: str) -> str:
    return f"m/{module}.html"


def _decl_url(d: IndexedDecl) -> str:
    return f"{_module_url(d.module)}#{d.name}"


def _decl_html(d: IndexedDecl, idx: DeclIndex, base: str) -> str:
    src = f"{REPO_URL}/blob/main/{d.path}#L{d.line}"
    users = sorted(u for u in idx.used_by.get(d.name, ()) if u in idx.decls
                   and not idx.decls[u].private)
    used = ""
    if users:
        links = ", ".join(f'<a href="{base}{_decl_url(idx.decls[u])}">{html.escape(u)}</a>'
                          for u in users[:40])
        more = f" and {len(users) - 40} more" if len(users) > 40 else ""
        used = f'<div class="meta">used by {len(users)}: {links}{more}</div>'
    doc = markdown(d.doc, base) if d.doc else ""
    attrs = f' · {", ".join(d.attrs)}' if d.attrs else ""
    return (f'<div class="decl" id="{html.escape(d.name)}">'
            f'<span class="kind">{d.kind}</span><span class="name">{html.escape(d.name)}</span>'
            f'<pre>{html.escape(d.type)}</pre>{doc}'
            f'<div class="meta"><a href="{src}">source</a>{attrs}</div>{used}</div>')


def build(index_path: str | Path, out: str | Path) -> int:
    idx = DeclIndex.load(index_path)
    out = Path(out)
    (out / "m").mkdir(parents=True, exist_ok=True)
    names = doc_standard.subject_names()
    by_module: dict[str, list[IndexedDecl]] = defaultdict(list)
    for d in idx.decls.values():
        if not d.private and d.kind not in SKIP_KINDS:
            by_module[d.module].append(d)
    docs = {library.module_name(Path(d.path)): d for d in doc_standard.all_docs()}

    search = []
    for module, decls in sorted(by_module.items()):
        decls.sort(key=lambda d: d.line)
        mdoc = docs.get(module)
        title = (mdoc.title if mdoc and mdoc.title else module)
        path = library.module_path(module)
        intro = markdown(re.sub(r"^\s*#\s+.*\n", "", mdoc.text.strip() + "\n"), "../") \
            if mdoc else ""
        subjects = "".join(f'<span title="{html.escape(names.get(c, ""))}">{c}</span>'
                           for c in (mdoc.subjects if mdoc else ()))
        body = (f"<h1>{html.escape(title)}</h1><div class='meta'><code>{module}</code> · "
                f'<a href="{REPO_URL}/blob/main/{path}">source</a></div>'
                f'<div class="subjects">{subjects}</div>{intro}'
                + "".join(_decl_html(d, idx, "../") for d in decls))
        (out / _module_url(module)).write_text(_page(title, body, "../"), encoding="utf-8")
        for d in decls:
            first = (d.doc or "").strip().split("\n\n")[0].replace("\n", " ")[:160]
            search.append({"n": d.name, "u": _decl_url(d), "d": first or d.kind,
                           "h": f"{d.name} {d.doc or ''} {d.type} {module}".lower()})

    (out / "search.json").write_text(json.dumps(search, ensure_ascii=False), encoding="utf-8")

    sections: dict[str, list[str]] = defaultdict(list)
    for module in sorted(by_module):
        parts = module.split(".")
        sections[parts[1] if len(parts) > 2 else "(root)"].append(module)
    n_decl = sum(len(v) for v in by_module.values())
    body = [f"<h1>MathFin</h1><p>{len(by_module)} modules, {n_decl} public declarations "
            f"(Lean {html.escape(idx.toolchain)}). Search above, or browse by section or by "
            f'<a href="subjects.html">subject</a>.</p>']
    for sec, mods in sections.items():
        body.append(f"<h2>{html.escape(sec)}</h2><ul class='mods'>")
        for m in mods:
            t = docs.get(m).title if docs.get(m) and docs.get(m).title else m
            body.append(f'<li><a href="{_module_url(m)}">{html.escape(t)}</a> '
                        f'<span class="meta">{m} · {len(by_module[m])}</span></li>')
        body.append("</ul>")
    (out / "index.html").write_text(_page("MathFin", "".join(body), "", search=True),
                                    encoding="utf-8")

    by_subject: dict[str, list[str]] = defaultdict(list)
    for m, d in docs.items():
        for c in d.subjects:
            by_subject[c].append(m)
    body = ["<h1>Subjects</h1><p>JEL and MSC2020 codes from the modules' <code>Tags</code>."]
    for code, name in names.items():
        mods = sorted(by_subject.get(code, ()))
        if not mods:
            continue
        body.append(f'<h2 id="{code.replace(" ", "-")}">{code} — {html.escape(name)}</h2>'
                    "<ul class='mods'>")
        body += [f'<li><a href="{_module_url(m)}">{html.escape(docs[m].title or m)}</a></li>'
                 for m in mods if m in by_module]
        body.append("</ul>")
    (out / "subjects.html").write_text(_page("Subjects", "".join(body), ""), encoding="utf-8")

    body = ["<h1>References</h1>"]
    for key, clean in doc_standard.bib_entries().items():
        bits = [clean.get("author", ""), f"<em>{html.escape(clean.get('title', ''))}</em>",
                clean.get("journal", "") or clean.get("publisher", "")
                or clean.get("institution", ""), clean.get("year", "")]
        body.append(f'<p id="{key}"><strong>[{key}]</strong> '
                    + ", ".join(b for b in bits if b) + "</p>")
    (out / "references.html").write_text(_page("References", "".join(body), ""),
                                         encoding="utf-8")
    return len(by_module)


def main() -> int:
    ap = argparse.ArgumentParser(prog="python3 -m tools.verify.docs_site")
    ap.add_argument("index")
    ap.add_argument("--out", default="site")
    args = ap.parse_args()
    n = build(args.index, args.out)
    print(f"docs site: {n} module pages in {args.out}/")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
