"""The library's documentation site, generated from the declaration index.

docs/specs/2026-11-05-library-practices-design.md §7. Everything on it comes from the library's
own records, so the site cannot drift from the library:

* ``decl-index.json`` (the Lean environment's account: every public declaration, its statement,
  docstring, attributes and the library declarations it uses);
* the module docstrings and import lists (``tools/verify/library.py``, ``doc_standard.py``);
* the corpus (``benchmarks/*.json``: each entry's status, description and the module it imports);
* the blueprint (``docs/blueprint_nodes.json``, ``docs/blueprint_frontier.toml``);
* the bibliography and the subject vocabulary (``docs/references.bib``, ``docs/subjects.toml``).

Pages: a home page with the map of the library (sections as a graph of what imports what) and the
blueprint's landmarks; a page per section with its module graph; a page per module with its
docstring, its import neighbourhood, the corpus entries it formalizes and every declaration
(statement with linked names, docstring, source, used-by); the blueprint as a dependency graph and
as the program tree (tree.html, with the corpus placed on it by program_tree.py); the
corpus by status; the subjects; the references; and a ranked client-side search.

    python3 -m tools.verify.docs_site decl-index.json --out site

Pure stdlib; the page scripts load Cytoscape (graphs) and KaTeX (math) from cdnjs/jsdelivr.
CI (`docs-site.yml`) builds it from main's `decl-index` artifact and publishes it to GitHub Pages.
"""

from __future__ import annotations

import argparse
import html
import json
import re
import shutil
import tomllib
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

from . import doc_standard, library, taxonomy
from .blueprint_issues import issues_url
from .program_tree import tree_data
from .corpus import iter_entries
from .decl_index import DeclIndex, IndexedDecl

REPO_URL = "https://github.com/formal-applied-math/formal-mathfin"
MATHLIB_FIND = "https://leanprover-community.github.io/mathlib4_docs/find/?pattern={}#doc"
SKIP_KINDS = frozenset({"constructor", "recursor", "quot"})
ASSETS = Path(__file__).with_name("site_assets")
BLUEPRINT_NODES = Path("docs/blueprint_nodes.json")
FRONTIER = Path("docs/blueprint_frontier.toml")
LANDMARKS = Path("docs/landmarks.toml")

# The layers of the map (its colour): the taxonomy's roots, trunk and limbs.
LAYER_NAMES = {"roots": "Probability and statistics", "trunk": "Positions and markets",
               "limbs": "Valuation, choice and risk"}
LAYER_VAR = {"roots": "--s1", "trunk": "--s2", "limbs": "--s3"}
LAYER_OF_KIND = {"root": "roots", "trunk": "trunk", "limb": "limbs"}


def section_info(sec: str) -> tuple[str, str, str]:
    """(name, layer, blurb) of a section: a cell of docs/taxonomy.toml."""
    cell = taxonomy.cells().get(sec)
    if cell is None:
        return sec, "limbs", ""
    kind = taxonomy.cells()[taxonomy.part_of(sec)]["kind"]
    return taxonomy.label(sec), LAYER_OF_KIND[kind], cell["blurb"]


STATUS = {"full": "full statement", "library_wrapper": "library wrapper",
          "reduced_core": "reduced core", "placeholder": "placeholder"}
STATUS_VAR = {"full": "--s1", "library_wrapper": "--s2", "reduced_core": "--s3",
              "placeholder": "--muted"}
FONTS = ("https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@400;600"
         "&family=Source+Serif+4:opsz,wght@8..60,500;8..60,600;8..60,700&display=swap")
SCRIPTS = (
    "https://cdnjs.cloudflare.com/ajax/libs/cytoscape/3.28.1/cytoscape.min.js",
    "https://cdnjs.cloudflare.com/ajax/libs/dagre/0.8.5/dagre.min.js",
    "https://cdn.jsdelivr.net/npm/cytoscape-dagre@2.5.0/cytoscape-dagre.js",
    "https://cdnjs.cloudflare.com/ajax/libs/KaTeX/0.16.9/katex.min.js",
    "https://cdnjs.cloudflare.com/ajax/libs/KaTeX/0.16.9/contrib/auto-render.min.js",
)
KATEX_CSS = "https://cdnjs.cloudflare.com/ajax/libs/KaTeX/0.16.9/katex.min.css"


def esc(s: object) -> str:
    return html.escape(str(s), quote=True)


# ------------------------------------------------------------------ markdown

def _inline(text: str) -> str:
    """Escape, then render `code`, **bold**, *italic*, [text][key] and [text](url). Code spans and
    `$math$` are set aside first, so emphasis may run across them and never reaches inside them."""
    kept: list[str] = []

    def keep(rendered: str) -> str:
        kept.append(rendered)
        return f"\x00{len(kept) - 1}\x00"

    text = re.sub(r"`([^`]*)`", lambda m: keep(f"<code>{html.escape(m.group(1))}</code>"), text)
    text = re.sub(r"\$[^$\n]+\$", lambda m: keep(html.escape(m.group(0), quote=False)), text)
    p = html.escape(text, quote=False)
    p = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", p)
    p = re.sub(r"(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])", r"<em>\1</em>", p)
    p = re.sub(r"\[([^\]]+)\]\[([^\]\s]+)\]",
               r'\1 <a href="{base}references.html#\2">[\2]</a>', p)
    p = re.sub(r"\[([^\]]+)\]\((https?://[^)\s]+)\)", r'<a href="\2">\1</a>', p)
    return re.sub("\x00(\\d+)\x00", lambda m: kept[int(m.group(1))], p)


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


def first_sentence(text: str | None, limit: int = 200) -> str:
    """The opening sentence of a docstring paragraph, Markdown markers stripped; a sentence end or
    a cut never falls inside `$math$`."""
    if not text:
        return ""
    para = " ".join(text.strip().split("\n\n")[0].split())
    para = re.sub(r"\*\*|__|`", "", para)
    para = re.sub(r"(?<![\w*$\\])\*(\S[^*$]*?)\*(?![\w*])", r"\1", para)
    inside, end = False, len(para)
    for i, c in enumerate(para):
        if c == "$":
            inside = not inside
        elif c in ".!?" and not inside and (i + 1 == len(para) or para[i + 1] == " "):
            end = i + 1
            break
    s = para[:end]
    if len(s) <= limit:
        return s
    s = s[:limit - 1].rsplit(" ", 1)[0]
    if s.count("$") % 2:
        s = s[:s.rindex("$")].rstrip()
    return s + "…"


# ------------------------------------------------------------------ statements

_NAME = re.compile(r"(?<![\w.'])((?:[A-Z][\w']*\.)+[\w'?!]+(?:\.[\w'?!]+)*)")
_STRIP_NS = ("MeasureTheory.", "ProbabilityTheory.")


@dataclass
class Linker:
    """Statements in the index are fully qualified; show them the way doc-gen4 does: short names,
    each linked (library names to their page, upstream ones to Mathlib's docs), the full name on
    hover, and instance binders without their `inst` names."""
    idx: DeclIndex
    base: str
    public: dict[str, IndexedDecl] = field(default_factory=dict)

    def short(self, name: str) -> str:
        if name.startswith("MathFin."):
            head, _, last = name.rpartition(".")
            return f"{head.rpartition('.')[2]}.{last}" if head in self.public else last
        for ns in _STRIP_NS:
            if name.startswith(ns):
                return name[len(ns):]
        return name

    def statement(self, stmt: str) -> str:
        stmt = re.sub(r"\[inst(?:_\d+)? : ", "[", stmt)
        out, last = [], 0
        for m in _NAME.finditer(stmt):
            name = m.group(1)
            root = name.split(".", 1)[0]
            if len(root) < 3:                                   # `T.toNNReal`: a local variable
                continue
            out.append(html.escape(stmt[last:m.start()]))
            d = self.public.get(name)
            if d is not None:
                out.append(f'<a class="mf" href="{self.base}{decl_url(d)}" title="{esc(name)}">'
                           f"{esc(self.short(name))}</a>")
            elif name.startswith("MathFin."):
                out.append(f'<span title="{esc(name)}">{esc(self.short(name))}</span>')
            else:
                out.append(f'<a href="{MATHLIB_FIND.format(esc(name))}" title="{esc(name)}">'
                           f"{esc(self.short(name))}</a>")
            last = m.end()
        out.append(html.escape(stmt[last:]))
        return "".join(out)


# ------------------------------------------------------------------ the library model

def module_url(module: str) -> str:
    return f"m/{module}.html"


def decl_url(d: IndexedDecl) -> str:
    return f"{module_url(d.module)}#{d.name}"


def section_of(module: str) -> str:
    """The taxonomy cell holding a module; "" for the library's own machinery."""
    return taxonomy.cell_of(module) or ""


def section_url(sec: str) -> str:
    return f"s/{sec.replace('/', '-')}.html"


@dataclass
class Site:
    idx: DeclIndex
    decls: dict[str, list[IndexedDecl]]          # module → its public declarations, in order
    docs: dict[str, doc_standard.ModuleDoc]
    imports: dict[str, list[str]]                # module → library modules it imports
    importers: dict[str, list[str]]
    entries: dict[str, list[tuple[str, dict]]]   # module → corpus entries formalized in it
    all_entries: list[tuple[str, dict]]
    subjects: dict[str, str]

    @classmethod
    def load(cls, index_path: str | Path) -> "Site":
        idx = DeclIndex.load(index_path)
        decls: dict[str, list[IndexedDecl]] = defaultdict(list)
        for d in idx.decls.values():
            if not d.private and d.kind not in SKIP_KINDS:
                decls[d.module].append(d)
        for v in decls.values():
            v.sort(key=lambda d: d.line)
        paths = {library.module_name(p): p for p in library.modules()}
        docs = {library.module_name(Path(d.path)): d for d in doc_standard.all_docs()}
        imports = {m: [i for i in library.library_imports(p.read_text(encoding="utf-8"))
                       if i in paths and i != "MathFin.Init"] for m, p in paths.items()}
        importers: dict[str, list[str]] = defaultdict(list)
        for m, imps in imports.items():
            for i in imps:
                importers[i].append(m)
        entries: dict[str, list[tuple[str, dict]]] = defaultdict(list)
        all_entries = list(iter_entries())
        for f, e in all_entries:
            for m in library.library_imports(e["code"]["lean"]):
                if m in paths:
                    entries[m].append((f, e))
        return cls(idx, dict(decls), docs, imports, dict(importers), dict(entries), all_entries,
                   doc_standard.subject_names())

    def modules(self) -> list[str]:
        return sorted(m for m in self.imports if m != "MathFin.Init")

    def title(self, m: str) -> str:
        d = self.docs.get(m)
        return d.title if d and d.title else m.rsplit(".", 1)[-1]

    def lede(self, m: str) -> str:
        d = self.docs.get(m)
        if not d:
            return ""
        body = re.sub(r"^\s*#\s+.*\n", "", d.text.strip() + "\n").strip()
        return first_sentence(body.split("\n## ")[0], 220)


# ------------------------------------------------------------------ page shell

NAV = [("index.html", "Map"), ("landmarks.html", "Landmarks"), ("blueprint.html", "Blueprint"),
       ("tree.html", "Tree"), ("corpus.html", "Corpus"),
       ("subjects.html", "Subjects"), ("references.html", "References")]


def page(title: str, body: str, base: str, current: str = "", desc: str = "") -> str:
    nav = "".join(f'<a href="{base}{u}"{" aria-current=page" if u == current else ""}>{t}</a>'
                  for u, t in NAV)
    scripts = "".join(f'<script src="{s}" defer></script>' for s in SCRIPTS)
    return f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(title)}</title><meta name="description" content="{esc(desc or title)}">
<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="stylesheet" href="{FONTS}">
<link rel="stylesheet" href="{KATEX_CSS}"><link rel="stylesheet" href="{base}assets/site.css">
{scripts}<script src="{base}assets/site.js" defer></script></head>
<body data-base="{base}"><div class="top"><div class="top-in">
<a class="brand" href="{base}index.html">Math<span>Fin</span></a><nav class="nav">{nav}</nav>
<div class="search"><input id="q" type="search" autocomplete="off" spellcheck="false"
 placeholder="Search names, statements, docstrings" aria-label="Search"><kbd>/</kbd>
<div class="results" id="results"></div></div>
<button class="theme" id="theme" title="Toggle dark mode" aria-label="Toggle dark mode">◐</button>
</div></div><main>{body}</main>
<footer><div>MathFin · Lean 4 · built on Mathlib and BrownianMotion ·
<a href="{REPO_URL}">source</a> · generated from the library's declaration index</div></footer>
</body></html>"""


def graph(gid: str, spec: dict, cls: str = "") -> str:
    data = json.dumps(spec, ensure_ascii=False).replace("</", "<\\/")
    return (f'<div class="graph {cls}" data-graph="{gid}-data" role="img" '
            f'aria-label="{esc(spec.get("label", "graph"))}"></div>'
            f'<script type="application/json" id="{gid}-data">{data}</script>')


def legend(items: list[tuple[str, str, str]]) -> str:
    """(css colour var, label, extra class) per item."""
    return '<div class="legend">' + "".join(
        f'<span><i class="{c}" style="background:var({v})"></i>{esc(t)}</span>'
        for v, t, c in items) + "</div>"


def transitive_reduction(nodes: set[str], edges: set[tuple[str, str]]) -> set[tuple[str, str]]:
    """Drop an edge a→b when b is reachable from a another way (the graph is a DAG of imports)."""
    succ: dict[str, set[str]] = defaultdict(set)
    for a, b in edges:
        succ[a].add(b)
    keep = set()
    for a, b in edges:
        seen, stack = set(), [c for c in succ[a] if c != b]
        while stack:
            x = stack.pop()
            if x == b:
                break
            if x in seen:
                continue
            seen.add(x)
            stack.extend(succ[x])
        else:
            keep.add((a, b))
    return keep


def status_counts(entries: list[tuple[str, dict]]) -> Counter:
    return Counter(e.get("metadata", {}).get("formalization_status", "full") for _, e in entries)


def status_bar(counts: Counter, scale: int, label: str, link: str = "") -> str:
    total = sum(counts.values())
    segs = "".join(
        f'<div class="bar-seg" style="width:{100 * counts[s] / scale:.3f}%;background:var({STATUS_VAR[s]})"'
        f' data-tip="{esc(label)}: {counts[s]} {STATUS[s]}"></div>'
        for s in STATUS if counts.get(s))
    lab = f'<a href="{link}">{esc(label)}</a>' if link else esc(label)
    return (f'<div class="bar-row"><div class="lab">{lab}</div><div class="bar-track">{segs}</div>'
            f'<div class="val">{total}</div></div>')


# ------------------------------------------------------------------ pages

def build_home(site: Site, out: Path, blueprint: list[dict]) -> None:
    mods = site.modules()
    by_sec: dict[str, list[str]] = defaultdict(list)
    for m in mods:
        by_sec[section_of(m)].append(m)
    n_decl = sum(len(site.decls.get(m, ())) for m in mods)
    n_thm = sum(1 for m in mods for d in site.decls.get(m, ()) if d.kind in ("theorem", "lemma"))
    st = status_counts(site.all_entries)
    ready = st["full"] + st["library_wrapper"]
    proved = sum(1 for n in blueprint if n.get("leanOk"))

    # the map: sections, sized by declarations, edges = modules of A importing modules of B
    w: Counter = Counter()
    for m in mods:
        for i in site.imports[m]:
            a, b = section_of(m), section_of(i)
            if a and b and a != b:
                w[(b, a)] += 1                      # from the imported section to the importer
    sec_decls = {s: sum(len(site.decls.get(m, ())) for m in ms) for s, ms in by_sec.items()}
    sec_entries = {s: sum(len(site.entries.get(m, ())) for m in ms) for s, ms in by_sec.items()}
    nodes = []
    for s, ms in by_sec.items():
        if not s:
            continue
        _, layer, _ = section_info(s)
        nodes.append({"id": s, "label": taxonomy.cells()[s]["title"], "layer": layer, "url": section_url(s),
                      "sz": round(22 + 3.2 * sec_decls[s] ** 0.5, 1),
                      "info": f"{len(ms)} modules · {sec_decls[s]} declarations · "
                              f"{sec_entries[s]} corpus entries"})
    edges = [{"source": a, "target": b, "ew": round(0.8 + 1.4 * c ** 0.5, 2)}
             for (a, b), c in w.items()]
    the_map = graph("map", {"kind": "map", "nodes": nodes, "edges": edges,
                            "label": "Map of the library's sections"}, "tall")
    table = "".join(
        f'<tr><td><a href="{section_url(s)}">{esc(section_info(s)[0])}</a></td>'
        f'<td>{LAYER_NAMES[section_info(s)[1]]}</td>'
        f'<td class="n">{len(by_sec[s])}</td><td class="n">{sec_decls[s]}</td>'
        f'<td class="n">{sec_entries[s]}</td></tr>'
        for s in sorted(by_sec, key=lambda s: -sec_decls[s]) if s)

    # landmarks: the proved theorems the most other blueprint results build on, transitively
    users: dict[str, set[str]] = defaultdict(set)
    for n in blueprint:
        for u in n.get("uses", ()):
            users[u].add(n["label"])

    def reach(label: str) -> int:
        seen, stack = set(), list(users[label])
        while stack:
            x = stack.pop()
            if x not in seen:
                seen.add(x)
                stack.extend(users[x])
        return len(seen)

    proved_thms = [n for n in blueprint if n.get("latexEnv") == "theorem" and n.get("leanOk")]
    landmarks = []
    for n in sorted(proved_thms, key=lambda n: -reach(n["label"]))[:12]:
        d = site.idx.decls.get(n.get("name", ""))
        href = decl_url(d) if d and not d.private else "blueprint.html"
        text = first_sentence(n.get("text", ""), 240)
        landmarks.append(f'<a class="card" href="{href}"><h3>{esc(n["title"])}</h3>'
                         f'<div class="stmt" data-math>{esc(text)}</div>'
                         f'<div class="nums">{reach(n["label"])} results build on it · '
                         f'<span class="mono">{esc(n.get("module", "").removeprefix("MathFin."))}'
                         f'</span></div></a>')

    cards = []
    for s in sorted(by_sec, key=lambda s: -sec_decls[s]):
        if not s:
            continue
        name, layer, blurb = section_info(s)
        cards.append(f'<a class="card" href="{section_url(s)}"><h3><span class="dot" '
                     f'style="background:var({LAYER_VAR[layer]})">'
                     f'</span>{esc(name)}</h3><div class="sub">{esc(blurb)}</div>'
                     f'<div class="nums">{len(by_sec[s])} modules · {sec_decls[s]} declarations · '
                     f'{sec_entries[s]} entries</div></a>')

    body = f"""
<section class="hero"><h1>Mathematical finance, machine-checked.</h1>
<p class="lede">A Lean&nbsp;4 library on Mathlib and Rémy Degenne's BrownianMotion: stochastic
calculus, arbitrage and pricing, term structure and credit, portfolios and risk, each statement
checked by Lean's kernel. There is no <code>sorry</code>, and every theorem the corpus cites is pinned,
by the build, to Lean's three standard axioms.</p>
<div class="tiles">
<div class="tile"><div class="v">{len(mods)}</div><div class="k">modules</div></div>
<div class="tile"><div class="v">{n_decl:,}</div><div class="k">public declarations <small>· {n_thm:,} theorems</small></div></div>
<div class="tile"><div class="v">{len(site.all_entries)}</div><div class="k">corpus entries <small>· {ready} delivery-ready</small></div></div>
<div class="tile"><div class="v">{proved}</div><div class="k">blueprint results proved <small>· {sum(1 for n in blueprint if not n.get("leanOk"))} on the frontier</small></div></div>
<div class="tile"><div class="v">0</div><div class="k"><code>sorry</code> <small>· axioms pinned</small></div></div>
</div></section>

<h2>The map</h2>
<p class="ink2">Each disc is a cell of the <a href="tree.html">taxonomy</a> (<code>docs/taxonomy.toml</code>),
sized by its declarations: probability and statistics at the centre, positions and markets around
them, valuation, choice and risk outside. An arrow runs from a cell to one that builds on it,
thicker the more of its modules are imported. Hover to see a cell's neighbours, click to open it.</p>
{the_map}
{legend([(LAYER_VAR[k], v, "") for k, v in LAYER_NAMES.items()])}
<details class="tableview"><summary>Table view</summary><table class="data"><thead><tr>
<th>Cell</th><th>Layer</th><th>Modules</th><th>Declarations</th><th>Corpus entries</th></tr></thead>
<tbody>{table}</tbody></table></details>

<h2>Landmarks</h2>
<p class="ink2">The proved results on the <a href="blueprint.html">blueprint</a> that the most
other results build on.</p>
<div class="cards">{"".join(landmarks)}</div>

<h2>Cells</h2>
<div class="cards">{"".join(cards)}</div>
"""
    (out / "index.html").write_text(page("MathFin — mathematical finance in Lean", body, "",
                                         "index.html",
                                         "A Lean 4 library of formally verified mathematical finance."),
                                    encoding="utf-8")


def build_section(site: Site, out: Path, sec: str, mods: list[str]) -> None:
    name, layer, blurb = section_info(sec)
    inside = set(mods)
    edges = {(i, m) for m in mods for i in site.imports[m] if i in inside}
    red = transitive_reduction(inside, edges)
    rel = lambda m: m.removeprefix("MathFin.")  # noqa: E731
    nodes = [{"id": m, "label": rel(m), "full": site.title(m), "url": module_url(m),
              "info": f"{len(site.decls.get(m, ()))} declarations · "
                      f"{len(site.entries.get(m, ()))} corpus entries",
              "cls": layer} for m in mods]
    g = graph("sec", {"nodes": nodes, "edges": [{"source": a, "target": b} for a, b in red],
                      "label": f"Module graph of {name}"},
              "tall" if len(mods) > 40 else "")
    groups: dict[str, list[str]] = defaultdict(list)
    for m in mods:
        parts = m.split(".")
        groups[parts[2] if len(parts) > 3 else ""].append(m)
    blocks = []
    for gname in sorted(groups, key=lambda g: (g != "", g)):
        cards = "".join(
            f'<a class="card" href="../{module_url(m)}"><h3>{esc(site.title(m))}</h3>'
            f'<div class="sub">{esc(site.lede(m))}</div><div class="nums mono">{esc(m)}</div>'
            f'<div class="nums">{len(site.decls.get(m, ()))} declarations'
            + (f' · {len(site.entries[m])} corpus entries' if site.entries.get(m) else "")
            + "</div></a>" for m in groups[gname])
        head = f"<h3>{esc(gname)}</h3>" if gname else ""
        blocks.append(f"{head}<div class='cards'>{cards}</div>")
    st = status_counts([e for m in mods for e in site.entries.get(m, ())])
    body = f"""<div class="crumbs"><a href="../index.html">Map</a> / {esc(name)}</div>
<h1>{esc(name)}</h1><p class="lede ink2">{esc(blurb)}</p>
<div class="tiles"><div class="tile"><div class="v">{len(mods)}</div><div class="k">modules</div></div>
<div class="tile"><div class="v">{sum(len(site.decls.get(m, ())) for m in mods):,}</div><div class="k">declarations</div></div>
<div class="tile"><div class="v">{sum(st.values())}</div><div class="k">corpus entries <small>· {st["full"]} full</small></div></div></div>
<h2>Module graph</h2><p class="ink2">An arrow runs from a module to one that imports it (implied
imports omitted). Hover for a module's title, click to open it.</p>{g}
<h2>Modules</h2>{"".join(blocks)}"""
    (out / section_url(sec)).write_text(page(f"{name} — MathFin", body, "../", "", blurb),
                                        encoding="utf-8")


def decl_html(site: Site, d: IndexedDecl, link: Linker) -> str:
    src = f"{REPO_URL}/blob/main/{library.module_path(d.module)}#L{d.line}"
    users = sorted(u for u in site.idx.used_by.get(d.name, ())
                   if u in site.idx.decls and not site.idx.decls[u].private)
    used = ""
    if users:
        links = ", ".join(f'<a href="../{decl_url(site.idx.decls[u])}">{esc(link.short(u))}</a>'
                          for u in users[:16])
        more = f" and {len(users) - 16} more" if len(users) > 16 else ""
        used = f'<div class="meta">used by {len(users)}: {links}{more}</div>'
    ns, _, last = d.name.rpartition(".")
    attrs = "".join(f' <span class="badge">@[{esc(a)}]</span>' for a in d.attrs)
    doc = f'<div class="doc">{markdown(d.doc, "../")}</div>' if d.doc else ""
    return (f'<article class="decl" id="{esc(d.name)}"><div class="decl-h">'
            f'<span class="kind k-{d.kind}">{d.kind}</span>'
            f'<span class="dname"><span class="ns">{esc(ns)}.</span>{esc(last)}</span>{attrs}'
            f'<a class="src" href="{src}">source</a></div>'
            f'<pre class="stmt-pre">{link.statement(d.type)}</pre>{doc}{used}</article>')


def build_module(site: Site, out: Path, m: str, link: Linker) -> None:
    decls = site.decls.get(m, [])
    mdoc = site.docs.get(m)
    title = site.title(m)
    sec = section_of(m)
    sname = section_info(sec)[0]
    body_doc = markdown(re.sub(r"^\s*#\s+.*\n", "", mdoc.text.strip() + "\n"), "../") if mdoc else ""
    chips = "".join(f'<a class="chip" href="../subjects.html#{esc(c.replace(" ", "-"))}" '
                    f'title="{esc(site.subjects.get(c, ""))}">{esc(c)}</a>'
                    for c in (mdoc.subjects if mdoc else ()))
    ins, outs = site.imports.get(m, []), site.importers.get(m, [])
    nodes = [{"id": m, "label": m.rsplit(".", 1)[-1], "full": title, "cls": "center"}]
    nodes += [{"id": i, "label": i.rsplit(".", 1)[-1], "full": site.title(i), "url": module_url(i),
               "info": "imported by this module"} for i in ins]
    nodes += [{"id": o, "label": o.rsplit(".", 1)[-1], "full": site.title(o), "url": module_url(o),
               "info": "imports this module"} for o in outs if o not in ins]
    edges = [{"source": i, "target": m} for i in ins] + [{"source": m, "target": o} for o in outs]
    ego = graph("ego", {"nodes": nodes, "edges": edges, "rankDir": "TB",
                        "label": f"Imports of {m} and its importers"}, "small")
    ents = site.entries.get(m, [])
    elist = "".join(
        f'<div class="entry"><div class="eid">{esc(e["id"])} · {esc(Path(f).name)} · '
        f'{STATUS.get(e.get("metadata", {}).get("formalization_status", "full"), "")}</div>'
        f'<div class="ename">{esc(e["name"])}</div><p>{esc(e.get("description", ""))}</p></div>'
        for f, e in ents)
    toc = "".join(f'<li><a href="#{esc(d.name)}">{esc(d.name.rpartition(".")[2])}</a></li>'
                  for d in decls)
    path = library.module_path(m)
    body = f"""<div class="crumbs"><a href="../index.html">Map</a> /
<a href="../{section_url(sec)}">{esc(sname)}</a> / <span class="mono">{esc(m)}</span></div>
<h1>{esc(title)}</h1>
<div class="chips"><span class="chip mono">{esc(m)}</span>{chips}
<a class="chip" href="{REPO_URL}/blob/main/{path}">source</a></div>
<div class="modhead"><div class="doc">{body_doc}</div>
<div><h3>Import neighbourhood</h3>{ego}
<p class="muted" style="font-size:.84rem">Above: what it imports. Below: what imports it.</p>
{"<h3>Corpus entries</h3>" + elist if elist else ""}</div></div>
<h2>Declarations <span class="muted" style="font-size:1rem">{len(decls)}</span></h2>
<ul class="toc">{toc}</ul>
{"".join(decl_html(site, d, link) for d in decls)}"""
    (out / module_url(m)).write_text(page(f"{title} — MathFin", body, "../", "",
                                          site.lede(m)), encoding="utf-8")


def build_blueprint(site: Site, out: Path, nodes_json: list[dict], frontier: list[dict]) -> None:
    labels = {n["label"] for n in nodes_json} | {f["label"] for f in frontier}
    connected = {n["label"] for n in nodes_json}
    grew = True
    while grew:  # a frontier node is connected when its uses reach the proved blueprint
        grew = False
        for f in frontier:
            if f["label"] not in connected and any(u in connected for u in f.get("uses", ())):
                connected.add(f["label"])
                grew = True
    for n in nodes_json:
        connected.update(u for u in n.get("uses", ()) if u in labels)
    gnodes, cards = [], []
    for n in nodes_json:
        upstream = "upstream" in n.get("title", "").lower()
        cls = "upstream" if upstream else ("proved" if n.get("leanOk") else "frontier")
        gnodes.append({"id": n["label"], "label": n["title"], "cls": cls,
                       "info": "upstream (Mathlib)" if upstream else "proved in Lean"})
        d = site.idx.decls.get(n.get("name", ""))
        lean = (f'<a href="{decl_url(d)}"><code>{esc(n["name"])}</code></a>' if d and not d.private
                else f'<code>{esc(n.get("name", ""))}</code>')
        cards.append(f'<div id="bp-{esc(n["label"])}" hidden><h3>{esc(n["title"])}</h3>'
                     f'<p><span class="badge ok">proved</span> <span class="badge">{esc(n["label"])}</span></p>'
                     f'<div data-math>{markdown(n.get("text", ""), "")}</div><p>{lean}</p>'
                     f'<p><a href="{issues_url(n["label"])}">issues and pull requests</a></p></div>')
    for f in frontier:
        if f["label"] not in connected:
            continue
        gnodes.append({"id": f["label"], "label": f["title"], "cls": "frontier",
                       "info": "frontier: stated, not yet formalized"})
        cards.append(f'<div id="bp-{esc(f["label"])}" hidden><h3>{esc(f["title"])}</h3>'
                     f'<p><span class="badge">frontier</span> <span class="badge">{esc(f["label"])}</span>'
                     f' <span class="badge">{esc(f.get("area", ""))}</span></p>'
                     f'<p data-math>{esc(f.get("statement", ""))}</p>'
                     f'<p><a href="{issues_url(f["label"])}">open issues</a></p></div>')
    ids = {g["id"] for g in gnodes}
    gedges = [{"source": u, "target": n["label"]} for n in nodes_json + frontier
              if n["label"] in ids for u in n.get("uses", ()) if u in ids]
    g = graph("bp", {"nodes": gnodes, "edges": gedges, "panel": "bp-side",
                     "label": "Blueprint dependency graph"}, "tall")
    loose: dict[str, list[dict]] = defaultdict(list)
    for f in frontier:
        if f["label"] not in connected:
            loose[f.get("area", "") or "other"].append(f)
    loose_html = "".join(
        f"<h3>{esc(area)}</h3><div class='cards'>" + "".join(
            f'<a class="card" href="{issues_url(f["label"])}"><h3>{esc(f["title"])}</h3>'
            f'<div class="stmt">{esc(f.get("statement", ""))}</div>'
            f'<div class="nums">{esc(f.get("ground") or f["label"])}</div></a>' for f in fs)
        + "</div>"
        for area, fs in sorted(loose.items()))
    proved = sum(1 for n in nodes_json if n.get("leanOk"))
    body = f"""<h1>Blueprint</h1>
<p class="lede ink2">The program's spine: {proved} results proved in Lean, their dependencies read off
the proof terms (never drawn by hand), and the {len(frontier)} results on the frontier, stated and
not yet formalized. Arrows run from a result to the results that use it. Click a node for its statement.</p>
{legend([("--good", "proved in Lean", ""), ("--s1", "upstream (Mathlib)", ""),
         ("--muted", "frontier", "dash")])}
{g}
<aside class="panel side" id="bp-side"><p class="empty">Select a node to read its statement,
the Lean declaration that proves it, and the issues that advance it.</p></aside>
{"".join(cards)}
<h2>Frontier on upstream ground</h2>
<p class="ink2">Stated results that build on Mathlib alone, with no proved node above to grow from;
each card says what it draws on and links to its open issues. Every other frontier result reaches
the proved blueprint through its uses (<code>blueprint_issues check</code> enforces it).</p>
{loose_html}"""
    (out / "blueprint.html").write_text(page("Blueprint — MathFin", body, "", "blueprint.html",
                                             "The MathFin blueprint: dependency graph of the "
                                             "program's results."), encoding="utf-8")


TREE_SCRIPTS = ("https://cdnjs.cloudflare.com/ajax/libs/d3/7.9.0/d3.min.js", "assets/tree.js")
TREE_KINDS = (("rests-on-node", "rests on a node", "--tr-leaf-2"),
              ("feeds-node", "feeds a node", "--tr-leaf-3"),
              ("upstream-only", "upstream only", "--tr-soil-2"),
              ("off-map", "off the map", "--tr-fallen"))


def build_tree(site: Site, out: Path, nodes_json: list[dict], frontier: list[dict],
               issues: list[dict] | None) -> None:
    """The program tree: the blueprint as a tree, with the corpus as its leaves
    (tools/verify/program_tree.py places every entry)."""
    data = tree_data(site.idx, nodes_json, frontier, issues)
    data["repo"] = REPO_URL
    for n in data["nodes"]:
        d = site.idx.decls.get(n.get("d") or "")
        if d and not d.private:
            n["h"] = decl_url(d)
    areas, total = data["areas"], data["corpus"]
    off = sum(c.get("off-map", 0) for c in areas.values())
    on = sum(c.get("rests-on-node", 0) + c.get("feeds-node", 0) for c in areas.values())
    names = data["cellName"]
    bars = []
    for a in sorted(areas, key=lambda a: -sum(areas[a].values())):
        c, t = areas[a], sum(areas[a].values())
        segs = "".join(f'<span title="{label}: {c[k]}" style="width:{100 * c[k] / t:.2f}%;'
                       f'background:var({var})"></span>'
                       for k, label, var in TREE_KINDS if c.get(k))
        bars.append(f'<div class="t-bar"><span>{esc(names.get(a, a))}</span><div class="t-track">{segs}</div>'
                    f'<span class="ink2">{t - c.get("off-map", 0)} / {t}</span></div>')
    plots = "".join(
        f'<div class="t-plot"><p><b>{esc(names.get(a, a))}</b> <span class="ink2">{len(es)} off the map</span></p>'
        f'<div class="t-seeds">' + "".join(f'<i title="{esc(e)} — {esc(nm)}"></i>' for e, nm in es)
        + "</div></div>"
        for a, es in sorted(data["off"].items(), key=lambda kv: -len(kv[1])))
    partial = [n for n in data["nodes"] if n.get("core")]
    partial_rows = "".join(
        f'<tr><td><button type="button" class="t-chip" data-focus="{esc(n["l"])}">'
        f'{esc(n["t"])}</button></td><td>{", ".join(f"<code>{esc(c)}</code>" for c in n["core"])}'
        f"</td></tr>" for n in partial)
    proved = sum(n["s"] == "proved" for n in data["nodes"])
    nfront = sum(n["s"] == "frontier" for n in data["nodes"])
    payload = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    body = f"""<h1>The program tree</h1>
<p class="lede ink2">The blueprint drawn on the library's taxonomy (<code>docs/taxonomy.toml</code>),
the one statement of how it organizes financial mathematics. The roots in the soil are the tools:
probability in its branches, and statistics. The trunk is positions and markets: payoffs, the
market and its numéraire, strategies and their gains. Three limbs grow from it, one for each
question asked of a position: <em>what is it worth</em> (valuation, in the middle), <em>whether to
hold it</em> (choice, on the left) and <em>how dangerous is it</em> (risk, on the right). Each
limb's branches are its cells. A theorem between two limbs sits in the fork between them. Colour
is the model family, the same hue in every limb, so credit in valuation and credit in risk read as
one family seen by two questions; nodes with no family are general theory and keep the wood's
colour. Height is generality: the general theorems sit near the fork, instances above them, product
formulas at the tips. The dark wood drawn over the pale map is the proofs: each of the {proved}
proved results is joined to every node its proof uses, and wood thickens with the corpus it
carries. A knot's size counts the corpus entries whose proof rests deepest on it; the Leaves button
hangs them on the tree. The {nfront} frontier results are dashed blueprint shoots, each bud coloured
by the state of its issue, with the open problems as stars. Proved results that rest on no node
grow straight from the soil; entries that touch no node lie on the ground. Click a node to trace
its lineage; drag to pan, scroll to zoom; names fill in as you zoom.</p>
<div class="t-box" id="tree-box"><div class="t-tools">
<input id="t-q" type="search" placeholder="Find a node: Itô, VaR, Heston…" aria-label="Find a node" autocomplete="off">
<button type="button" id="t-grow">Grow it again</button>
<button type="button" id="t-leaves" aria-pressed="false">Leaves</button>
<span class="t-zoom"><button type="button" id="t-zin" aria-label="Zoom in">+</button><button type="button" id="t-zout" aria-label="Zoom out">−</button></span>
<button type="button" id="t-reset">Reset view</button></div>
<div class="t-stage"><svg id="tree" role="img" aria-label="The MathFin blueprint as a tree"></svg>
<aside class="t-panel" id="tree-panel" aria-live="polite"></aside></div>
<div id="tree-tip" hidden></div></div>
{legend([(f["hue"], f["title"], "") for f in data["families"]] + [("--tr-bark", "general theory", "")])}
<h2>Where the corpus sits</h2>
<p class="ink2">{on} of the {total} corpus entries are on the map: their proofs rest on a blueprint
node, or a node's proof uses what they cite. {off} cite MathFin results in no relation the map
records. They are proved, and the import graph connects them to the library, but the program map
does not show them. The count is a ratchet (<code>corpus_off_blueprint</code>): it may fall and
may not rise.</p>
<div class="t-bars">{"".join(bars)}</div>
{legend([(v, label, "") for _, label, v in TREE_KINDS])}
<h2>Off the map, by cell</h2><p class="ink2">One dot per entry; hover for its id.</p>
<div class="t-bed">{plots}</div>
<h2>Frontier with a proved core</h2>
<p class="ink2">Frontier results that corpus entries already prove in part (the node's
<code>core</code>). They stay on the frontier until the whole statement is proved.</p>
<table class="t-table"><tbody>{partial_rows}</tbody></table>
<script type="application/json" id="tree-data">{payload}</script>
{"".join(f'<script src="{s}" defer></script>' for s in TREE_SCRIPTS)}"""
    (out / "tree.html").write_text(page("Program tree — MathFin", body, "", "tree.html",
                                        "The MathFin blueprint as a tree, with the corpus as "
                                        "its leaves."), encoding="utf-8")


LANDMARK_KEYS = ("decl", "title", "summary", "scope")


def load_landmarks(path: Path = LANDMARKS) -> list[dict]:
    """The curated landmark list; a malformed entry is an error, never a silently dropped card."""
    if not path.exists():
        return []
    entries = tomllib.loads(path.read_text(encoding="utf-8")).get("landmark", [])
    seen: set[str] = set()
    for i, e in enumerate(entries):
        where = f"{path} landmark #{i + 1} ({e.get('decl', '?')})"
        for k in LANDMARK_KEYS:
            if not isinstance(e.get(k), str) or not e[k].strip():
                raise ValueError(f"{where}: missing or empty string key `{k}`")
        also = e.get("also", [])
        if not isinstance(also, list) or not all(isinstance(a, str) and a for a in also):
            raise ValueError(f"{where}: `also` must be a list of declaration names")
        if extra := set(e) - set(LANDMARK_KEYS) - {"also"}:
            raise ValueError(f"{where}: unknown keys {sorted(extra)}")
        if e["decl"] in seen:
            raise ValueError(f"{where}: duplicate decl")
        seen.add(e["decl"])
    return entries


def landmark_path(idx: DeclIndex, decl: str, anchors: dict[str, str]) -> list[tuple[str, str]]:
    """The anchor declarations `decl` builds on, transitively through the uses recorded in the
    index, as (name, titles of the anchors it uses directly) from the nearest to the foundations.
    `anchors` maps a declaration name to its display title (blueprint nodes and curated
    landmarks). Edges are the transitive reduction of reachability among the anchors."""
    def reach(start: str) -> set[str]:
        seen: set[str] = set()
        stack = [start]
        while stack:
            d = idx.decls.get(stack.pop())
            if d is None:
                continue
            for u in d.uses:
                if u not in seen and u != start:
                    seen.add(u)
                    stack.append(u)
        return seen

    below = {a for a in reach(decl) if a in anchors}
    nodes = below | {decl}
    r = {a: reach(a) & nodes for a in nodes}
    kept = transitive_reduction(nodes, {(a, b) for a in nodes for b in r[a]})
    depth = {decl: 0}                       # longest chain from `decl`; foundations come last
    for a in sorted(nodes, key=lambda a: -len(r[a])):
        for x, y in kept:
            if x == a:
                depth[y] = max(depth.get(y, 0), depth.get(a, 0) + 1)
    order = sorted(below, key=lambda a: (depth.get(a, 0), anchors[a]))
    return [(a, ", ".join(sorted(anchors[y] for x, y in kept if x == a))) for a in order]


def _landmark_stmt(link: Linker, d: IndexedDecl) -> str:
    src = f"{REPO_URL}/blob/main/{library.module_path(d.module)}#L{d.line}"
    ns, _, last = d.name.rpartition(".")
    return (f'<article class="decl"><div class="decl-h"><span class="kind k-{d.kind}">{d.kind}</span>'
            f'<span class="dname"><span class="ns">{esc(ns)}.</span>{esc(last)}</span>'
            f'<a class="src" href="{src}">source</a>'
            f' <a class="src" href="{decl_url(d)}">module page</a></div>'
            f'<pre class="stmt-pre">{link.statement(d.type)}</pre></article>')


def landmark_card(site: Site, link: Linker, e: dict, anchors: dict[str, str]) -> str:
    d = site.idx.decls.get(e["decl"])
    aid = esc(e["decl"])
    if d is None or d.private:
        return (f'<section class="landmark missing" id="{aid}"><h2>{esc(e["title"])}</h2>'
                f'<p class="muted">Not in this build: <code>{esc(e["decl"])}</code> is not in the '
                f"declaration index this site was generated from.</p></section>")
    stmts = _landmark_stmt(link, d)
    for a in e.get("also", ()):
        c = site.idx.decls.get(a)
        stmts += (_landmark_stmt(link, c) if c is not None and not c.private else
                  f'<p class="muted">Companion <code>{esc(a)}</code> is not in this build.</p>')
    path = [(a, via) for a, via in landmark_path(site.idx, e["decl"], anchors)
            if a in site.idx.decls and not site.idx.decls[a].private]
    chain = ""
    if path:
        items = "".join(
            f'<li><a href="{decl_url(site.idx.decls[a])}">{esc(anchors[a])}</a>'
            + (f' <span class="muted">uses {esc(via)}</span>' if via else "") + "</li>"
            for a, via in path)
        chain = ('<h3>Builds on</h3><p class="muted">Blueprint results and other landmarks this '
                 "declaration uses, transitively, from the nearest to the foundations.</p>"
                 f"<ol class='lm-path'>{items}</ol>")
    return (f'<section class="landmark" id="{aid}"><h2>{esc(e["title"])}</h2>'
            f'<p class="lm-summary">{esc(e["summary"])}</p>'
            f'<p class="lm-scope"><strong>Not proved.</strong> {esc(e["scope"])}</p>'
            f'<h3>The Lean statement</h3>{stmts}{chain}</section>')


def build_landmarks(site: Site, out: Path, landmarks: list[dict], nodes_json: list[dict],
                    link: Linker) -> None:
    anchors = {n["name"]: n["title"] for n in nodes_json if n.get("name")}
    anchors.update({e["decl"]: e["title"] for e in landmarks})
    cards = "".join(landmark_card(site, link, e, anchors) for e in landmarks)
    toc = "".join(f'<li><a href="#{esc(e["decl"])}">{esc(e["title"])}</a></li>' for e in landmarks)
    body = f"""<h1>Landmarks</h1>
<p class="lede ink2">The headline results, one per line of the README's main results. Each shows the
statement exactly as Lean elaborates it, read from the declaration index, with what the statement
does not cover stated next to it. The prose above a statement is a reading aid; the statement is the claim.</p>
<ul class="toc">{toc}</ul>{cards}"""
    (out / "landmarks.html").write_text(
        page("Landmarks — MathFin", body, "", "landmarks.html",
             "The library's headline theorems with their exact Lean statements and scope."),
        encoding="utf-8")


def build_corpus(site: Site, out: Path) -> None:
    by_file: dict[str, list[tuple[str, dict]]] = defaultdict(list)
    for f, e in site.all_entries:
        by_file[Path(f).stem].append((f, e))
    order = sorted(by_file, key=lambda k: -len(by_file[k]))
    scale = max(len(v) for v in by_file.values())
    bars = "".join(status_bar(status_counts(by_file[k]), scale, k.replace("_", " "), f"#{k}")
                   for k in order)
    st = status_counts(site.all_entries)
    rows = "".join(f"<tr><td>{k.replace('_', ' ')}</td>" + "".join(
        f'<td class="n">{status_counts(by_file[k])[s]}</td>' for s in STATUS) + "</tr>" for k in order)
    lists = []
    for k in order:
        items = []
        for f, e in by_file[k]:
            mods = [m for m in library.library_imports(e["code"]["lean"]) if m in site.imports]
            where = " · ".join(f'<a href="{module_url(m)}">{esc(m.rsplit(".", 1)[-1])}</a>'
                               for m in mods[:3])
            s = e.get("metadata", {}).get("formalization_status", "full")
            items.append(f'<div class="entry" style="border-left-color:var({STATUS_VAR[s]})" '
                         f'data-text="{esc((e["id"] + " " + e["name"] + " " + e.get("description", "")).lower())}">'
                         f'<div class="eid">{esc(e["id"])} · {STATUS[s]}{" · " + where if where else ""}</div>'
                         f'<div class="ename">{esc(e["name"])}</div>'
                         f'<p>{esc(e.get("description", ""))}</p></div>')
        lists.append(f'<section id="{k}"><h3>{esc(k.replace("_", " "))} '
                     f'<span class="muted">{len(by_file[k])}</span></h3>{"".join(items)}</section>')
    body = f"""<h1>Corpus</h1>
<p class="lede ink2">{len(site.all_entries)} theorem statements, each a Lean snippet that restates a
result and checks it against the library. The status says how faithful the statement is to its
source: a <b>full statement</b> is the theorem itself, a <b>library wrapper</b> restates a Mathlib
result, a <b>reduced core</b> proves less than the source and its description says what.</p>
<div class="tiles">{"".join(f'<div class="tile"><div class="v">{st[s]}</div><div class="k">{STATUS[s]}</div></div>' for s in STATUS if st[s])}</div>
<h2>By area</h2>
{legend([(STATUS_VAR[s], STATUS[s], "sq") for s in STATUS if st[s]])}
<div class="panel bars">{bars}</div>
<details class="tableview"><summary>Table view</summary><table class="data"><thead><tr><th>File</th>
{"".join(f'<th>{STATUS[s]}</th>' for s in STATUS)}</tr></thead><tbody>{rows}</tbody></table></details>
<h2>Entries</h2>
<input class="filter" type="search" placeholder="Filter entries" data-filter="#entries">
<div id="entries">{"".join(lists)}</div>
<script>
document.querySelectorAll('input[data-filter]').forEach(box => box.addEventListener('input', () => {{
  const t = box.value.toLowerCase().trim(), root = document.querySelector(box.dataset.filter);
  root.querySelectorAll('.entry').forEach(e => e.hidden = t && !e.dataset.text.includes(t));
  root.querySelectorAll('section').forEach(s => s.hidden = ![...s.querySelectorAll('.entry')].some(e => !e.hidden));
}}));
</script>"""
    (out / "corpus.html").write_text(page("Corpus — MathFin", body, "", "corpus.html",
                                          "The MathFin corpus of formally verified theorem "
                                          "statements, by area and status."), encoding="utf-8")


def build_subjects(site: Site, out: Path) -> None:
    by_subject: dict[str, list[str]] = defaultdict(list)
    for m, d in site.docs.items():
        if m in site.imports:
            for c in d.subjects:
                by_subject[c].append(m)

    def chart(prefix: str) -> str:
        codes = sorted((c for c in by_subject if c.startswith(prefix)),
                       key=lambda c: -len(by_subject[c]))
        if not codes:
            return ""
        top = max(len(by_subject[c]) for c in codes)
        return '<div class="panel bars">' + "".join(
            f'<div class="bar-row"><div class="lab"><a href="#{esc(c.replace(" ", "-"))}">{esc(c)}</a> '
            f'<span class="muted">{esc(site.subjects.get(c, ""))}</span></div>'
            f'<div class="bar-track"><div class="bar-seg" style="width:{100 * len(by_subject[c]) / top:.2f}%;'
            f'background:var(--s1)" data-tip="{esc(c)} — {esc(site.subjects.get(c, ""))}: '
            f'{len(by_subject[c])} modules"></div></div><div class="val">{len(by_subject[c])}</div></div>'
            for c in codes) + "</div>"

    lists = []
    for code in sorted(by_subject, key=lambda c: (not c.startswith("JEL"), c)):
        mods = sorted(by_subject[code])
        lists.append(f'<details id="{esc(code.replace(" ", "-"))}"><summary><b>{esc(code)}</b> — '
                     f'{esc(site.subjects.get(code, ""))} <span class="muted">{len(mods)}</span></summary>'
                     "<ul>" + "".join(f'<li><a href="{module_url(m)}">{esc(site.title(m))}</a> '
                                      f'<span class="muted mono" style="font-size:.78rem">{esc(m)}</span></li>'
                                      for m in mods) + "</ul></details>")
    body = f"""<h1>Subjects</h1>
<p class="lede ink2">Where the library sits in economics and mathematics: the JEL and MSC2020 codes
its modules carry in their <code>Tags</code>, by the number of modules that carry each.</p>
<div class="grid2"><div><h2>Economics (JEL)</h2>{chart("JEL")}</div>
<div><h2>Mathematics (MSC2020)</h2>{chart("MSC")}</div></div>
<h2>By code</h2>{"".join(lists)}"""
    (out / "subjects.html").write_text(page("Subjects — MathFin", body, "", "subjects.html",
                                            "MathFin by JEL and MSC subject."), encoding="utf-8")


def build_references(site: Site, out: Path) -> None:
    cited: dict[str, list[str]] = defaultdict(list)
    for m, d in site.docs.items():
        if m in site.imports:
            for k in d.citations:
                cited[k].append(m)
    items = []
    for key, clean in doc_standard.bib_entries().items():
        bits = [esc(clean.get("author", "")), f"<em>{esc(clean.get('title', ''))}</em>",
                esc(clean.get("journal", "") or clean.get("publisher", "")
                    or clean.get("institution", "")), esc(clean.get("year", ""))]
        by = sorted(cited.get(key, ()))
        users = (" · cited in " + ", ".join(f'<a href="{module_url(m)}">{esc(site.title(m))}</a>'
                                            for m in by[:8])
                 + (f" and {len(by) - 8} more" if len(by) > 8 else "")) if by else ""
        items.append(f'<div class="entry" id="{esc(key)}"><div class="eid">{esc(key)}</div>'
                     f'<p>{", ".join(b for b in bits if b and b != "<em></em>")}'
                     f'<span class="muted" style="font-size:.84rem">{users}</span></p></div>')
    body = (f'<h1>References</h1><p class="lede ink2">One bibliography for the library and the '
            f'corpus, with the modules that cite each work.</p>{"".join(items)}')
    (out / "references.html").write_text(page("References — MathFin", body, "",
                                              "references.html"), encoding="utf-8")


def build(index_path: str | Path, out: str | Path, issues_path: str | Path | None = None) -> int:
    site = Site.load(index_path)
    out = Path(out)
    if out.exists():
        shutil.rmtree(out)
    for sub in ("m", "s", "assets"):
        (out / sub).mkdir(parents=True, exist_ok=True)
    for a in ASSETS.iterdir():
        shutil.copy(a, out / "assets" / a.name)
    nodes_json = json.loads(BLUEPRINT_NODES.read_text(encoding="utf-8")) \
        if BLUEPRINT_NODES.exists() else []
    frontier = tomllib.loads(FRONTIER.read_text(encoding="utf-8")).get("node", []) \
        if FRONTIER.exists() else []
    blueprint = nodes_json + [dict(f, leanOk=False) for f in frontier]

    landmarks = load_landmarks()
    public = {d.name: d for ds in site.decls.values() for d in ds}
    link = Linker(site.idx, "../", public)
    search = []
    mods = site.modules()
    for m in mods:
        build_module(site, out, m, link)
        for d in site.decls.get(m, ()):
            search.append({"n": d.name, "u": decl_url(d), "k": d.kind, "m": m,
                           "d": first_sentence(d.doc, 140),
                           "h": f"{d.name} {d.doc or ''} {d.type[:300]}".lower()})
    (out / "search.json").write_text(json.dumps(search, ensure_ascii=False), encoding="utf-8")
    by_sec: dict[str, list[str]] = defaultdict(list)
    for m in mods:
        if section_of(m):
            by_sec[section_of(m)].append(m)
    for sec, ms in by_sec.items():
        build_section(site, out, sec, ms)
    build_home(site, out, blueprint)
    build_blueprint(site, out, nodes_json, frontier)
    issues = ([json.loads(line) for line in Path(issues_path).read_text(encoding="utf-8").splitlines()
               if line.strip()] if issues_path else None)
    build_tree(site, out, nodes_json, frontier, issues)
    build_landmarks(site, out, landmarks, nodes_json, Linker(site.idx, "", public))
    build_corpus(site, out)
    build_subjects(site, out)
    build_references(site, out)
    (out / ".nojekyll").write_text("", encoding="utf-8")
    return len(mods)


def main() -> int:
    ap = argparse.ArgumentParser(prog="python3 -m tools.verify.docs_site")
    ap.add_argument("index")
    ap.add_argument("--out", default="site")
    ap.add_argument("--issues", help="issues and pull requests, one JSON object per line "
                    "(gh api …/issues --jq '.[] | {number,title,state,body,labels,is_pr}')")
    args = ap.parse_args()
    n = build(args.index, args.out, args.issues)
    print(f"docs site: {n} module pages in {args.out}/")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
