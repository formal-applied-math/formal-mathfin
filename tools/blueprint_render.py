#!/usr/bin/env python3
"""Regenerate the mermaid spine in docs/blueprint.md from extracted blueprint JSON.

Pipeline (the graph is generated ground truth, never hand-drawn):

  1. inside the verify container:
       lake build MathFin.Blueprint blueprint_export
       lake exe blueprint_export MathFin.Blueprint > docs/blueprint_nodes.json
  2. host-side:
       python3 tools/blueprint_render.py        # rewrites the marked block

Edges come from `Architect.collectUsed` over the *proof terms* (transitive,
passing through untagged helpers) — see MathFinTools/Blueprint.lean. A node
with no inferred edge is a genuine root: if the prose claims a dependency the
graph does not show, the prose is wrong, not the graph (this caught
`bs_pde_holds` being self-contained algebra on day one).

The not-yet-formalized frontier (no Lean declarations to tag) is declared in
docs/blueprint_frontier.toml, grouped by area in the graph and visibly
⏳-classed. Below the graph, a generated table lists every node with a live
link to the issues and pull requests naming it (`Blueprint: <label>` in their
body — the one place the link is stored; tools/verify/blueprint_issues.py
checks both directions).
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))
from tools.verify.blueprint_issues import issues_url, load_frontier  # noqa: E402

NODES_JSON = REPO / "docs" / "blueprint_nodes.json"
BLUEPRINT_MD = REPO / "docs" / "blueprint.md"

BEGIN = "<!-- BEGIN GENERATED SPINE (tools/blueprint_render.py — do not hand-edit) -->"
END = "<!-- END GENERATED SPINE -->"

def mermaid_id(label: str) -> str:
    """`thm:ito-formula-l2` → `itoFormulaL2` (mermaid-safe camelCase)."""
    stem = label.split(":", 1)[-1]
    parts = re.split(r"[^A-Za-z0-9]+", stem)
    return parts[0] + "".join(p.capitalize() for p in parts[1:] if p)


def topo_order(nodes: list[dict]) -> list[dict]:
    """Kahn topological sort (deps first), label-sorted within a layer —
    stable output for clean git diffs."""
    by_label = {n["label"]: n for n in nodes}
    indeg = {n["label"]: 0 for n in nodes}
    for n in nodes:
        for u in n["uses"]:
            if u in indeg:
                indeg[n["label"]] += 1
    order, layer = [], sorted(l for l, d in indeg.items() if d == 0)
    while layer:
        nxt = []
        for l in layer:
            order.append(by_label[l])
            for m in nodes:
                if l in m["uses"]:
                    indeg[m["label"]] -= 1
                    if indeg[m["label"]] == 0:
                        nxt.append(m["label"])
        layer = sorted(set(nxt))
    if len(order) != len(nodes):  # cycle should be impossible for proof terms
        raise SystemExit("cycle detected in blueprint graph — refusing to render")
    return order


def node_class(n: dict) -> str:
    if not n.get("leanOk", True):
        return "partial"
    if not n.get("module", "").startswith("MathFin"):
        return "upstream"
    return "proved"


def render(nodes: list[dict], frontier: list) -> str:
    lines = ["```mermaid", "graph TD"]
    ordered = topo_order(nodes)
    ids = {n["label"]: mermaid_id(n["label"]) for n in nodes}
    for n in ordered:
        title = n.get("title") or n["label"]
        lines.append(f'  {ids[n["label"]]}["{title}"]:::{node_class(n)}')
    by_area: dict[str, list] = {}
    for f in frontier:
        ids[f.label] = mermaid_id(f.label)
        by_area.setdefault(f.area or "other", []).append(f)
    for area in sorted(by_area):
        lines.append(f'  subgraph frontier_{mermaid_id(area)}["⏳ frontier · {area}"]')
        for f in sorted(by_area[area], key=lambda f: f.label):
            lines.append(f'    {ids[f.label]}["{f.title}"]:::frontier')
        lines.append("  end")
    lines.append("")
    for n in ordered:
        for u in sorted(n["uses"]):
            if u in ids:
                lines.append(f"  {ids[u]} --> {ids[n['label']]}")
    for f in sorted(frontier, key=lambda f: f.label):
        for u in f.uses:
            if u in ids:
                lines.append(f"  {ids[u]} --> {ids[f.label]}")
    lines += [
        "",
        "  classDef proved fill:#d4edda,stroke:#28a745,color:#111;",
        "  classDef upstream fill:#d9e8f6,stroke:#1f6fb2,color:#111;",
        "  classDef partial fill:#ffe5d0,stroke:#d9534f,color:#111;",
        "  classDef frontier fill:#fff3cd,stroke:#d39e00,color:#111;",
        "```",
        "",
        "| node | status | issues and pull requests |",
        "|---|---|---|",
    ]
    status = {"proved": "✅", "upstream": "✅ upstream", "partial": "🚧"}
    for n in ordered:
        lines.append(f"| `{n['label']}` {n.get('title') or ''} | {status[node_class(n)]} "
                     f"| [linked]({issues_url(n['label'])}) |")
    for f in sorted(frontier, key=lambda f: f.label):
        lines.append(f"| `{f.label}` {f.title} | ⏳ | [linked]({issues_url(f.label)}) |")
    return "\n".join(lines)


def main() -> None:
    raw = json.loads(NODES_JSON.read_text())
    # the exe emits titles only in the Node; carry them through if present
    for n in raw:
        n.setdefault("title", None)
    md = BLUEPRINT_MD.read_text()
    if BEGIN not in md or END not in md:
        raise SystemExit(f"markers not found in {BLUEPRINT_MD}; refusing to guess")
    frontier = load_frontier(REPO / "docs" / "blueprint_frontier.toml")
    block = f"{BEGIN}\n{render(raw, frontier)}\n{END}"
    new = re.sub(re.escape(BEGIN) + r".*?" + re.escape(END), lambda _: block, md, flags=re.S)
    BLUEPRINT_MD.write_text(new)
    print(f"rendered {len(raw)} nodes + {len(frontier)} frontier into {BLUEPRINT_MD}")


if __name__ == "__main__":
    main()
