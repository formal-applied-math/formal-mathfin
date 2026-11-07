"""The blueprint and the issue tracker stay connected.

The network half (every open math issue names a node; every frontier node has an open
issue; every proved node has a delivery record) runs against GitHub in ``build.yml`` and
``blueprint-sync.yml`` (``python3 -m tools.verify.blueprint_issues check``). These tests
pin the checker's logic on fixtures, and check the parts that need no network: the
frontier file is well formed, the exported nodes match the Lean tags, and the generated
block of ``docs/blueprint.md`` is current.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from tools.verify import blueprint_issues as bi

REPO = Path(__file__).resolve().parent.parent


def _issue(number, body="", state="open", labels=("type:proof",), is_pr=False):
    return bi.Issue(number=number, title=f"issue {number}", state=state,
                    labels=frozenset(labels), body=body, is_pr=is_pr)


NODES = {
    "thm:a": bi.Node("thm:a", "A", "proved"),
    "thm:f": bi.Node("thm:f", "F", "frontier", uses=("thm:a",), statement="F holds."),
}


def test_named_nodes_parses_the_line() -> None:
    body = "Some text\n**Blueprint:** `thm:a`, thm:f\nmore"
    assert bi.named_nodes(body) == ["thm:a", "thm:f"]
    assert bi.named_nodes("- Blueprint: thm:a") == ["thm:a"]
    assert bi.named_nodes("no line here") == []
    assert bi.named_nodes("Blueprint: thm:<node-label>") == []  # template placeholder


def test_connected_program_has_no_problems() -> None:
    issues = [_issue(1, "Blueprint: thm:f"), _issue(2, "Blueprint: thm:a", state="closed")]
    assert bi.check(issues, NODES) == []


def test_each_invariant_fires() -> None:
    msgs = [p.message for p in bi.check([
        _issue(3, "nothing"),                              # open math issue, no node
        _issue(4, "Blueprint: thm:nope"),                  # unknown node
        _issue(5, "Blueprint: thm:f", state="closed"),     # frontier node, only closed issues
        _issue(6, "", labels=("type:proof", "tracking")),  # tracking: exempt
        _issue(7, "", labels=("type:refactor",)),          # not math work: exempt
    ], NODES)]
    assert any(m.startswith("#3 ") for m in msgs)
    assert any("#4 names `thm:nope`" in m for m in msgs)
    assert any("frontier node `thm:f`" in m and "#5" in m for m in msgs)
    assert any("proved node `thm:a`" in m for m in msgs)
    assert not any(m.startswith(("#6 ", "#7 ")) for m in msgs)


def test_a_pull_request_is_a_delivery_record() -> None:
    issues = [_issue(8, "Blueprint: thm:f"), _issue(9, "Blueprint: thm:a", is_pr=True,
                                                    state="closed")]
    assert bi.check(issues, NODES) == []


def test_every_frontier_node_grows_from_the_wood() -> None:
    nodes = dict(NODES)
    nodes["thm:g"] = bi.Node("thm:g", "G", "frontier", uses=("thm:f",), statement="G.")
    nodes["thm:h"] = bi.Node("thm:h", "H", "frontier", statement="H.",
                             ground="Mathlib: conditional expectation")
    assert bi.frontier_problems(nodes, {}) == []  # a frontier chain into the wood; a ground
    nodes["thm:x"] = bi.Node("thm:x", "X", "frontier", statement="X.")
    nodes["thm:y"] = bi.Node("thm:y", "Y", "frontier", uses=("thm:x",), statement="Y.")
    msgs = bi.frontier_problems(nodes, {})
    assert {m.split("`")[1] for m in msgs} == {"thm:x", "thm:y"}
    assert all("reach no proved node" in m for m in msgs)


def test_core_names_corpus_proofs() -> None:
    nodes = dict(NODES)
    nodes["thm:c"] = bi.Node("thm:c", "C", "frontier", uses=("thm:a",), statement="C.",
                             core=("e-full", "e-placeholder", "e-missing"))
    msgs = bi.frontier_problems(nodes, {"e-full": "full", "e-placeholder": "placeholder"})
    assert len(msgs) == 2
    assert any("`e-placeholder` is placeholder" in m for m in msgs)
    assert any("unknown corpus entry `e-missing`" in m for m in msgs)


def test_frontier_file_is_well_formed() -> None:
    nodes = bi.load_nodes(REPO / bi.NODES_JSON, REPO / bi.FRONTIER_TOML)
    assert bi.frontier_problems(nodes) == []


def test_exported_nodes_match_the_lean_tags() -> None:
    lean = set(re.findall(r'attribute \[blueprint "([^"]+)"',
                          (REPO / "MathFin/Blueprint.lean").read_text(encoding="utf-8")))
    exported = {n["label"] for n in json.loads((REPO / bi.NODES_JSON).read_text())}
    assert lean == exported, (
        f"docs/blueprint_nodes.json is stale (Lean only: {sorted(lean - exported)}, "
        f"JSON only: {sorted(exported - lean)}); re-run blueprint_export")


def test_rendered_blueprint_is_current() -> None:
    sys.path.insert(0, str(REPO / "tools"))
    import blueprint_render as br

    md = br.BLUEPRINT_MD.read_text(encoding="utf-8")
    raw = json.loads(br.NODES_JSON.read_text(encoding="utf-8"))
    for n in raw:
        n.setdefault("title", None)
    block = f"{br.BEGIN}\n{br.render(raw, bi.load_frontier(REPO / bi.FRONTIER_TOML))}\n{br.END}"
    assert block in md, "docs/blueprint.md is stale: run `python3 tools/blueprint_render.py`"
