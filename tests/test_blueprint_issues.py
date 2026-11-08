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
    nodes = bi.load_nodes(REPO / bi.NODES_JSON, REPO / bi.FRONTIER_TOML, REPO / bi.RETIRED_TOML)
    assert bi.frontier_problems(nodes) == []


RETIRED = {"thm:old": bi.Retired("thm:old", "thm:a", "a waypoint")}


def test_a_retired_label_is_history_when_closed_and_a_problem_when_open() -> None:
    closed = [_issue(1, "Blueprint: thm:old", state="closed"),
              _issue(2, "Blueprint: thm:old", state="closed", is_pr=True),
              _issue(3, "Blueprint: thm:f"), _issue(4, "Blueprint: thm:a", state="closed")]
    assert bi.check(closed, NODES, retired=RETIRED) == []
    problems = bi.check([_issue(5, "Blueprint: thm:old, thm:f"),
                         _issue(6, "Blueprint: thm:old", is_pr=True),
                         _issue(7, "Blueprint: thm:a", state="closed")], NODES, retired=RETIRED)
    msgs = [p.message for p in problems if p.issue is not None]
    assert len(msgs) == 2
    assert all("folded into `thm:a`" in m for m in msgs)
    assert {p.issue for p in problems if p.issue is not None} == {5, 6}
    # without the retired file the same name is just an unknown node
    assert any("not a blueprint node" in p.message
               for p in bi.check([_issue(8, "Blueprint: thm:old")], NODES))


def test_a_retired_label_is_never_a_node_and_folds_into_one() -> None:
    live = dict(NODES, **{"thm:old": bi.Node("thm:old", "Old", "proved")})
    msgs = [p.message for p in bi.check([_issue(1, "Blueprint: thm:f")], live, retired=RETIRED)]
    assert any("retired label `thm:old` is also a live node" in m for m in msgs)
    lost = {"thm:old": bi.Retired("thm:old", "thm:gone")}
    msgs = [p.message for p in bi.check([_issue(1, "Blueprint: thm:f")], NODES, retired=lost)]
    assert any("folded into `thm:gone`, which is not a node" in m for m in msgs)


def test_load_nodes_drops_a_retired_label_from_an_older_export(tmp_path) -> None:
    nodes_json = tmp_path / "nodes.json"
    nodes_json.write_text(json.dumps([{"label": "thm:a", "title": "A", "module": "MathFin.X"},
                                      {"label": "thm:old", "title": "O", "module": "MathFin.X"}]))
    retired = tmp_path / "retired.toml"
    retired.write_text('[[retired]]\nlabel = "thm:old"\nfolded_into = "thm:a"\nreason = "x"\n')
    frontier = tmp_path / "frontier.toml"
    frontier.write_text("")
    assert set(bi.load_nodes(nodes_json, frontier, retired)) == {"thm:a"}
    frontier.write_text('[[node]]\nlabel = "thm:old"\ntitle = "O"\nstatement = "s"\narea = "x"\n')
    try:
        bi.load_nodes(nodes_json, frontier, retired)
    except ValueError as e:
        assert "retired" in str(e)
    else:
        raise AssertionError("a frontier node may not reuse a retired label")


def _lean_tag_labels() -> set[str]:
    text = (REPO / "MathFin/Blueprint.lean").read_text(encoding="utf-8")
    return set(re.findall(r'^attribute \[blueprint "([^"]+)"', text, re.M))


def test_retired_file_is_consistent_with_the_tags_and_the_frontier() -> None:
    """Read from the Lean source, so it holds before docs/blueprint_nodes.json is re-exported."""
    retired = bi.load_retired(REPO / bi.RETIRED_TOML)
    assert retired, "docs/blueprint_retired.toml is empty or unreadable"
    tags = _lean_tag_labels()
    frontier = {n.label for n in bi.load_frontier(REPO / bi.FRONTIER_TOML)}
    assert not set(retired) & tags, f"retired labels still tagged: {sorted(set(retired) & tags)}"
    assert not set(retired) & frontier, "retired labels on the frontier"
    lost = [r.label for r in retired.values() if r.folded_into not in tags | frontier]
    assert not lost, f"retired labels folded into a label that is no node: {lost}"
    assert all(r.reason.strip() for r in retired.values()), "a retired label states no reason"


def test_frontier_uses_name_live_nodes() -> None:
    tags = _lean_tag_labels()
    frontier = bi.load_frontier(REPO / bi.FRONTIER_TOML)
    live = tags | {n.label for n in frontier}
    bad = [(n.label, u) for n in frontier for u in n.uses if u not in live]
    assert not bad, f"frontier `uses` naming no live node: {bad}"


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


def test_islands_are_components_apart_from_brownian_motion() -> None:
    from tools.verify.program_tree import islands

    nodes = [
        {"label": "def:brownian-motion", "uses": []},
        {"label": "thm:a", "uses": ["def:brownian-motion"]},
        {"label": "def:b", "uses": []},
        {"label": "thm:c", "uses": ["def:b"]},
        {"label": "thm:d", "uses": [], "leanOk": False},
        {"label": "thm:e", "uses": ["def:b", "thm:a"]},
        {"label": "def:f", "uses": []},
    ]
    assert islands(nodes) == [["def:f"]]
    assert islands(nodes[:4]) == [["def:b", "thm:c"]]
