"""The research-problem catalogue names real blueprint nodes and real Lean statements.

A problem the library cannot state yet is kept, with the frontier nodes it needs; a problem
stated in Lean names its theorem in ``MathFinFrontier/`` through its blueprint node.
"""

from __future__ import annotations

from tools.verify import blueprint_issues as bi
from tools.verify import research_problems as rp


def test_catalogue_is_connected_to_the_blueprint():
    assert rp.problems(rp.load(), bi.load_nodes()) == []


def _node(label, status="frontier", lean=""):
    return bi.Node(label=label, title=label, status=status, lean=lean)


def _record(**ls):
    return {"id": "MF-OP-999", "formalization": {"lean_statement": ls}}


def test_checker_flags_broken_links():
    nodes = {"def:a": _node("def:a"), "def:done": _node("def:done", status="proved"),
             "thm:q": _node("thm:q", lean="MathFinFrontier.q")}
    stated = {"MathFinFrontier.q"}
    ok = [_record(status="blocked", blueprint="thm:q", needs=["def:a"], lean=None),
          _record(status="stated", blueprint="thm:q", needs=[], lean="MathFinFrontier.q")]
    assert rp.problems(ok, nodes, stated) == []
    bad = {
        "not a node": _record(status="blocked", needs=["def:missing"]),
        "already proved": _record(status="blocked", needs=["def:done"]),
        "names nothing": _record(status="blocked", needs=[]),
        "not a theorem": _record(status="stated", blueprint="thm:q", lean="MathFinFrontier.r"),
        "is not one of": _record(status="open"),
    }
    for fragment, rec in bad.items():
        errs = rp.problems([rec], nodes, stated)
        assert any(fragment in e for e in errs), (fragment, errs)


def test_needs_ranking_counts_blocked_problems():
    recs = [{"id": i, "formalization": {"lean_statement": {"needs": n}}}
            for i, n in [("A", ["def:x", "def:y"]), ("B", ["def:x"]), ("C", [])]]
    assert rp.needs_ranking(recs) == [("def:x", ["A", "B"]), ("def:y", ["A"])]
