"""The daemon response must carry the GOAL at each `sorry`, not just a count.

lean-interact's `Sorry` object already has `.goal` (the proof state at that position);
`parse_response` counted the sorries and dropped their goals, so every consumer of the
daemon was blind to intermediate proof states. These tests pin the surfaced shape and
its backward compatibility — the existing `sorry_count` / `success` keys are unchanged,
so callers that never look at `sorries` cannot notice.

Pure: a stub response object, no Lean process, no lean_interact import needed.
"""

from tools.verify.lean_repl import parse_response


class _Pos:
    def __init__(self, line, column):
        self.line = line
        self.column = column


class _Sorry:
    def __init__(self, goal, line=1, column=2):
        self.goal = goal
        self.start_pos = _Pos(line, column)


class _Response:
    def __init__(self, messages=None, sorries=None):
        self.messages = messages or []
        self.sorries = sorries or []


def test_sorry_goals_are_surfaced():
    r = parse_response(_Response(sorries=[_Sorry("x : ℝ\n⊢ 0 ≤ x")]))
    assert r["sorry_count"] == 1
    assert r["sorries"] == [{"line": 1, "column": 2, "goal": "x : ℝ\n⊢ 0 ≤ x"}]


def test_multiple_sorries_keep_their_order():
    r = parse_response(_Response(sorries=[_Sorry("⊢ A", 1, 0), _Sorry("⊢ B", 5, 4)]))
    assert [s["goal"] for s in r["sorries"]] == ["⊢ A", "⊢ B"]
    assert [s["line"] for s in r["sorries"]] == [1, 5]


def test_no_sorries_gives_an_empty_list_not_a_missing_key():
    r = parse_response(_Response())
    assert r["sorries"] == [] and r["sorry_count"] == 0
    assert r["success"] is True


def test_a_sorry_without_position_still_reports_its_goal():
    s = _Sorry("⊢ P")
    s.start_pos = None
    r = parse_response(_Response(sorries=[s]))
    assert r["sorries"] == [{"line": None, "column": None, "goal": "⊢ P"}]


def test_a_sorry_object_without_a_goal_attribute_is_tolerated():
    """Older lean-interact, or a REPL shape we have not seen: count it, do not crash."""
    class _Bare:
        pass
    r = parse_response(_Response(sorries=[_Bare()]))
    assert r["sorry_count"] == 1
    assert r["sorries"] == [{"line": None, "column": None, "goal": None}]


def test_existing_keys_are_unchanged_for_callers_that_ignore_sorries():
    class _Msg:
        def __init__(self, severity, data):
            self.severity = severity
            self.data = data
            self.start_pos = _Pos(3, 7)
    r = parse_response(_Response(messages=[_Msg("error", "boom"), _Msg("warning", "meh")],
                                 sorries=[_Sorry("⊢ P")]))
    assert r["success"] is False
    assert r["errors"] == ["line 3:7: boom"]
    assert r["warnings"] == ["line 3:7: meh"]
    assert r["sorry_count"] == 1


def test_a_non_list_sorries_field_does_not_break_the_response():
    resp = _Response()
    resp.sorries = None
    r = parse_response(resp)
    assert r["sorry_count"] == 0 and r["sorries"] == []
