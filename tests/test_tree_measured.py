"""The measured tree's data (tools/verify/program_tree.py): heights, islands, towers, phantoms."""

from __future__ import annotations

from tools.verify import chain_reach as cr
from tools.verify import program_tree as pt

INF = float("inf")


def _n(label, s="proved", d=None, m=None, u=(), p="valuation", b="trees", **kw):
    return dict(l=label, t=label, s=s, d=d, m=m, u=list(u), p=p, b=b, e=kw.pop("e", 0), i=[], **kw)


def test_heights_follow_hops_and_frontier_inherits() -> None:
    nodes = [_n("a", d="A"), _n("b", d="B"), _n("f", s="frontier", u=["a"]),
             _n("g", s="frontier", u=["b"])]
    pt.assign_hops(nodes, {"A": 2, "B": INF})
    by = {n["l"]: n["hp"] for n in nodes}
    assert by == {"a": 2, "b": None, "f": 3, "g": None}


def test_towers_collapse_to_one_node() -> None:
    nodes = [_n("x", d="X", m="MathFin.T.A.One", e=2, u=["root"]),
             _n("y", d="Y", m="MathFin.T.A.Two", e=3, u=["x"]),
             _n("z", d="Z", m="MathFin.Other", u=["y", "x"])]
    pt.assign_hops(nodes, {"X": 4, "Y": 2, "Z": 3})
    tw = [dict(key="t", title="T", modules=["MathFin.T.A"])]
    mods = ["MathFin.T.A.One", "MathFin.T.A.Two", "MathFin.T.A.Two.Deep", "MathFin.Other"]
    out = pt.collapse_towers(nodes, mods, tw)
    tower = next(n for n in out if n["l"] == "tower:t")
    assert len(out) == 2 and tower["tw"] == 3 and tower["hp"] == 2 and tower["e"] == 5
    assert tower["d"] == "Y" and tower["u"] == ["root"]
    assert next(n for n in out if n["l"] == "z")["u"] == ["tower:t"]


def test_islands_ring_unless_reached_or_declared() -> None:
    nodes = [_n("a", d="A", m="MathFin.M.A", b="diffusions"), _n("b", d="B", m="MathFin.M.B", b="model-free"),
             _n("c", d="C", m="MathFin.M.C", b="term"), _n("ok", d="O", m="MathFin.M.O")]
    pt.assign_hops(nodes, {"A": INF, "B": INF, "C": INF, "O": 2})
    st = [dict(modules=["MathFin.M.C"], reason="a law", socket="x", title="Laws")]
    kinds = {"valuation": "limb"}
    isl = pt.float_islands(nodes, kinds, reached={"a"}, standalone=st)
    ring = {c["title"]: c["ring"] for c in isl}
    assert len(isl) == 3 and "ok" not in sum((c["nodes"] for c in isl), [])
    assert ring["Laws"] is False                      # declared
    assert sum(ring.values()) == 1                    # b: reached a, declared c, only b rings
    assert next(n for n in nodes if n["l"] == "ok").get("isl") is None


SPINE, BS = "MathFin.Pricing.Market", "MathFin.Models.BlackScholes.Call"


def _d(name, module, kind="theorem", type_="", uses=()):
    return dict(name=name, module=module, kind=kind, type=type_, uses=list(uses), private=False)


def test_phantom_sits_between_its_ends_at_its_hop_with_its_gain() -> None:
    lib = [_d("MathFin.Market", SPINE, "structure", "Type"),
           _d("MathFin.bsCall", BS, "def", "ℝ → ℝ"),
           _d("MathFin.bsDelta", BS, "def", "ℝ → ℝ"),
           _d("MathFin.bsDelta_eq", BS, type_="MathFin.bsDelta 0 = MathFin.bsCall 0",
              uses=("MathFin.bsDelta", "MathFin.bsCall", "MathFin.a", "MathFin.b"))]
    conn = _d("MathFinFrontier.bs_market", "MathFinFrontier.X",
              type_="∀ (M : MathFin.Market), MathFin.bsCall 0 = 0 ∧ MathFin.bsDelta 0 = 0")
    reach = cr.compute(lib)
    nodes = [_n("m", d="MathFin.Market", m=SPINE), _n("c", d="MathFin.bsCall", m=BS)]
    gains = cr.connector_gains(lib, [conn])
    ph = pt.phantoms(nodes, [("conn", conn)], reach, {d["name"]: d["module"] for d in lib},
                     gains)["conn"]
    assert set(ph["ends"]) == {"m", "c"} and ph["hp"] == 1 and ph["gain"] == gains[conn["name"]]
    assert ph["gain"] >= 1
