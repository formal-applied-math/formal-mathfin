"""Chain reach (tools/verify/chain_reach.py) on a small fixture: statements make edges, nothing
else does, and a definitional restatement is not a bridge."""

from __future__ import annotations

from tools.verify import chain_reach as cr


def _d(name, module, kind="theorem", type_="", uses=(), private=False):
    return {"name": name, "module": module, "kind": kind, "type": type_, "uses": list(uses),
            "private": private}


SPINE = "MathFin.Pricing.Market"
BS = "MathFin.Models.BlackScholes.Call"
CHOICE = "MathFin.Choice.Utility.VonNeumannMorgenstern"


def _lib(bridge_uses=("MathFin.a", "MathFin.b")):
    return [
        _d("MathFin.Market", SPINE, "structure", "Type"),
        _d("MathFin.Market.IsPricingMeasure", SPINE, "def", "MathFin.Market → Prop"),
        _d("MathFin.bsCall", BS, "def", "ℝ → ℝ"),
        _d("MathFin.bsDelta", BS, "def", "ℝ → ℝ"),
        _d("MathFin.expectedUtility", CHOICE, "def", "ℝ → ℝ"),
        # a bridge: the market's price is the formula (its proof uses two other lemmas)
        _d("MathFin.price_eq_bsCall", BS,
           type_="∀ (M : MathFin.Market), M.IsPricingMeasure → MathFin.bsCall 0 = 0",
           uses=("MathFin.Market", "MathFin.bsCall", *bridge_uses)),
        _d("MathFin.bsDelta_eq", BS, type_="MathFin.bsDelta 0 = MathFin.bsCall 0",
           uses=("MathFin.bsDelta", "MathFin.bsCall", "MathFin.a", "MathFin.b")),
        _d("MathFin.eu_pos", CHOICE, type_="0 ≤ MathFin.expectedUtility 0",
           uses=("MathFin.expectedUtility", "MathFin.a", "MathFin.b")),
    ]


def test_hops_follow_statements() -> None:
    r = cr.compute(_lib())
    assert r.hops["MathFin.price_eq_bsCall"] == 1          # mentions the spine itself
    assert r.hops["MathFin.bsDelta_eq"] == 2               # through the formula it is about
    assert r.hops["MathFin.eu_pos"] == float("inf")        # choice: nothing joins it
    assert r.sockets == {"diffusions"}                      # dot notation resolves


def test_a_definitional_restatement_is_not_a_bridge() -> None:
    r = cr.compute(_lib(bridge_uses=()))
    assert r.hops["MathFin.bsDelta_eq"] == float("inf")
    assert cr.compute(_lib(bridge_uses=()), guard=False).hops["MathFin.bsDelta_eq"] == 2


def test_a_connector_would_join_and_says_how_much() -> None:
    k = _d("MathFinFrontier.utility_state_price", "MathFinFrontier.Choice",
           type_="∀ (M : MathFin.Market), M.IsPricingMeasure → MathFin.expectedUtility 0 = 0")
    assert cr.compute(_lib(), connectors=[k]).hops["MathFin.eu_pos"] == 2
    assert cr.connector_gains(_lib(), [k]) == {"MathFinFrontier.utility_state_price": 1, "*": 1}


def test_the_ratchet_reads_reach_as_debt(tmp_path) -> None:
    """R3 enters the ratchet as the per-mille beyond three hops, sockets as families without
    one: both rise when the library comes apart, so neither may."""
    import json

    from tools.verify import ratchet, taxonomy

    p = tmp_path / "decl-index.json"
    p.write_text(json.dumps({"decls": _lib()}), encoding="utf-8")
    m = ratchet.reach_metrics(p)
    assert m["chain_beyond_r3_permille"] == 333               # eu_pos of three theorems
    assert m["families_without_socket"] == len(taxonomy.families()) - 1
