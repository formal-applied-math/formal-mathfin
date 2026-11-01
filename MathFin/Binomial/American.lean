/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Binomial.Model

/-!
# American option pricing in the binomial tree

For a binomial tree with up-factor `u`, down-factor `d`, per-step rate `r`,
under the no-arbitrage condition `d < e^r < u`, an American option with
intrinsic payoff `g : ℝ → ℝ` (e.g. `S ↦ max(S − K, 0)` for a call) has price

  `V_n(S) = max(g(S), e^{-r} · (p · V_{n-1}(uS) + (1 − p) · V_{n-1}(dS)))`

with `V_0(S) = g(S)`, where `p = crrUpProb u d r`. `n` counts steps remaining.

This is the exercise-everywhere case of the tree's one recursion `bermudanPrice`
(`Binomial/Model.lean`); its dominance and supermartingale clauses
(`le_bermudanPrice`, `bermudanPrice_supermartingale`), its Snell-envelope characterization
(`Binomial/SnellEnvelope.lean`) and its monotonicity in the exercise set, hence the
European ≤ American ordering (`Binomial/Bermudan.lean`), all apply to it.

This file defines `americanPrice`, with the one-step Bellman equation `americanPrice_succ`.
-/

@[expose] public section

namespace MathFin

open Real

/-- American option price in the binomial tree: the Bellman recursion taking, at each
step, the maximum of immediate exercise (`g S`) and the discounted expected continuation,
i.e. `bermudanPrice` with early exercise at every step. `n` counts steps remaining; `g` is
the intrinsic payoff function. -/
noncomputable def americanPrice (u d r : ℝ) (g : ℝ → ℝ) : ℕ → ℝ → ℝ :=
  bermudanPrice Set.univ u d r g

/-- At maturity (`n = 0`), the American price equals the intrinsic payoff. -/
@[simp]
lemma americanPrice_zero (u d r : ℝ) (g : ℝ → ℝ) (S : ℝ) :
    americanPrice u d r g 0 S = g S := rfl

/-- One-step Bellman: `V_{n+1}(S) = max(g(S), one-period continuation)`. -/
lemma americanPrice_succ (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    americanPrice u d r g (n + 1) S = max (g S)
      (binomialOptionPriceOnePeriod u d r
        (americanPrice u d r g n (S * u))
        (americanPrice u d r g n (S * d))) :=
  bermudanPrice_succ_of_mem (Set.mem_univ _) u d r g S

end MathFin
