/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.FTAPMultiState

/-!
# Triangle arbitrage: the cross-rate identity from the FTAP

Three currencies `A, B, C` with exchange rates in cyclic order: `S_AB` units of `B` per unit
of `A`, `S_BC` units of `C` per unit of `B`, and `S_CA` units of `A` per unit of `C`. The
round trip `A → B → C → A` turns one unit of `A` into `S_AB · S_BC · S_CA` units of `A`.

The market is three **conversion trades**, each a vector of net holdings in `(A, B, C)`:
`A → B` is `(−1, S_AB, 0)`, `B → C` is `(0, −1, S_BC)`, `C → A` is `(S_CA, 0, −1)`
(`triangleTrades`). Trading is frictionless: any real multiple of a trade may be taken, a
negative multiple being the reverse conversion at the reciprocal rate; there is no bid–ask
spread and no transaction cost. An **arbitrage** is a combination of trades whose net
holding is non-negative in every currency and positive in one.

That is `HasArbitrage_multi_state` of `Foundations/FTAPMultiState.lean`, with the currencies
as the coordinates in place of states of the world. The multi-state FTAP is a statement
about a subspace of `ℝ³` and the standard simplex (Stiemke's alternative), so it applies
whatever the coordinates mean; its strictly positive `q` is then a vector of consistent
values of the three currencies in a common unit.

`TriangleNoArb` is defined as the absence of such an arbitrage, and the cross-rate identity
is a theorem: for positive `S_AB`, `S_BC`, `TriangleNoArb ↔ S_AB · S_BC · S_CA = 1`
(`triangleNoArb_iff`). The forward direction is the FTAP's backward half (no arbitrage ⟹
positive currency values `q` with `q_A = S_AB q_B`, `q_B = S_BC q_C`, `q_C = S_CA q_A`); the
reverse direction prices with `q ∝ (S_AB S_BC, S_BC, 1)` and applies the forward half.

## Results

* `triangleTrades`, `TriangleNoArb`
* `prod_eq_one_of_triangleNoArb` — no arbitrage forces `S_AB · S_BC · S_CA = 1` (any signs)
* `triangleNoArb_iff` — for positive `S_AB`, `S_BC`: no arbitrage ⟺ `S_AB · S_BC · S_CA = 1`
* `triangleNoArb_solve_third` — for positive `S_AB`, `S_BC`, exactly one `S_CA` allows no
  arbitrage, namely `1 / (S_AB · S_BC)`
-/

@[expose] public section

namespace MathFin

/-- The three **conversion trades** of the currency triangle, as net holdings in
`(A, B, C)`: row `0` converts one `A` into `S_AB` units of `B`, row `1` one `B` into `S_BC`
units of `C`, row `2` one `C` into `S_CA` units of `A`. -/
def triangleTrades (S_AB S_BC S_CA : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![-1, S_AB, 0], ![0, -1, S_BC], ![S_CA, 0, -1]]

/-- **Triangle no-arbitrage**: no frictionless combination of the three conversion trades has
a net holding that is non-negative in every currency and positive in one. The cross-rate
identity `S_AB · S_BC · S_CA = 1` is the theorem `triangleNoArb_iff`. -/
def TriangleNoArb (S_AB S_BC S_CA : ℝ) : Prop :=
  ¬ HasArbitrage_multi_state (triangleTrades S_AB S_BC S_CA)

/-- **No arbitrage forces the cross-rate identity**, whatever the signs of the rates. The
multi-state FTAP gives strictly positive currency values `q` pricing each trade at zero:
`q_A = S_AB q_B`, `q_B = S_BC q_C`, `q_C = S_CA q_A`, so `q_A = S_AB S_BC S_CA q_A`. -/
theorem prod_eq_one_of_triangleNoArb {S_AB S_BC S_CA : ℝ}
    (h : TriangleNoArb S_AB S_BC S_CA) : S_AB * S_BC * S_CA = 1 := by
  obtain ⟨q, hq, -, hfair⟩ := hasEMM_multi_of_not_hasArbitrage (triangleTrades S_AB S_BC S_CA) h
  have h0 : q 0 * -1 + q 1 * S_AB + q 2 * 0 = 0 := by
    simpa [triangleTrades, Fin.sum_univ_three] using hfair 0
  have h1 : q 0 * 0 + q 1 * -1 + q 2 * S_BC = 0 := by
    simpa [triangleTrades, Fin.sum_univ_three] using hfair 1
  have h2 : q 0 * S_CA + q 1 * 0 + q 2 * -1 = 0 := by
    simpa [triangleTrades, Fin.sum_univ_three] using hfair 2
  refine mul_left_cancel₀ (hq 0).ne' ?_
  linear_combination h0 + S_AB * h1 + S_AB * S_BC * h2

/-- **Triangle no-arbitrage is the cross-rate identity.** For positive rates `S_AB`, `S_BC`,
the three conversion trades allow no arbitrage iff `S_AB · S_BC · S_CA = 1`. Forward:
`prod_eq_one_of_triangleNoArb`. Reverse: the currency values `(S_AB S_BC, S_BC, 1)` are
strictly positive and price every trade at zero, so they normalise to an EMM
(`hasEMM_multi_of_pos_dual`) and the forward FTAP excludes arbitrage. -/
theorem triangleNoArb_iff {S_AB S_BC S_CA : ℝ} (hab : 0 < S_AB) (hbc : 0 < S_BC) :
    TriangleNoArb S_AB S_BC S_CA ↔ S_AB * S_BC * S_CA = 1 := by
  refine ⟨prod_eq_one_of_triangleNoArb, fun hprod ↦ noArbitrage_of_emm_multi _ ?_⟩
  refine hasEMM_multi_of_pos_dual (q := ![S_AB * S_BC, S_BC, 1]) (fun i ↦ ?_) (fun k ↦ ?_)
  · fin_cases i
    exacts [mul_pos hab hbc, hbc, one_pos]
  · fin_cases k <;> simp [triangleTrades, Fin.sum_univ_three] <;> linarith

/-- **No arbitrage determines the third rate**: given positive `S_AB`, `S_BC`, exactly one
`S_CA` leaves the triangle without arbitrage, namely `S_CA = 1 / (S_AB · S_BC)`. -/
theorem triangleNoArb_solve_third {S_AB S_BC : ℝ} (hab : 0 < S_AB) (hbc : 0 < S_BC) :
    ∃! S_CA : ℝ, TriangleNoArb S_AB S_BC S_CA := by
  have hne : S_AB * S_BC ≠ 0 := (mul_pos hab hbc).ne'
  refine ⟨1 / (S_AB * S_BC), (triangleNoArb_iff hab hbc).mpr (mul_one_div_cancel hne),
    fun S_CA h ↦ ?_⟩
  rw [eq_div_iff hne]
  linear_combination prod_eq_one_of_triangleNoArb h

end MathFin
