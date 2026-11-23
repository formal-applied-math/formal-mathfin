/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.Forwards.FxForwardParity

/-!
# Contango, backwardation and basis convergence

The cost-of-carry forward of a commodity spot `S` with financing rate `r` and convenience
yield `δ` is `F(T) = S·e^{(r−δ)T}` — the library's `fxForward S r δ`, where the yield sits in
the slot of the foreign rate of covered interest parity (the same formula the dividend-yield
machinery of `BlackScholes/Dividends.lean` carries at the effective rate `r − q`). The forward
itself is derived, not posited: `covered_interest_parity` gets it from
`forward_price_from_no_arbitrage` and `uncovered_interest_parity` from
`expected_terminal_eq_forward`. This module adds the qualitative market structure that formula
induces, for `S > 0`:

* **Contango** (forward above spot, a normal market): `F(T) > S ⟺ δ < r`, at any positive
  maturity; **backwardation** (forward below spot, an inverted market): `F(T) < S ⟺ r < δ`;
  at `r = δ` the forward meets the spot. The carry differential `r − δ` decides all three.
* **Term structure**: `T ↦ F(T)` is strictly increasing exactly when `r > δ` (a full-carry
  curve), strictly decreasing exactly when `r < δ`, and flat exactly when `r = δ`.
* **Basis convergence**: the basis `b(T) = S − F(T)` (the spot-minus-forward sign convention of
  Hull ch. 3 and of the issue; `TheoryOfStorage.lean`'s carry identity `F − S = C − Y` writes
  the same gap with the opposite sign) vanishes at `T = 0` and tends to `0` as `T → 0⁺`.

No hypothesis beyond `0 < S` (and `0 < T` for the pointwise sign facts, since `F(0) = S`
regardless of the rates): everything is `Real.exp` monotonicity.

## Main definitions

None: the module states facts about the existing `fxForward`.

## Main results

* `fxForward_eq_spot_iff` : `fxForward S r δ T = S ↔ r = δ` for `0 < S`, `0 < T`.
* `fxForward_contango_iff` : `S < fxForward S r δ T ↔ δ < r` for `0 < S`, `0 < T`.
* `fxForward_backwardation_iff` : `fxForward S r δ T < S ↔ r < δ` for `0 < S`, `0 < T`.
* `fxForward_strictMono_iff` : `StrictMono (fxForward S r δ) ↔ δ < r` for `0 < S`.
* `fxForward_strictAnti_iff` : `StrictAnti (fxForward S r δ) ↔ r < δ` for `0 < S`.
* `fxForward_const_iff` : the curve is flat (`∀ T, fxForward S r δ T = S`) exactly when
  `r = δ`, for `0 < S`.
* `fxForward_basis_zero` : `S − fxForward S r δ 0 = 0`.
* `fxForward_basis_tendsto_zero` : `T ↦ S − fxForward S r δ T` tends to `0` as `T → 0⁺`.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 3; ch. 5; ch. 18
* [N. Kaldor, *Speculation and economic stability*][Kaldor1939]
* [H. Working, *The theory of price of storage*][Working1949]

## Tags

contango, backwardation, basis, basis convergence, term structure, cost of carry, convenience
yield, normal market, inverted market, MSC 91G20, JEL G13, JEL Q02
-/

@[expose] public section

namespace MathFin

/-! ### The pointwise sign structure -/

/-- **Forward meets spot exactly at equal rates**: for a positive spot and a positive maturity,
`F(T) = S` holds exactly when the financing rate equals the convenience yield. At `T = 0` the
forward equals the spot for every `r` and `δ`, which is `fxForward_basis_zero`. -/
theorem fxForward_eq_spot_iff (S r δ T : ℝ) (hS : 0 < S) (hT : 0 < T) :
    fxForward S r δ T = S ↔ r = δ := by
  rw [fxForward, mul_eq_left₀ hS.ne', Real.exp_eq_one_iff, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hT.ne'
  · intro h
    exact Or.inl h

/-- **Contango**: for a positive spot and a positive maturity the forward is above the spot
exactly when the financing rate exceeds the convenience yield — the carry differential
`r − δ` is positive. A normal market. -/
theorem fxForward_contango_iff (S r δ T : ℝ) (hS : 0 < S) (hT : 0 < T) :
    S < fxForward S r δ T ↔ δ < r := by
  rw [fxForward, lt_mul_iff_one_lt_right hS, Real.one_lt_exp_iff]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact sub_pos.mp h1
    · exact absurd h2 (not_lt.mpr hT.le)
  · intro h
    exact mul_pos (sub_pos.mpr h) hT

/-- **Backwardation**: for a positive spot and a positive maturity the forward is below the spot
exactly when the convenience yield exceeds the financing rate — the carry differential
`r − δ` is negative, the high-convenience-yield case of the theory of storage. An inverted
market. -/
theorem fxForward_backwardation_iff (S r δ T : ℝ) (hS : 0 < S) (hT : 0 < T) :
    fxForward S r δ T < S ↔ r < δ := by
  rw [fxForward, mul_lt_iff_lt_one_right hS, Real.exp_lt_one_iff]
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact absurd h2 (not_lt.mpr hT.le)
    · exact sub_neg.mp h1
  · intro h
    exact mul_neg_of_neg_of_pos (sub_neg.mpr h) hT

end MathFin
