/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.Forwards.FxForwardParity
public import MathFin.Models.Forwards.TheoryOfStorage

/-!
# Contango, backwardation and basis convergence

The cost-of-carry forward of a commodity spot `S` with financing rate `r` and convenience
yield `δ` is `F(T) = S·e^{(r−δ)T}` — the library's `fxForward S r δ`, where the yield sits in
the slot of the foreign rate of covered interest parity. The forward is derived, not posited,
in that FX reading: `covered_interest_parity` gets it from `forward_price_from_no_arbitrage` and
`uncovered_interest_parity` from `expected_terminal_eq_forward`. The commodity reading is the
same formula, not a separate derivation: `δ` is a continuous multiplicative yield, whereas
`TheoryOfStorage.lean`'s convenience yield `Y` is an additive amount paid at delivery.
`continuousYieldAmount` converts one to the other (the delivery-date value
`S e^{rT}(1 − e^{−δT})` of the yield) and `storageForward_continuousYield_iff` proves that the
storage no-arbitrage forward with that additive yield is `fxForward S r δ T`. The forward is the
deterministic-rate curve; futures and forwards agree only under deterministic rates (`thm:futures-forward-convexity` is the gap).
This module adds the qualitative market structure that formula
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

* `continuousYieldAmount`: the additive delivery-date amount `S e^{rT}(1 − e^{−δT})` that a
  continuous yield `δ` is worth.

The other results state facts about the existing `fxForward`.

## Main results

* `storageForward_continuousYield_iff` : the storage forward with zero cost and the additive yield
  `continuousYieldAmount S r δ T` has zero value exactly at `F = fxForward S r δ T`: the bridge
  from the continuous yield to `TheoryOfStorage`'s additive one.
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

open scoped Topology
open Filter

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

/-! ### The term structure -/

/-- **A rising term structure is a full-carry curve**: `T ↦ fxForward S r δ T` is strictly
increasing exactly when the financing rate exceeds the convenience yield. A strictly monotone
curve is in contango at maturity `1`, which forces `δ < r`; conversely a positive carry
differential scales `Real.exp` monotonicity up by the positive spot. -/
theorem fxForward_strictMono_iff (S r δ : ℝ) (hS : 0 < S) :
    StrictMono (fxForward S r δ) ↔ δ < r := by
  constructor
  · intro h
    exact (fxForward_contango_iff S r δ 1 hS one_pos).mp (by
      simpa only [fxForward, mul_zero, Real.exp_zero, mul_one] using h zero_lt_one)
  · intro hδ
    have hc : 0 < r - δ := sub_pos.mpr hδ
    exact fun a b hab ↦
      mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hab hc)) hS

/-- **A falling term structure is an inverted curve**: `T ↦ fxForward S r δ T` is strictly
decreasing exactly when the convenience yield exceeds the financing rate — the mirror image of
`fxForward_strictMono_iff`, with the negative carry differential reversing `Real.exp`
monotonicity. -/
theorem fxForward_strictAnti_iff (S r δ : ℝ) (hS : 0 < S) :
    StrictAnti (fxForward S r δ) ↔ r < δ := by
  constructor
  · intro h
    exact (fxForward_backwardation_iff S r δ 1 hS one_pos).mp (by
      simpa only [fxForward, mul_zero, Real.exp_zero, mul_one] using h zero_lt_one)
  · intro hδ
    have hc : r - δ < 0 := sub_neg.mpr hδ
    exact fun a b hab ↦
      mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left hab hc)) hS

/-- **A flat term structure means the rates agree**: the forward curve is constant at the spot
exactly when the financing rate equals the convenience yield — the third case of the
trichotomy, at every maturity at once. -/
theorem fxForward_const_iff (S r δ : ℝ) (hS : 0 < S) :
    (∀ T : ℝ, fxForward S r δ T = S) ↔ r = δ := by
  constructor
  · intro h
    exact (fxForward_eq_spot_iff S r δ 1 hS one_pos).mp (h 1)
  · intro h T
    rw [fxForward, h, sub_self, zero_mul, Real.exp_zero, mul_one]

/-! ### Basis convergence -/

/-- **The basis vanishes at zero maturity**: the spot-minus-forward basis `S − F(T)` is zero
at `T = 0`, where the forward equals the spot whatever the rates. -/
theorem fxForward_basis_zero (S r δ : ℝ) :
    S - fxForward S r δ 0 = 0 := by
  rw [fxForward, mul_zero, Real.exp_zero, mul_one, sub_self]

/-- **The basis converges to zero**: the spot-minus-forward basis `S − F(T)` tends to `0` as
the maturity tends to `0⁺` — continuity of the forward curve at the spot, restricted to the
positive maturities. -/
theorem fxForward_basis_tendsto_zero (S r δ : ℝ) :
    Tendsto (fun T : ℝ ↦ S - fxForward S r δ T) (𝓝[>] 0) (𝓝 0) := by
  have hval : S - fxForward S r δ 0 = 0 := fxForward_basis_zero S r δ
  have hcont : Continuous fun T : ℝ ↦ S - fxForward S r δ T := by
    unfold fxForward
    fun_prop
  simpa only [hval] using
    (hcont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

/-! ### The bridge to the additive convenience yield -/

/-- **The additive amount a continuous yield is worth at delivery**: a commodity of spot `S`
financed at `r` and yielding `δ` continuously has carry `S e^{rT} − S e^{(r−δ)T}` over `[0, T]`,
that is `S e^{rT}(1 − e^{−δT})`, the amount `Y` of `TheoryOfStorage.lean` paid at delivery. -/
noncomputable def continuousYieldAmount (S r δ T : ℝ) : ℝ :=
  S * Real.exp (r * T) * (1 - Real.exp (-(δ * T)))

/-- **The storage forward with a continuous yield is the cost-of-carry forward.** In a
finite-state market with state prices `q` and bond price `e^{−rT}`, the commodity at spot `S`
priced as the claim on `S_T + Y` with the additive yield `Y = continuousYieldAmount S r δ T` and
no storage cost (`storageForward_from_no_arbitrage` at `C = 0`), the forward struck at `F` has
zero value exactly when `F = fxForward S r δ T = S e^{(r−δ)T}`: the additive convenience yield
of the theory of storage and the continuous yield of the cost-of-carry forward are one carry. -/
theorem storageForward_continuousYield_iff {ι : Type*} (s : Finset ι) (q S_T : ι → ℝ)
    (S r δ T F : ℝ) (h_bond : ∑ i ∈ s, q i = Real.exp (-(r * T)))
    (h_carry : ∑ i ∈ s, q i * (S_T i - 0 + continuousYieldAmount S r δ T) = S) :
    (∑ i ∈ s, q i * (S_T i - F) = 0) ↔ F = fxForward S r δ T := by
  have hexp : Real.exp ((r - δ) * T) = Real.exp (r * T) * Real.exp (-(δ * T)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hcarry : S / Real.exp (-(r * T)) + 0 - continuousYieldAmount S r δ T
      = fxForward S r δ T := by
    rw [continuousYieldAmount, fxForward, hexp, Real.exp_neg (r * T), div_inv_eq_mul]
    ring
  rw [storageForward_from_no_arbitrage s q S_T _ S 0 _ F (Real.exp_pos _).ne' h_bond h_carry,
    hcarry]

end MathFin
