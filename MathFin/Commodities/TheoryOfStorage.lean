/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Theory of storage: convenience yield and the canonical-storage price kink

The **theory of storage** (Kaldor 1939, Working 1949) models the commodity spot
price as a kinked function of "availability" `A` (current stock plus expected
supply). For availability below the kink point `A*` (scarcity) the price tracks
the inverse demand-for-storage curve `f⁻¹(A)`, which falls as availability
rises; at and above `A*` storage is profitable and the market sits at the
investment-regime price floor `Sbar = E[S_{t+1}] − C`:

  `S(A) = max(Sbar, f⁻¹(A))`                         (canonical-storage price)
  `Y(A) = max(f⁻¹(A) − Sbar, 0)`                      (convenience yield)

The convenience yield is positive exactly where scarcity bites — below the
kink (`A` small, so `f⁻¹(A)` would exceed `Sbar`) — and zero at and above it.
The two are two faces of the same kink: `Y(A) = S(A) − Sbar` always. Taking
the futures price to be `F = Sbar + C` (it is not derived here), the
cost-of-carry identity — the spot price `S(A)` plus the finance/storage cost `C`
net of the convenience-yield benefit — is that identity rearranged:

  `F − S(A) = C − Y(A)`

(convenience yield *reduces* net carry cost — high-yield, near-backwardation
markets have `Y(A)` large relative to `C`. This is the standard sign
convention in the literature: convenience yield is a benefit to the holder
of physical stock, so it subtracts from the holder's net financing cost,
i.e. from `C`).

For an isoelastic demand-for-storage curve
`f⁻¹(A) = p_ref · (a_ref / A) ^ ε` (flexibility `ε = −d ln p / d ln A`,
reference availability `a_ref`, reference price `p_ref`), the kink point
`A*` where `f⁻¹(A*) = Sbar` is

  `A* = a_ref · (p_ref / Sbar) ^ {1/ε}`.

## Main results

* `storageSpotPrice`, `convenienceYield`: the two kinked functions, generic
  in the inverse demand-for-storage curve `f⁻¹ : ℝ → ℝ`.
* `convenienceYield_eq_storageSpotPrice_sub` : `Y(A) = S(A) − Sbar`.
* `carry_identity_at_availability` : `(Sbar + C) − S(A) = C − Y(A)`, the
  cost-of-carry identity at the kink functions with `F` taken to be `Sbar + C`
  (`convenienceYield_eq_storageSpotPrice_sub` rearranged; no futures pricing is
  derived).
* `invDemandIsoelastic`, `kinkPoint`, `kinkPoint_spec` : the isoelastic
  demand-for-storage curve and the kink point solving `f⁻¹(A*) = Sbar`.

## References

* N. Kaldor, "Speculation and economic stability", *Review of Economic Studies* 7 (1939), 1–27.
* H. Working, "The theory of price of storage", *American Economic Review* 39 (1949),
  1254–1262.
-/

@[expose] public section

namespace MathFin

/-! ### Canonical-storage spot price and convenience yield -/

/-- **Canonical-storage spot price**: the price sits at the investment-regime
floor `Sbar` when the inverse demand-for-storage curve `f⁻¹` would call for
less, else tracks it. -/
noncomputable def storageSpotPrice (Sbar : ℝ) (invDemand : ℝ → ℝ) (A : ℝ) : ℝ :=
  max Sbar (invDemand A)

/-- **Convenience yield**: positive exactly where scarcity pushes the
demand-for-storage price above the investment-regime floor, zero at and
above it. -/
noncomputable def convenienceYield (Sbar : ℝ) (invDemand : ℝ → ℝ) (A : ℝ) : ℝ :=
  max (invDemand A - Sbar) 0

/-- The convenience yield is exactly how far the canonical-storage price sits
above the floor `Sbar` — the two kinks are one and the same. -/
theorem convenienceYield_eq_storageSpotPrice_sub (Sbar : ℝ) (invDemand : ℝ → ℝ) (A : ℝ) :
    convenienceYield Sbar invDemand A = storageSpotPrice Sbar invDemand A - Sbar := by
  unfold convenienceYield storageSpotPrice
  rw [max_comm Sbar (invDemand A), ← max_sub_sub_right, sub_self]

/-! ### Cost-of-carry identity -/

/-- **Carry identity at a given availability**: with the futures price taken to
be `F = Sbar + C` (cost of carry off the investment-regime floor), the carry
spread against the canonical-storage spot price is exactly `C − Y(A)` —
convenience yield subtracts from the carry cost `C`, the standard
theory-of-storage sign convention (convenience yield is a benefit to the
holder of physical stock). No futures pricing is derived here: `F` is an input,
and the identity is `convenienceYield_eq_storageSpotPrice_sub` rearranged. -/
theorem carry_identity_at_availability (Sbar C : ℝ) (invDemand : ℝ → ℝ) (A : ℝ) :
    (Sbar + C) - storageSpotPrice Sbar invDemand A = C - convenienceYield Sbar invDemand A := by
  rw [convenienceYield_eq_storageSpotPrice_sub]; ring

/-! ### Isoelastic demand for storage and its kink point -/

/-- **Isoelastic inverse demand for storage**: `f⁻¹(A) = p_ref · (a_ref/A)^ε`,
flexibility `ε = −d ln p / d ln A` against reference availability `a_ref` and
price `p_ref`. -/
noncomputable def invDemandIsoelastic (a_ref p_ref ε A : ℝ) : ℝ :=
  p_ref * (a_ref / A) ^ ε

/-- **Kink point**: the availability `A*` at which the isoelastic
demand-for-storage curve meets the investment-regime floor `Sbar`. -/
noncomputable def kinkPoint (a_ref p_ref Sbar ε : ℝ) : ℝ :=
  a_ref * (p_ref / Sbar) ^ (1 / ε)

/-- **Kink-point equation**: `f⁻¹(A*) = Sbar`, i.e. `kinkPoint` really is where
the isoelastic demand-for-storage curve crosses the floor. -/
theorem kinkPoint_spec (a_ref p_ref Sbar ε : ℝ)
    (ha : 0 < a_ref) (hp : 0 < p_ref) (hS : 0 < Sbar) (hε : ε ≠ 0) :
    invDemandIsoelastic a_ref p_ref ε (kinkPoint a_ref p_ref Sbar ε) = Sbar := by
  unfold invDemandIsoelastic kinkPoint
  have hx : (0:ℝ) ≤ p_ref / Sbar := le_of_lt (div_pos hp hS)
  have step1 : a_ref / (a_ref * (p_ref / Sbar) ^ (1 / ε)) = (Sbar / p_ref) ^ (1 / ε) := by
    rw [div_mul_eq_div_div, div_self (ne_of_gt ha), one_div, ← Real.inv_rpow hx, inv_div]
  have step2 : ((Sbar / p_ref) ^ (1 / ε)) ^ ε = Sbar / p_ref := by
    rw [← Real.rpow_mul (le_of_lt (div_pos hS hp)), one_div, inv_mul_cancel₀ hε, Real.rpow_one]
  rw [step1, step2]
  field_simp

end MathFin
