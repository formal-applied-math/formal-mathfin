/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Theory of storage: convenience yield and the working/canonical storage kink

The **theory of storage** (Working 1949, Kaldor) models commodity stocks as
a kinked function of "availability" `A` (current stock plus expected supply):
below the kink stocks sit at an irreducible pipeline-fill floor `Sbar`; above
it they track the inverse demand-for-storage curve `f⁻¹`.

  `S(A) = max(Sbar, f⁻¹(A))`                         (working storage)
  `Y(A) = max(f⁻¹(A) − Sbar, 0)`                      (convenience yield)

The two are two faces of the same kink: `Y(A) = S(A) − Sbar` always. The
cost-of-carry identity ties the futures price `F` to the spot price `S`
through the finance/storage cost `C` net of the convenience-yield benefit:

  `F − S = C − Y(A)`

(convenience yield *reduces* net carry cost — high-yield, near-backwardation
markets have `Y(A)` large relative to `C`; this is the sign convention the
roadmap flagged for a double-check, and it is the standard one in the
literature: convenience yield is a benefit to the holder of physical stock,
so it subtracts from the holder's net financing cost, i.e. from `C`).

For an isoelastic demand-for-storage curve
`f⁻¹(A) = p_ref · (a_ref / A) ^ ε` (price elasticity `ε`, reference
availability `a_ref`, reference price `p_ref`), the kink point `A*` where
`f⁻¹(A*) = Sbar` is

  `A* = a_ref · (p_ref / Sbar) ^ {1/ε}`.

## Main results

* `workingStorage`, `convenienceYield`: the two kinked functions, generic in
  the inverse demand-for-storage curve `f⁻¹ : ℝ → ℝ`.
* `convenienceYield_eq_workingStorage_sub` : `Y(A) = S(A) − Sbar`.
* `forwardPrice`, `carry_identity` : `F − S = C − Y(A)`.
* `invDemandIsoelastic`, `kinkPoint`, `kinkPoint_spec` : the isoelastic
  demand-for-storage curve and the kink point solving `f⁻¹(A*) = Sbar`.
-/

@[expose] public section

namespace MathFin

open Real

/-! ### Working storage and convenience yield -/

/-- **Working storage**: stock sits at the irreducible floor `Sbar` when the
inverse demand-for-storage curve `f⁻¹` would call for less, else tracks it. -/
noncomputable def workingStorage (Sbar : ℝ) (invDemand : ℝ → ℝ) (A : ℝ) : ℝ :=
  max Sbar (invDemand A)

/-- **Convenience yield**: the benefit of holding physical stock above the
pipeline-fill floor, zero below it. -/
noncomputable def convenienceYield (Sbar : ℝ) (invDemand : ℝ → ℝ) (A : ℝ) : ℝ :=
  max (invDemand A - Sbar) 0

/-- The convenience yield is exactly how far working storage sits above the
floor `Sbar` — the two kinks are one and the same. -/
theorem convenienceYield_eq_workingStorage_sub (Sbar : ℝ) (invDemand : ℝ → ℝ) (A : ℝ) :
    convenienceYield Sbar invDemand A = workingStorage Sbar invDemand A - Sbar := by
  unfold convenienceYield workingStorage
  rw [max_comm Sbar (invDemand A), ← max_sub_sub_right, sub_self]

/-! ### Cost-of-carry identity -/

/-- **Forward price under cost of carry**: spot plus net financing/storage
cost `C`, minus the convenience-yield benefit `Y`. -/
noncomputable def forwardPrice (S C Y : ℝ) : ℝ := S + C - Y

/-- **Carry identity**: `F − S = C − Y(A)`. Convenience yield subtracts from
the carry cost `C`, consistent with it being a benefit to the holder of
physical stock (the standard theory-of-storage sign convention). -/
theorem carry_identity (S C Y : ℝ) : forwardPrice S C Y - S = C - Y := by
  unfold forwardPrice; ring

/-! ### Isoelastic demand for storage and its kink point -/

/-- **Isoelastic inverse demand for storage**: `f⁻¹(A) = p_ref · (a_ref/A)^ε`,
price elasticity `ε` against reference availability `a_ref` and price
`p_ref`. -/
noncomputable def invDemandIsoelastic (a_ref p_ref ε A : ℝ) : ℝ :=
  p_ref * (a_ref / A) ^ ε

/-- **Kink point**: the availability `A*` at which the isoelastic
demand-for-storage curve meets the pipeline-fill floor `Sbar`. -/
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
