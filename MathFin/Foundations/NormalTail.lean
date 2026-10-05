/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.NormalQuantile
public import MathFin.RiskMeasures.RockafellarUryasev

/-! # The left tail of the standard normal

Three facts about `Φ` and the standard normal density `φ` used to bound option prices far from
the money: `Φ(x) → 0` as `x → −∞`, the Mills bound `−x·Φ(x) ≤ φ(x)`, and `φ ≤ 1`.
-/

@[expose] public section

namespace MathFin

open Filter Topology ProbabilityTheory MeasureTheory

/-- `Φ` tends to `0` at `−∞`. -/
theorem tendsto_Phi_atBot : Tendsto Phi atBot (𝓝 0) :=
  cdf_gaussianReal_zero_one ▸ tendsto_cdf_atBot (gaussianReal 0 1)

/-- `Φ` tends to `1` at `+∞`. -/
theorem tendsto_Phi_atTop : Tendsto Phi atTop (𝓝 1) :=
  cdf_gaussianReal_zero_one ▸ tendsto_cdf_atTop (gaussianReal 0 1)

/-- **The Mills bound**, in the form `−x·Φ(x) ≤ φ(x)`: the stop-loss value
`𝔼[(Z + x)⁺] = φ(x) + x·Φ(x)` of a standard normal `Z` is nonnegative. -/
theorem neg_mul_Phi_le_gaussianPDFReal (x : ℝ) : -x * Phi x ≤ gaussianPDFReal 0 1 x := by
  have h0 : 0 ≤ ∫ y, max (y - -x) 0 * gaussianPDFReal 0 1 y :=
    integral_nonneg fun y ↦ mul_nonneg (le_max_right _ _) (gaussianPDFReal_nonneg _ _ _)
  rw [integral_max_sub_mul_gaussianPDFReal, gaussianPDFReal_zero_one_neg, Phi_neg] at h0
  linarith

/-- The standard normal density is at most `1`. -/
theorem gaussianPDFReal_zero_one_le_one (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  exact mul_le_one₀ (inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by nlinarith [Real.pi_gt_three])))
    (Real.exp_pos _).le (Real.exp_le_one_iff.2
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg x)) zero_le_two))

end MathFin
