/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualNormalization
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualStockConvexity

/-! # Physical-unit identification of the actual exercise boundary

The threshold is identified from payoff contact after exact stopping-price
normalization. No classical solution or boundary smoothness is assumed.

## Result

Public entry points include `brownianUsualExerciseBoundary_eq_scaled_canonical` and
`brownianUsualLogBoundary_normalization`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

theorem normalized_rates_admissible {r q σ : ℝ} (hr : 0 < r)
    (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ) :
    0 < normalizedRate r σ ∧ 0 ≤ normalizedRate q σ ∧
      normalizedRate q σ ≤ normalizedRate r σ := by
  unfold normalizedRate
  exact ⟨by positivity,by positivity,
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqr (by norm_num)) (sq_nonneg σ)⟩

theorem brownianUsualExerciseBoundary_normalization {K r q σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ)
    {τ : ℝ} (hτ : 0 < τ) :
    brownianUsualExerciseBoundary K r q σ τ.toNNReal =
      K*Real.exp (canonicalLogBoundary (normalizedRate r σ) (normalizedRate q σ) (σ^2/2*τ)) := by
  obtain ⟨hk,hh,hhk⟩ := normalized_rates_admissible hr hq hqr hσ
  let b := canonicalLogBoundary (normalizedRate r σ) (normalizedRate q σ)
  let B := K*Real.exp (b (σ^2/2*τ))
  have ht : 0 < σ^2/2*τ := by positivity
  have hBpos : 0 < B := mul_pos hK (Real.exp_pos _)
  have hBK : B ≤ K := by
    have he := mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (canonicalLogBoundary_neg hk hh hhk ht).le) hK.le
    simpa only [mul_one] using he
  have hcontact (S : ℝ) (hS : 0 < S) :
      brownianUsualAmericanPut K r q σ S τ.toNNReal = max (K-S) 0 ↔ S ≤ B := by
    rw [brownianUsualAmericanPut_normalization hK hr.le hσ hS,
      Real.coe_toNNReal _ hτ.le,← putPayoff_in_stock_units hK hS,mul_right_inj' hK.ne',
      canonicalPrice_contact_iff_logBoundary hk hh hhk ht]
    rw [← Real.exp_le_exp,Real.exp_log (div_pos hS hK),div_le_iff₀ hK]
    dsimp [B,b]
    rw [mul_comm K]
  let μ := completedMeasure gaussianLimit
  have hz : ∀ᵐ ω ∂μ, brownian 0 ω = 0 := isBrownianReal_brownian.eval_zero_ae_eq_zero
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  change exerciseThreshold μ brownianUsualFiltration brownian K r q σ τ.toNNReal = B
  have hmem : B ∈ exerciseSet μ brownianUsualFiltration brownian K r q σ τ.toNNReal := by
    refine ⟨hBpos.le,hBK,?_⟩
    have he := (hcontact B hBpos).mpr le_rfl
    rw [max_eq_left (sub_nonneg.mpr hBK)] at he
    convert! he using 1
  apply le_antisymm _ (le_csSup exerciseSet_bddAbove hmem)
  apply csSup_le ⟨0,zero_mem_exerciseSet brownian_completed_measurable hz hK.le hr.le⟩
  intro S hS
  by_cases hSpos : 0 < S
  · apply (hcontact S hSpos).mp
    exact hS.2.2.trans (max_eq_left (sub_nonneg.mpr hS.2.1)).symm
  · exact (le_of_not_gt hSpos).trans hBpos.le

theorem brownianUsualExerciseBoundary_eq_scaled_canonical {K r q σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ)
    {τ : ℝ} (hτ : 0 < τ) :
    brownianUsualExerciseBoundary K r q σ τ.toNNReal =
      K*canonicalStockBoundary (normalizedRate r σ) (normalizedRate q σ) (σ^2/2*τ) := by
  obtain ⟨hk,hh,hhk⟩ := normalized_rates_admissible hr hq hqr hσ
  rw [brownianUsualExerciseBoundary_normalization hK hr hq hqr hσ hτ,
    exp_canonicalLogBoundary hk hh hhk (by positivity)]

theorem brownianUsualLogBoundary_normalization {K r q σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ)
    {τ : ℝ} (hτ : 0 < τ) :
    Real.log (brownianUsualExerciseBoundary K r q σ τ.toNNReal/K) =
      canonicalLogBoundary (normalizedRate r σ) (normalizedRate q σ) (σ^2/2*τ) := by
  rw [brownianUsualExerciseBoundary_normalization hK hr hq hqr hσ hτ,
    mul_div_cancel_left₀ _ hK.ne',Real.log_exp]

end MathFin.BlackScholes.AmericanPut.Stopping
