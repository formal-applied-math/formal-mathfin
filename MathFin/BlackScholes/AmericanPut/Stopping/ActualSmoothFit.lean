/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.StoppedSlopeExpectation

/-! # Smooth fit for the actual American stopping price

Optimality supplies an upper bound on the price quotient using the same rule
at the boundary spot. Payoff domination supplies the lower bound. The two
quotients have the same limit, proving the actual boundary derivative.

## Result

Public entry points include `canonicalPrice_slope_le_contactSlope`,
`canonicalPrice_slope_ge_payoff`, `canonicalPrice_slope_tendsto_boundary`,
`canonicalPrice_smooth_fit`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

theorem canonicalPrice_slope_le_contactSlope {k h : ℝ} (hk : 0 ≤ k)
    {b x : ℝ} (hx : b < x) (T : ℝ≥0) :
    slope (fun y => canonicalPrice k h y (T : ℝ)) b x ≤
      ∫ ω, actualContactSlope (h := h) hk b x T ω ∂completedMeasure gaussianLimit := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  let θ := brownianUsualActualContactRule (h := h) hk x T
  have hθ : Measurable (brownianUsualActualContactTime (h := h) hk x T) := θ.measurable_time
  have hxI := canonicalReward_integrable (h := h) brownian_completed_measurable μ hk x hθ
  have hbI := canonicalReward_integrable (h := h) brownian_completed_measurable μ hk b hθ
  have hbV : (∫ ω, putReward brownian 1 k h (Real.sqrt 2) (Real.exp b)
      (brownianUsualActualContactTime (h := h) hk x T) ω ∂μ) ≤ canonicalPrice k h b (T : ℝ) :=
    expectedReward_le_canonicalPrice (h := h) hk b T θ
  have heI : (∫ ω, actualContactSlope (h := h) hk b x T ω ∂μ) =
      (canonicalPrice k h x (T : ℝ) - ∫ ω, putReward brownian 1 k h (Real.sqrt 2) (Real.exp b)
        (brownianUsualActualContactTime (h := h) hk x T) ω ∂μ)/(x-b) := by
    rw [integral_congr_ae (Eventually.of_forall (actualContactSlope_eq_rewards hk b x T)),
      integral_div,integral_sub hxI hbI,brownianUsualActualContactRule_optimal hk x T]
  rw [heI]
  simp only [slope,vsub_eq_sub,smul_eq_mul,← div_eq_inv_mul]
  exact div_le_div_of_nonneg_right (by linarith) (sub_pos.mpr hx).le

theorem canonicalPrice_slope_ge_payoff {k h : ℝ} (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k)
    {t x : ℝ} (ht : 0 < t) (hx : canonicalLogBoundary k h t < x) :
    slope putPayoff (canonicalLogBoundary k h t) x ≤
      slope (fun y => canonicalPrice k h y t) (canonicalLogBoundary k h t) x := by
  have he := (canonicalPrice_contact_iff_logBoundary hk hh hhk ht).mpr
    (le_rfl : canonicalLogBoundary k h t ≤ canonicalLogBoundary k h t)
  simp only [slope,vsub_eq_sub,smul_eq_mul,← div_eq_inv_mul,he]
  exact div_le_div_of_nonneg_right
    (sub_le_sub_right (canonicalPrice_bounds hk.le x t).1 _) (sub_pos.mpr hx).le

theorem canonicalPrice_slope_tendsto_boundary {k h : ℝ} (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k)
    {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (slope (fun y => canonicalPrice k h y (T : ℝ)) (canonicalLogBoundary k h (T : ℝ)))
      (𝓝[>] (canonicalLogBoundary k h (T : ℝ)))
      (𝓝 (-Real.exp (canonicalLogBoundary k h (T : ℝ)))) := by
  have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
  have hlo :=
      (putPayoff_hasDerivAt_neg (canonicalLogBoundary_neg hk hh hhk hTR)).tendsto_slope.mono_left
    (nhdsGT_le_nhdsNE (canonicalLogBoundary k h (T : ℝ)))
  have hhi := actualContactSlope_integral_tendsto hk hh hhk hT
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact canonicalPrice_slope_ge_payoff hk hh hhk hTR hx
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact canonicalPrice_slope_le_contactSlope hk.le
        (show canonicalLogBoundary k h (T : ℝ) < x from hx) T

/-- The exact one-sided derivative required by `DividendPutSolution.smooth_fit`,
now proved for the actual stopping price without a classical-solution premise. -/
theorem canonicalPrice_smooth_fit {k h t : ℝ} (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k)
    (ht : 0 < t) :
    HasDerivWithinAt (fun x => canonicalPrice k h x t) (-Real.exp (canonicalLogBoundary k h t))
      (Ici (canonicalLogBoundary k h t)) (canonicalLogBoundary k h t) := by
  have hs := canonicalPrice_slope_tendsto_boundary hk hh hhk (Real.toNNReal_pos.mpr ht)
  simp only [Real.coe_toNNReal _ ht.le] at hs
  exact ((hasDerivWithinAt_iff_tendsto_slope' (by simp : canonicalLogBoundary k h t ∉
    Ioi (canonicalLogBoundary k h t))).mpr hs).Ici_of_Ioi

theorem zeroDividend_canonicalPrice_smooth_fit {k t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    HasDerivWithinAt (fun x => canonicalPrice k 0 x t) (-Real.exp (canonicalLogBoundary k 0 t))
      (Ici (canonicalLogBoundary k 0 t)) (canonicalLogBoundary k 0 t) :=
  canonicalPrice_smooth_fit hk le_rfl hk.le ht

end MathFin.BlackScholes.AmericanPut.Stopping
