/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.PayoffSlope
public import MathFin.BlackScholes.AmericanPut.Stopping.ContactTimeBoundary

/-! # Expected payoff slopes along actual optimal rules

The time-zero boundary limit and the global log-payoff slope bound justify
dominated convergence of difference quotients along the actual contact rules.

## Result

Public entry points include `normalized_putReward_eq_logPayoff`, `actualContactSlope`,
`actualContactSlope_bound`, `actualContactSlope_measurable`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

theorem normalized_putReward_eq_logPayoff (k h x : ℝ) (θ : (ℝ≥0 → ℝ) → ℝ≥0)
    (ω : ℝ≥0 → ℝ) :
    putReward brownian 1 k h (Real.sqrt 2) (Real.exp x) θ ω =
      Real.exp (-k*(θ ω : ℝ))*putPayoff
        (x+((k-h-1)*(θ ω : ℝ)+Real.sqrt 2*brownian (θ ω) ω)) := by
  unfold putReward MathFin.gbmValue putPayoff
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),show (2 : ℝ)/2 = 1 by norm_num,
    Real.exp_add x]

/-- The discounted put slope between `b` and `x`, evaluated at the actual contact time `s` of the
path `ω` and at the displacement `(k-h-1)*s + Real.sqrt 2*brownian s ω`. -/
noncomputable def actualContactSlope {k h : ℝ} (hk : 0 ≤ k) (b x : ℝ) (T : ℝ≥0)
    (ω : ℝ≥0 → ℝ) : ℝ :=
  let s := brownianUsualActualContactTime (h := h) hk x T ω
  discountedPutSlope k b x (s : ℝ) ((k-h-1)*(s : ℝ)+Real.sqrt 2*brownian s ω)

theorem actualContactSlope_bound {k h : ℝ} (hk : 0 ≤ k) (b x : ℝ) (T : ℝ≥0)
    (ω : ℝ≥0 → ℝ) : ‖actualContactSlope (h := h) hk b x T ω‖ ≤ 1 :=
  discountedPutSlope_bound hk (brownianUsualActualContactTime hk x T ω).coe_nonneg b x _

theorem actualContactSlope_measurable {k h : ℝ} (hk : 0 ≤ k) (b x : ℝ) (T : ℝ≥0) :
    @Measurable _ _ (completedMeasurableSpace gaussianLimit) inferInstance
      (actualContactSlope (h := h) hk b x T) := by
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  have hτ : Measurable (brownianUsualActualContactTime (h := h) hk x T) :=
    (brownianUsualActualContactRule (h := h) hk x T).measurable_time
  have hW : Measurable (fun ω => brownian (brownianUsualActualContactTime (h := h) hk x T ω) ω) :=
    brownian_completed_measurable.comp (hτ.prodMk measurable_id)
  have hs : Measurable (fun ω => (brownianUsualActualContactTime (h := h) hk x T ω : ℝ)) :=
    NNReal.continuous_coe.measurable.comp hτ
  unfold actualContactSlope discountedPutSlope putPayoff
  dsimp only
  fun_prop

theorem actualContactSlope_integrable {k h : ℝ} (hk : 0 ≤ k) (b x : ℝ) (T : ℝ≥0) :
    Integrable (actualContactSlope (h := h) hk b x T) (completedMeasure gaussianLimit) := by
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact (integrable_const (1 : ℝ)).mono'
    (actualContactSlope_measurable hk b x T).aestronglyMeasurable
    (Eventually.of_forall (actualContactSlope_bound hk b x T))

theorem actualContactSlope_eq_rewards {k h : ℝ} (hk : 0 ≤ k) (b x : ℝ) (T : ℝ≥0)
    (ω : ℝ≥0 → ℝ) :
    actualContactSlope (h := h) hk b x T ω =
      (putReward brownian 1 k h (Real.sqrt 2) (Real.exp x)
        (brownianUsualActualContactTime (h := h) hk x T) ω -
       putReward brownian 1 k h (Real.sqrt 2) (Real.exp b)
        (brownianUsualActualContactTime (h := h) hk x T) ω)/(x-b) := by
  rw [normalized_putReward_eq_logPayoff,normalized_putReward_eq_logPayoff]
  unfold actualContactSlope discountedPutSlope
  ring

theorem actualContactSlope_tendsto_ae {k h : ℝ} (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k)
    {T : ℝ≥0} (hT : 0 < T) :
    ∀ᵐ ω ∂completedMeasure gaussianLimit,
      Tendsto (fun x => actualContactSlope (h := h) hk.le (canonicalLogBoundary k h (T : ℝ)) x T ω)
        (𝓝[>] (canonicalLogBoundary k h (T : ℝ)))
        (𝓝 (-Real.exp (canonicalLogBoundary k h (T : ℝ)))) := by
  have hz : ∀ᵐ ω ∂completedMeasure gaussianLimit, brownian 0 ω = 0 :=
    isBrownianReal_brownian.eval_zero_ae_eq_zero
  filter_upwards [brownianUsualActualContactTime_tendsto_boundary hk hh hhk hT,hz] with ω hτ hω
  have ht : Tendsto (fun x => (brownianUsualActualContactTime (h := h) hk.le x T ω : ℝ))
      (𝓝 (canonicalLogBoundary k h (T : ℝ))) (𝓝 0) := by
    simpa only [Function.comp_def,NNReal.coe_zero] using (NNReal.continuous_coe.tendsto 0).comp hτ
  have hw : Tendsto (fun x => brownian (brownianUsualActualContactTime (h := h) hk.le x T ω) ω)
      (𝓝 (canonicalLogBoundary k h (T : ℝ))) (𝓝 0) := by
    simpa only [Function.comp_def,hω] using ((continuous_brownian ω).tendsto 0).comp hτ
  have hD := (ht.const_mul (k-h-1)).add (hw.const_mul (Real.sqrt 2))
  simp only [mul_zero,add_zero] at hD
  exact discountedPutSlope_tendsto (canonicalLogBoundary_neg hk hh hhk (by exact_mod_cast hT)) ht hD

theorem actualContactSlope_integral_tendsto {k h : ℝ} (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k)
    {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun x => ∫ ω, actualContactSlope (h := h) hk.le
      (canonicalLogBoundary k h (T : ℝ)) x T ω ∂completedMeasure gaussianLimit)
      (𝓝[>] (canonicalLogBoundary k h (T : ℝ)))
      (𝓝 (-Real.exp (canonicalLogBoundary k h (T : ℝ)))) := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  have hi := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (fun _ : (ℝ≥0 → ℝ) => (1 : ℝ))
    (Eventually.of_forall (fun x => (actualContactSlope_measurable (h := h) hk.le
      (canonicalLogBoundary k h (T : ℝ)) x T).aestronglyMeasurable))
    (Eventually.of_forall (fun x => Eventually.of_forall
      (actualContactSlope_bound (h := h) hk.le (canonicalLogBoundary k h (T : ℝ)) x T)))
    (integrable_const 1) (actualContactSlope_tendsto_ae hk hh hhk hT)
  simpa only [integral_const,probReal_univ,one_smul] using hi

end MathFin.BlackScholes.AmericanPut.Stopping
