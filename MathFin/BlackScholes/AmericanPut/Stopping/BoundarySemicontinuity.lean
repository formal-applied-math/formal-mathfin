/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.StrictExerciseGeometry
public import Mathlib.Topology.Semicontinuity.Basic

/-! # One-sided continuity of the actual financial exercise threshold

Continuity of the price in maturity makes the threshold upper semicontinuous.
Together with its monotonicity this proves continuity from shorter maturities.
Continuity from longer maturities is not asserted by this argument.

## Result

Public entry points include `threshold_upperSemicontinuous`, `threshold_continuousWithinAt_left`,
`brownianExerciseBoundary_upperSemicontinuous`, `brownianUsualExerciseBoundary_upperSemicontinuous`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

section General

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
  {K r q σ : ℝ}

theorem threshold_upperSemicontinuous (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    UpperSemicontinuous (exerciseThreshold P 𝓕 W K r q σ) := by
  intro T u hu
  have hB := threshold_bounds (P := P) (𝓕 := 𝓕) (q := q) (σ := σ) (T := T)
    hW hzero hK hr
  by_cases hKu : K < u
  · exact Eventually.of_forall (fun t =>
      (threshold_bounds (P := P) (𝓕 := 𝓕) (q := q) (σ := σ) (T := t)
        hW hzero hK hr).2.trans_lt hKu)
  have huK : u ≤ K := le_of_not_gt hKu
  have hu0 : 0 ≤ u := (hB.1.trans hu.le)
  have hgap : K-u < americanPutValue P 𝓕 W K r q σ u T := by
    have hlo := payoff_le_value (P := P) (𝓕 := 𝓕) (q := q) (σ := σ) (T := T)
      hW hzero hK hr hu0
    rw [max_eq_left (sub_nonneg.mpr huK)] at hlo
    apply lt_of_le_of_ne hlo
    intro he
    have hm : u ∈ exerciseSet P 𝓕 W K r q σ T := ⟨hu0,huK,he.symm⟩
    exact (not_le.mpr hu) (le_csSup exerciseSet_bddAbove hm)
  have hc := americanPutValue_continuous_horizon (P := P) (𝓕 := 𝓕) (q := q) (σ := σ)
    hW hpaths hK hr hu0
  filter_upwards [(hc.tendsto T).eventually (Ioi_mem_nhds hgap)] with t ht
  apply lt_of_not_ge
  intro hut
  have hm : u ∈ exerciseSet P 𝓕 W K r q σ t := by
    rw [exerciseSet_eq_interval hW hzero hK hr]
    exact ⟨hu0,hut⟩
  exact ht.ne' hm.2.2

theorem threshold_continuousWithinAt_left (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) (hK : 0 ≤ K) (hr : 0 ≤ r) (T : ℝ≥0) :
    ContinuousWithinAt (exerciseThreshold P 𝓕 W K r q σ) (Iic T) T := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ha.trans_le (threshold_antitone_horizon hW hzero hK hr ht)
  · intro a ha
    exact (threshold_upperSemicontinuous hW hpaths hzero hK hr T a ha).filter_mono
      nhdsWithin_le_nhds

end General

theorem brownianExerciseBoundary_upperSemicontinuous {K r q σ : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) : UpperSemicontinuous (brownianExerciseBoundary K r q σ) :=
  threshold_upperSemicontinuous measurable_brownian_uncurry continuous_brownian
    isBrownianReal_brownian.eval_zero_ae_eq_zero hK hr

theorem brownianUsualExerciseBoundary_upperSemicontinuous {K r q σ : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) : UpperSemicontinuous (brownianUsualExerciseBoundary K r q σ) := by
  let μ := completedMeasure gaussianLimit
  have hz : ∀ᵐ ω ∂μ, brownian 0 ω = 0 := isBrownianReal_brownian.eval_zero_ae_eq_zero
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact threshold_upperSemicontinuous (P := μ) (𝓕 := brownianUsualFiltration)
    brownian_completed_measurable continuous_brownian hz hK hr

theorem canonicalStockBoundary_antitone {k h : ℝ} (hk : 0 ≤ k) :
    Antitone (canonicalStockBoundary k h) := by
  let μ := completedMeasure gaussianLimit
  have hz : ∀ᵐ ω ∂μ, brownian 0 ω = 0 := isBrownianReal_brownian.eval_zero_ae_eq_zero
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  intro s t hst
  exact threshold_antitone_horizon (P := μ) (𝓕 := brownianUsualFiltration)
    brownian_completed_measurable hz (by norm_num) hk (Real.toNNReal_mono hst)

theorem canonicalStockBoundary_upperSemicontinuous {k h : ℝ} (hk : 0 ≤ k) :
    UpperSemicontinuous (canonicalStockBoundary k h) := by
  have hh := (brownianUsualExerciseBoundary_upperSemicontinuous
    (K := 1) (q := h) (σ := Real.sqrt 2) (by norm_num) hk).comp
    (show Continuous (fun t : ℝ => t.toNNReal) by fun_prop)
  convert! hh using 1

theorem canonicalStockBoundary_continuousWithinAt_left {k h : ℝ} (hk : 0 ≤ k) (T : ℝ) :
    ContinuousWithinAt (canonicalStockBoundary k h) (Iic T) T := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ha.trans_le (canonicalStockBoundary_antitone hk ht)
  · intro a ha
    exact (canonicalStockBoundary_upperSemicontinuous hk T a ha).filter_mono nhdsWithin_le_nhds

end MathFin.BlackScholes.AmericanPut.Stopping
