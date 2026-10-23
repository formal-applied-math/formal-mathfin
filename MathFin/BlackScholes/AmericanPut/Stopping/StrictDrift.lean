/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualTestFunctions

/-! # Strict signs of stopped generator integrals 
## Result

Public entry points include `integral_pos_of_ae_pos`, `planeDrift_pos`, `planeDrift_neg`,
`expected_rectangle_drift_pos`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

theorem integral_pos_of_ae_pos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NeZero μ] {f : Ω → ℝ} (hi : Integrable f μ) (hp : ∀ᵐ ω ∂μ, 0 < f ω) :
    0 < ∫ ω, f ω ∂μ := by
  have hn := integral_nonneg_of_ae (hp.mono (fun _ h => h.le))
  by_contra! hle
  have hz := (integral_eq_zero_iff_of_nonneg_ae (hp.mono (fun _ h => h.le)) hi).mp
    (le_antisymm hle hn)
  obtain ⟨ω,hpω,hzω⟩ := (hp.and hz).exists
  exact (ne_of_gt hpω) hzω

theorem planeDrift_pos {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G)
    {t : ℝ≥0} (ht : 0 < t) (ω : ℝ≥0 → ℝ)
    (hp : ∀ s ≤ t, 0 < planeGenerator G (s, brownian s ω)) :
    0 < planeDrift G t ω := by
  let ν := MathFin.ItoIntegralL2.timeMeasure.restrict (Ioc 0 t)
  haveI : NeZero ν := ⟨by
    intro hz
    have he := congrArg (fun μ : Measure ℝ≥0 => μ univ) hz
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have he' : ENNReal.ofReal (t : ℝ) = 0 := by
      simpa [ν,MathFin.ItoIntegralL2.timeMeasure_Ioc] using he
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr ht')) he'⟩
  have hc : Continuous (fun s : ℝ≥0 => planeGenerator G (s,brownian s ω)) :=
    (planeGenerator_continuous hG).comp (NNReal.continuous_coe.prodMk (continuous_brownian ω))
  apply integral_pos_of_ae_pos
    (hc.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact hp s hs.2

theorem planeDrift_neg {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G)
    {t : ℝ≥0} (ht : 0 < t) (ω : ℝ≥0 → ℝ)
    (hp : ∀ s ≤ t, planeGenerator G (s, brownian s ω) < 0) :
    planeDrift G t ω < 0 := by
  let ν := MathFin.ItoIntegralL2.timeMeasure.restrict (Ioc 0 t)
  haveI : NeZero ν := ⟨by
    intro hz
    have he := congrArg (fun μ : Measure ℝ≥0 => μ univ) hz
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have he' : ENNReal.ofReal (t : ℝ) = 0 := by
      simpa [ν,MathFin.ItoIntegralL2.timeMeasure_Ioc] using he
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr ht')) he'⟩
  have hc : Continuous (fun s : ℝ≥0 => planeGenerator G (s,brownian s ω)) :=
    (planeGenerator_continuous hG).comp (NNReal.continuous_coe.prodMk (continuous_brownian ω))
  have hi : Integrable (fun s : ℝ≥0 => -planeGenerator G (s,brownian s ω)) ν :=
    (hc.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self).neg
  have hh := integral_pos_of_ae_pos hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact neg_pos.mpr (hp s hs.2))
  simp only [integral_neg] at hh
  exact neg_pos.mp hh

theorem expected_rectangle_drift_pos (k h x : ℝ) {R : ℝ} (hR : 0 < R)
    {δ : ℝ≥0} (hδ : 0 < δ) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ 3 G) (hc : HasCompactSupport G)
    (hp : ∀ z ∈ driverRectangle k h R δ, 0 < planeGenerator G z) :
    0 < ∫ ω, planeDrift G ((rawRectangleExitRule k h x R δ).time ω) ω ∂gaussianLimit := by
  obtain ⟨C,hC⟩ := (planeGenerator_hasCompactSupport hc).exists_bound_of_continuous
    (planeGenerator_continuous hG)
  apply integral_pos_of_ae_pos
    (planeDrift_stopped_integrable hG _ (fun s _ w => hC (s,w)))
  filter_upwards [rawRectangleExit_path_mem_ae k h x hR hδ] with ω hω
  exact planeDrift_pos hG hω.1 ω (fun s hs => hp _ (hω.2 s hs))

theorem expected_rectangle_drift_neg (k h x : ℝ) {R : ℝ} (hR : 0 < R)
    {δ : ℝ≥0} (hδ : 0 < δ) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ 3 G) (hc : HasCompactSupport G)
    (hp : ∀ z ∈ driverRectangle k h R δ, planeGenerator G z < 0) :
    (∫ ω, planeDrift G ((rawRectangleExitRule k h x R δ).time ω) ω ∂gaussianLimit) < 0 := by
  obtain ⟨C,hC⟩ := (planeGenerator_hasCompactSupport hc).exists_bound_of_continuous
    (planeGenerator_continuous hG)
  have hi := planeDrift_stopped_integrable hG (rawRectangleExitRule k h x R δ)
    (fun s _ w => hC (s,w))
  have hh := integral_pos_of_ae_pos hi.neg (by
    filter_upwards [rawRectangleExit_path_mem_ae k h x hR hδ] with ω hω
    exact neg_pos.mpr (planeDrift_neg hG hω.1 ω (fun s hs => hp _ (hω.2 s hs))))
  simp only [Pi.neg_apply,integral_neg] at hh
  exact neg_pos.mp hh

end MathFin.BlackScholes.AmericanPut.Stopping
