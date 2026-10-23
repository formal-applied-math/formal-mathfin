/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ContactMartingale

/-! # Bounded stopping of the compensated plane Itô process

These are test-function results, not differentiability assumptions on the
American price. The residual includes its nonzero generator integral. Continuous
paths upgrade fixed-time Itô identities before any random-time substitution.

## Result

Public entry points include `planeDrift`, `planeResidual`, `planeGenerator_continuous`,
`planeDrift_continuous`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

/-- The time integral `∫ s in Ioc 0 t, planeGenerator G (s, brownian s ω)` of the generator
along the Brownian path. -/
noncomputable def planeDrift (G : ℝ × ℝ → ℝ) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∫ s in Ioc 0 t, planeGenerator G (s,brownian s ω) ∂MathFin.ItoIntegralL2.timeMeasure

/-- The increment of `G` along the Brownian path with its drift subtracted:
`G (t, brownian t ω) - G (0, brownian 0 ω) - planeDrift G t ω`. -/
noncomputable def planeResidual (G : ℝ × ℝ → ℝ) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  G (t,brownian t ω)-G (0,brownian 0 ω)-planeDrift G t ω

theorem planeGenerator_continuous {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G) :
    Continuous (planeGenerator G) :=
  (planePartial_contDiff hG (1,0)).continuous.add
    (continuous_const.mul (planePartial_contDiff (planePartial_contDiff hG (0,1)) (0,1)).continuous)

theorem planeDrift_continuous {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G)
    (ω : ℝ≥0 → ℝ) : Continuous (fun t => planeDrift G t ω) :=
  MathFin.continuous_timeMeasure_primitive
    ((planeGenerator_continuous hG).comp (NNReal.continuous_coe.prodMk (continuous_brownian ω)))

theorem planeResidual_continuous {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G)
    (ω : ℝ≥0 → ℝ) : Continuous (fun t => planeResidual G t ω) :=
  ((hG.continuous.comp (NNReal.continuous_coe.prodMk (continuous_brownian ω))).sub
    continuous_const).sub (planeDrift_continuous hG ω)

theorem planeResidual_stronglyAdapted {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G) :
    StronglyAdapted brownianFiltration (planeResidual G) := by
  intro t
  exact MathFin.residual_stronglyMeasurable measurable_brownian continuous_brownian
    (f := fun t w => G (t,w)) (f_t := fun t w => planePartial G (1,0) (t,w))
    (f_xx := fun t w => planePartial (planePartial G (0,1)) (0,1) (t,w))
    hG.continuous (planePartial_contDiff hG (1,0)).continuous
    (planePartial_contDiff (planePartial_contDiff hG (0,1)) (0,1)).continuous t

theorem planeResidual_zero (G : ℝ × ℝ → ℝ) (ω : ℝ≥0 → ℝ) : planeResidual G 0 ω = 0 := by
  simp [planeResidual,planeDrift]

theorem planeResidual_localMartingale {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G) :
    IsLocalMartingale (planeResidual G) brownianAugFiltration gaussianLimit := by
  obtain ⟨M,hMc,hM,he⟩ := plane_ito_localMartingale
    isBrownianReal_brownian.toIsPreBrownianReal measurable_brownian continuous_brownian hG
  apply localMartingale_of_ae_path_eq hM
    (fun t => (planeResidual_stronglyAdapted hG t).mono (brownianFiltration_le_aug t))
    (planeResidual_continuous hG)
  apply indistinguishable_of_modification (Eventually.of_forall hMc)
    (Eventually.of_forall (planeResidual_continuous hG))
  intro t
  filter_upwards [he t] with ω hω
  change M t ω = G (t,brownian t ω)-G (0,brownian 0 ω)-planeDrift G t ω
  change G (t,brownian t ω)-G (0,brownian 0 ω) = M t ω+planeDrift G t ω at hω
  linarith

theorem planeDrift_norm_le {G : ℝ × ℝ → ℝ} {T t : ℝ≥0} {C : ℝ}
    (hL : ∀ s : ℝ≥0, s ≤ T → ∀ w : ℝ, ‖planeGenerator G (s,w)‖ ≤ C)
    (ht : t ≤ T) (ω : ℝ≥0 → ℝ) : ‖planeDrift G t ω‖ ≤ (t : ℝ)*C := by
  let ν := MathFin.ItoIntegralL2.timeMeasure.restrict (Ioc 0 t)
  haveI : IsFiniteMeasure ν := ⟨by
    simp only [ν,Measure.restrict_apply_univ,MathFin.ItoIntegralL2.timeMeasure_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  have hh := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun s => planeGenerator G (s,brownian s ω))
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs; exact hL s (hs.2.trans ht) _)
  simpa only [planeDrift,ν,Measure.real_def,Measure.restrict_apply_univ,
    MathFin.ItoIntegralL2.timeMeasure_Ioc,NNReal.coe_zero,sub_zero,
    ENNReal.toReal_ofReal t.coe_nonneg,mul_comm] using hh

theorem planeResidual_stopped_martingale {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G)
    {T : ℝ≥0} (θ : BoundedRule brownianFiltration T) {A C : ℝ}
    (hb : ∀ s : ℝ≥0, s ≤ T → ∀ w : ℝ, ‖G (s,w)‖ ≤ A)
    (hL : ∀ s : ℝ≥0, s ≤ T → ∀ w : ℝ, ‖planeGenerator G (s,w)‖ ≤ C) :
    Martingale (fun t ω => planeResidual G (min t (θ.time ω)) ω)
      brownianFiltration gaussianLimit := by
  let X := fun t ω => planeResidual G (min t (θ.time ω)) ω
  have hA : StronglyAdapted brownianFiltration X := by
    convert! (planeResidual_stronglyAdapted hG).stoppedProcess
      (planeResidual_continuous hG) θ.stopping using 1
  have hc : ∀ ω, Continuous (fun t => X t ω) := fun ω =>
    (planeResidual_continuous hG ω).comp (continuous_id.min continuous_const)
  have hθ : IsStoppingTime brownianAugFiltration (fun ω => (θ.time ω : WithTop ℝ≥0)) :=
    fun t => brownianFiltration_le_aug t _ (θ.stopping t)
  have hlocal : IsLocalMartingale X brownianAugFiltration gaussianLimit := by
    apply localMartingale_of_ae_path_eq
      (localMartingale_stopped_indicator (planeResidual_localMartingale hG) hθ)
      (fun t => (hA t).mono (brownianFiltration_le_aug t)) hc
    apply Eventually.of_forall
    intro ω t
    by_cases hp : 0 < θ.time ω
    · rw [indicator_of_mem (show ω ∈ {ω | 0 < θ.time ω} from hp)]
    · have hz : θ.time ω = 0 := le_antisymm (le_of_not_gt hp) zero_le
      simp [X,hz,planeResidual_zero]
  apply martingale_smaller_filtration brownianFiltration_le_aug _ hA
  apply bounded_localMartingale_is_martingale hlocal
    (fun t => (hA t).mono (brownianFiltration_le_aug t)) (C := A+A+(T : ℝ)*C)
  intro t ω
  have hs : min t (θ.time ω) ≤ T := (min_le_right _ _).trans (θ.le_horizon ω)
  have hC : 0 ≤ C := (norm_nonneg _).trans (hL 0 zero_le 0)
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add (hb _ hs _) (hb 0 zero_le _)))
    ((planeDrift_norm_le hL hs ω).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hC)))

theorem planeResidual_expected_stopped_zero {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G)
    {T : ℝ≥0} (θ : BoundedRule brownianFiltration T) {A C : ℝ}
    (hb : ∀ s : ℝ≥0, s ≤ T → ∀ w : ℝ, ‖G (s,w)‖ ≤ A)
    (hL : ∀ s : ℝ≥0, s ≤ T → ∀ w : ℝ, ‖planeGenerator G (s,w)‖ ≤ C) :
    (∫ ω, planeResidual G (θ.time ω) ω ∂gaussianLimit) = 0 := by
  have he := (planeResidual_stopped_martingale hG θ hb hL).setIntegral_eq
    (i := 0) (j := T) zero_le (s := univ) MeasurableSet.univ
  simpa only [setIntegral_univ,zero_min,planeResidual_zero,integral_zero,
    min_eq_right (θ.le_horizon _)] using he.symm

theorem planeDrift_stronglyAdapted {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G) :
    StronglyAdapted brownianFiltration (planeDrift G) := by
  intro t
  exact MathFin.driftPrimitive_stronglyMeasurable measurable_brownian continuous_brownian
    (f_t := fun t w => planePartial G (1,0) (t,w))
    (f_xx := fun t w => planePartial (planePartial G (0,1)) (0,1) (t,w))
    (planePartial_contDiff hG (1,0)).continuous
    (planePartial_contDiff (planePartial_contDiff hG (0,1)) (0,1)).continuous t

theorem planeDrift_stopped_integrable {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G)
    {T : ℝ≥0} (θ : BoundedRule brownianFiltration T) {C : ℝ}
    (hL : ∀ s : ℝ≥0, s ≤ T → ∀ w : ℝ, ‖planeGenerator G (s,w)‖ ≤ C) :
    Integrable (fun ω => planeDrift G (θ.time ω) ω) gaussianLimit := by
  have hm := measurable_uncurry_of_continuous_of_measurable (planeDrift_continuous hG)
    (fun t => ((planeDrift_stronglyAdapted hG t).mono (brownianFiltration.le t)).measurable)
  apply (integrable_const ((T : ℝ)*C)).mono'
    (hm.comp (θ.measurable_time.prodMk measurable_id)).aestronglyMeasurable
  apply Eventually.of_forall
  intro ω
  exact (planeDrift_norm_le hL (θ.le_horizon ω) ω).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast θ.le_horizon ω)
      ((norm_nonneg _).trans (hL 0 zero_le 0)))

theorem planeValue_stopped_integrable {G : ℝ × ℝ → ℝ} (hG : Continuous G)
    {T : ℝ≥0} (θ : BoundedRule brownianFiltration T) {A : ℝ}
    (hb : ∀ s : ℝ≥0, s ≤ T → ∀ w : ℝ, ‖G (s,w)‖ ≤ A) :
    Integrable (fun ω => G (θ.time ω,brownian (θ.time ω) ω)) gaussianLimit := by
  apply (integrable_const A).mono'
    (hG.measurable.comp ((NNReal.continuous_coe.measurable.comp θ.measurable_time).prodMk
      (measurable_brownian_uncurry.comp
          (θ.measurable_time.prodMk measurable_id)))).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => hb _ (θ.le_horizon ω) _)

/-- Dynkin's identity at any bounded raw Brownian stopping rule. -/
theorem plane_dynkin_boundedRule {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G)
    {T : ℝ≥0} (θ : BoundedRule brownianFiltration T) {A C : ℝ}
    (hb : ∀ s : ℝ≥0, s ≤ T → ∀ w : ℝ, ‖G (s,w)‖ ≤ A)
    (hL : ∀ s : ℝ≥0, s ≤ T → ∀ w : ℝ, ‖planeGenerator G (s,w)‖ ≤ C) :
    (∫ ω, G (θ.time ω,brownian (θ.time ω) ω) ∂gaussianLimit) =
      G (0,0) + ∫ ω, planeDrift G (θ.time ω) ω ∂gaussianLimit := by
  have hi := planeValue_stopped_integrable hG.continuous θ hb
  have h0 : Integrable (fun ω => G (0,brownian 0 ω)) gaussianLimit :=
    (integrable_const A).mono'
      (hG.continuous.measurable.comp
          (measurable_const.prodMk (measurable_brownian 0))).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hb 0 zero_le _))
  have hd := planeDrift_stopped_integrable hG θ hL
  have he := planeResidual_expected_stopped_zero hG θ hb hL
  change (∫ ω, (G (θ.time ω,brownian (θ.time ω) ω)-G (0,brownian 0 ω))-
    planeDrift G (θ.time ω) ω ∂gaussianLimit) = 0 at he
  have his : Integrable (fun ω => G (θ.time ω,brownian (θ.time ω) ω)-G (0,brownian 0 ω))
      gaussianLimit := hi.sub h0
  rw [integral_sub his hd,integral_sub hi h0] at he
  have he0 : (∫ ω, G (0,brownian 0 ω) ∂gaussianLimit) = G (0,0) := by
    calc
      _ = ∫ _, G (0,0) ∂gaussianLimit := integral_congr_ae
        (isBrownianReal_brownian.eval_zero_ae_eq_zero.mono (fun ω hω => by rw [hω]))
      _ = _ := by simp
  rw [he0] at he
  linarith

theorem planeGenerator_hasCompactSupport {G : ℝ × ℝ → ℝ} (hc : HasCompactSupport G) :
    HasCompactSupport (planeGenerator G) :=
  (hc.fderiv_apply ℝ (1,0)).add (((hc.fderiv_apply ℝ (0,1)).fderiv_apply ℝ (0,1)).mul_left)

/-- Compactly supported C3 test functions discharge both boundedness obligations. -/
theorem plane_dynkin_compact {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G)
    (hc : HasCompactSupport G) {T : ℝ≥0} (θ : BoundedRule brownianFiltration T) :
    (∫ ω, G (θ.time ω,brownian (θ.time ω) ω) ∂gaussianLimit) =
      G (0,0) + ∫ ω, planeDrift G (θ.time ω) ω ∂gaussianLimit := by
  obtain ⟨A,hA⟩ := hc.exists_bound_of_continuous hG.continuous
  obtain ⟨C,hC⟩ := (planeGenerator_hasCompactSupport hc).exists_bound_of_continuous
    (planeGenerator_continuous hG)
  exact plane_dynkin_boundedRule hG θ (fun s _ w => hA (s,w)) (fun s _ w => hC (s,w))

end MathFin.BlackScholes.AmericanPut.Stopping
