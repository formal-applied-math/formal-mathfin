/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FirstContactOptimality
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualSupermartingale

/-! # Optimality of first contact for the actual usual-filtration American price

No PDE, smooth-fit or boundary-regularity premise is used. The nearly optimal
sequence consists of the already constructed optimal physical-grid rules.

## Result

Public entry points include `canonicalRewardProcess`, `canonicalRewardProcess_continuous`,
`canonicalRewardProcess_bound`, `brownianUsualActualContactTime`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

/-- Discounted put reward of exercising at the capped time `min t T`, for strike `1` and
spot `Real.exp x` on the Brownian driver. -/
noncomputable def canonicalRewardProcess (k h x : ℝ) (T t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  putReward brownian 1 k h (Real.sqrt 2) (Real.exp x) (fun _ => min t T) ω

theorem canonicalRewardProcess_continuous (k h x : ℝ) (T : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    Continuous (fun t => canonicalRewardProcess k h x T t ω) := by
  have hw := (continuous_brownian ω).comp (continuous_id.min (continuous_const (y := T)))
  unfold canonicalRewardProcess putReward MathFin.gbmValue
  fun_prop

theorem canonicalRewardProcess_bound {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    ‖canonicalRewardProcess k h x T t ω‖ ≤ 1 := by
  rw [canonicalRewardProcess,Real.norm_eq_abs,abs_of_nonneg (putReward_nonneg _ _ _ _ _ _ _ _)]
  exact putReward_le_strike brownian (by norm_num) hk (Real.exp_pos x).le _ ω

/-- The stopping time of `brownianUsualActualContactRule`. -/
noncomputable def brownianUsualActualContactTime {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T : ℝ≥0) :
    (ℝ≥0 → ℝ) → ℝ≥0 :=
  @StoppingRule.time (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit) ℝ≥0 _
    brownianUsualFiltration T
    (brownianUsualActualContactRule (h := h) hk x T)

theorem brownianUsualActualContactRule_optimal {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, putReward brownian 1 k h (Real.sqrt 2) (Real.exp x)
      (brownianUsualActualContactTime (h := h) hk x T) ω ∂completedMeasure gaussianLimit) =
      canonicalPrice k h x (T : ℝ) := by
  let μ := completedMeasure gaussianLimit
  have hinit : canonicalDiscountedPrice k h x T 0 =ᵐ[μ] fun _ => canonicalPrice k h x (T : ℝ) :=
    canonicalDiscountedPrice_initial k h x T
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  let U := canonicalDiscountedPrice k h x T
  let Z := canonicalRewardProcess k h x T
  let τ : StoppingRule brownianUsualFiltration T :=
    canonicalContactRule (h := h) hk brownianUsual_adapted continuous_brownian x T
  let θ : ℕ → StoppingRule brownianUsualFiltration T := fun n =>
    (optimalGridRule μ brownianUsual_adapted 1 k h (Real.sqrt 2) (Real.exp x) T
        (gridStep_pos n))
  have hU := canonicalDiscountedPrice_usual_supermartingale (h := h) hk x T
  have hUc := canonicalDiscountedPrice_continuous (h := h) hk x T
  have hUb := canonicalDiscountedPrice_bound (h := h) hk x T
  have hZc := canonicalRewardProcess_continuous k h x T
  have hZm : Measurable Z.uncurry := measurable_uncurry_of_continuous_of_measurable hZc
    (fun t =>
        putReward_measurable brownian_completed_measurable 1 k h (Real.sqrt 2) (Real.exp x)
        measurable_const)
  have hZb := canonicalRewardProcess_bound (h := h) hk x T
  have hdom (t : ℝ≥0) (_ : t ≤ T) (ω : ℝ≥0 → ℝ) : Z t ω ≤ U t ω :=
    canonicalDiscountedPrice_dominates hk x T t ω
  have hbefore (ω : ℝ≥0 → ℝ) (t : ℝ≥0) (ht : t < τ.time ω) : Z t ω < U t ω := by
    apply sub_pos.mp
    rw [show U t ω-Z t ω = Real.exp (-k*(min t T : ℝ≥0))*canonicalGap brownian k h x T t ω from
      canonicalDiscountedPrice_gap k h x T t ω]
    exact mul_pos (Real.exp_pos _) (firstContactTime_pos_before
      (canonicalGap_continuous (h := h) hk continuous_brownian x T)
      (canonicalGap_nonneg hk x T) (canonicalGap_terminal hk x T) ω ht)
  have hcontact : ∀ᵐ ω ∂μ, U (τ.time ω) ω = Z (τ.time ω) ω := by
    apply Eventually.of_forall
    intro ω
    apply sub_eq_zero.mp
    rw [show U (τ.time ω) ω-Z (τ.time ω) ω =
      Real.exp (-k*(min (τ.time ω) T : ℝ≥0))*canonicalGap brownian k h x T (τ.time ω) ω from
        canonicalDiscountedPrice_gap k h x T (τ.time ω) ω]
    rw [canonicalContactRule_contact hk brownianUsual_adapted continuous_brownian x T ω,mul_zero]
  have hZrule (η : StoppingRule brownianUsualFiltration T) :
      (fun ω => Z (η.time ω) ω) = putReward brownian 1 k h (Real.sqrt 2) (Real.exp x) η.time := by
    funext ω
    unfold Z canonicalRewardProcess putReward
    simp only [min_eq_left (η.le_horizon ω)]
  have hI0 : (∫ ω, U 0 ω ∂μ) = canonicalPrice k h x (T : ℝ) := by
    rw [integral_congr_ae hinit]
    simp
  have happrox : Tendsto (fun n => ∫ ω, Z ((θ n).time ω) ω ∂μ) atTop (𝓝 (∫ ω, U 0 ω ∂μ)) := by
    simp only [hZrule,hI0]
    have hh := optimalGridRule_payoffs_tendsto (P := μ) (𝓕 := brownianUsualFiltration)
      (K := 1) (r := k) (q := h) (σ := Real.sqrt 2) (S := Real.exp x) (T := T)
      brownian_completed_measurable brownianUsual_adapted continuous_brownian
      (by norm_num) hk (Real.exp_pos x).le
    convert! hh using 1
    simp only [canonicalPrice,Real.toNNReal_coe,brownianUsualAmericanPut]
    rfl
  have he :=
      firstContact_expectedReward_eq_initial hU hUc hUb hZm hZc hZb hdom τ hbefore
      hcontact θ happrox
  rw [hZrule,hI0] at he
  convert! he using 1

end MathFin.BlackScholes.AmericanPut.Stopping
