/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.CanonicalPrice

/-! # Strict price positivity from the nondegenerate Gaussian terminal law

The deterministic maturity rule already has positive expected put payoff.
This proves price positivity without a classical PDE or optimal stopping rule.

## Result

Public entry points include `gaussian_put_integral_pos`, `brownian_put_maturity_reward_pos`,
`brownianAmericanPut_pos`, `brownianUsualAmericanPut_pos`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

theorem gaussian_put_integral_pos {K r q σ S : ℝ} (hK : 0 < K) (hr : 0 ≤ r)
    (hσ : 0 < σ) (hS : 0 < S) {T : ℝ≥0} (hT : 0 < T) :
    0 < ∫ y, Real.exp (-r*(T : ℝ))*
      max (K-MathFin.gbmValue S (r-q) σ T y) 0 ∂gaussianReal 0 T := by
  let F : ℝ → ℝ := fun y => Real.exp (-r*(T : ℝ))*
    max (K-MathFin.gbmValue S (r-q) σ T y) 0
  letI : (gaussianReal 0 T).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 (ne_of_gt hT)).isOpenPosMeasure
  have hc : Continuous F := by dsimp [F,MathFin.gbmValue]; fun_prop
  have hnonneg (y : ℝ) : 0 ≤ F y := mul_nonneg (Real.exp_pos _).le (le_max_right _ _)
  have hb (y : ℝ) : F y ≤ K :=
    putReward_le_strike (fun (_ : ℝ≥0) (w : ℝ) => w) hK.le hr hS.le (fun _ => T) y
  have hi : Integrable F (gaussianReal 0 T) :=
    (integrable_const K).mono_nonneg hc.aestronglyMeasurable
      (Eventually.of_forall hnonneg) (Eventually.of_forall hb)
  let D := (r-q-σ^2/2)*(T : ℝ)
  let y := (Real.log (K/S)-D-1)/σ
  have hy : D+σ*y < Real.log (K/S) := by
    have he : σ*y = Real.log (K/S)-D-1 := by
      dsimp [y]
      rw [mul_div_cancel₀ _ hσ.ne']
    linarith
  have hstock : MathFin.gbmValue S (r-q) σ T y < K := by
    have hh := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hy) hS
    rw [Real.exp_log (div_pos hK hS),mul_div_cancel₀ _ hS.ne'] at hh
    exact hh
  have hp : 0 < F y := mul_pos (Real.exp_pos _) ((sub_pos.mpr hstock).trans_le (le_max_left _ _))
  exact integral_pos_of_integrable_nonneg_nonzero hc hi hnonneg hp.ne'

theorem brownian_put_maturity_reward_pos {K r q σ S : ℝ} (hK : 0 < K) (hr : 0 ≤ r)
    (hσ : 0 < σ) (hS : 0 < S) {T : ℝ≥0} (hT : 0 < T) :
    0 < ∫ ω, putReward brownian K r q σ S (fun _ => T) ω ∂gaussianLimit := by
  have hc : Continuous (fun y => Real.exp (-r*(T : ℝ))*
      max (K-MathFin.gbmValue S (r-q) σ T y) 0) := by
    unfold MathFin.gbmValue
    fun_prop
  have he := (hasLaw_brownian_eval (t := T)).integral_comp hc.aestronglyMeasurable
  simp only [Function.comp_def] at he
  change 0 < ∫ ω, Real.exp (-r*(T : ℝ))*
    max (K-MathFin.gbmValue S (r-q) σ T (brownian T ω)) 0 ∂gaussianLimit
  rw [he]
  exact gaussian_put_integral_pos hK hr hσ hS hT

theorem brownianAmericanPut_pos {K r q σ S : ℝ} (hK : 0 < K) (hr : 0 ≤ r)
    (hσ : 0 < σ) (hS : 0 < S) {T : ℝ≥0} (hT : 0 < T) :
    0 < brownianAmericanPut K r q σ S T :=
  (brownian_put_maturity_reward_pos hK hr hσ hS hT).trans_le
    (european_expectation_le_value measurable_brownian_uncurry hK.le hr hS.le)

theorem brownianUsualAmericanPut_pos {K r q σ S : ℝ} (hK : 0 < K) (hr : 0 ≤ r)
    (hσ : 0 < σ) (hS : 0 < S) {T : ℝ≥0} (hT : 0 < T) :
    0 < brownianUsualAmericanPut K r q σ S T := by
  have he := integral_completion_original gaussianLimit
    (putReward_measurable measurable_brownian_uncurry K r q σ S measurable_const).stronglyMeasurable
      (f := putReward brownian K r q σ S (fun _ => T))
  have hp := brownian_put_maturity_reward_pos (q := q) hK hr hσ hS hT
  rw [← he] at hp
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact hp.trans_le (european_expectation_le_value (P := μ) (𝓕 := brownianUsualFiltration)
    brownian_completed_measurable hK.le hr hS.le)

theorem canonicalPrice_pos {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < canonicalPrice k h x t :=
  brownianUsualAmericanPut_pos (by norm_num) hk (Real.sqrt_pos.mpr (by norm_num))
    (Real.exp_pos x) (Real.toNNReal_pos.mpr ht)

end MathFin.BlackScholes.AmericanPut.Stopping
