/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.JointPriceContinuity
public import MathFin.BlackScholes.AmericanPut.Stopping.SpotDecay

/-! # An actual stopping-value candidate for the normalized classical price

Strike one and volatility sqrt(2) make physical time equal normalized time.
Time is clamped at zero only to define a total real-valued function. The
classical contract uses nonnegative times. No PDE or boundary is postulated.

## Result

Public entry points include `canonicalPrice`, `canonicalPrice_continuous`, `canonicalPrice_initial`,
`canonicalPrice_bounds`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

/-- The `brownianUsualAmericanPut` value at strike `1`, rate `k`, dividend `h`, volatility
`Real.sqrt 2`, spot `Real.exp x` and horizon `t.toNNReal`. Negative `t` is clamped to zero by
`toNNReal`. -/
noncomputable def canonicalPrice (k h x t : ℝ) : ℝ :=
  brownianUsualAmericanPut 1 k h (Real.sqrt 2) (Real.exp x) t.toNNReal

theorem canonicalPrice_continuous {k h : ℝ} (hk : 0 ≤ k) :
    Continuous (fun z : ℝ × ℝ => canonicalPrice k h z.1 z.2) := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  apply continuous_iff_continuousAt.mpr
  intro z
  have hv := americanPutValue_joint_continuousAt (P := μ) (𝓕 := brownianUsualFiltration)
    (q := h) (σ := Real.sqrt 2) brownian_completed_measurable continuous_brownian
    (show (0 : ℝ) ≤ 1 by norm_num) hk (Real.exp_pos z.1) z.2.toNNReal
  have ht : Tendsto (fun z : ℝ × ℝ => (Real.exp z.1,z.2.toNNReal)) (𝓝 z)
      (𝓝 (Real.exp z.1,z.2.toNNReal)) :=
    (show Continuous (fun z : ℝ × ℝ => (Real.exp z.1,z.2.toNNReal)) by fun_prop).tendsto z
  have hh := Tendsto.comp
    (g := fun w : ℝ × ℝ≥0 => americanPutValue μ brownianUsualFiltration brownian
      1 k h (Real.sqrt 2) w.1 w.2)
    (f := fun w : ℝ × ℝ => (Real.exp w.1,w.2.toNNReal)) hv ht
  convert! hh using 1

theorem canonicalPrice_initial {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) :
    canonicalPrice k h x 0 = putPayoff x := by
  let μ := completedMeasure gaussianLimit
  have hz : ∀ᵐ ω ∂μ, brownian 0 ω = 0 := isBrownianReal_brownian.eval_zero_ae_eq_zero
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  have hh :=
      value_at_expiry (P := μ) (𝓕 := brownianUsualFiltration) (K := 1) (q := h) (σ := Real.sqrt 2)
    brownian_completed_measurable hz
    (by norm_num) hk (Real.exp_pos x).le
  simpa only [canonicalPrice, brownianUsualAmericanPut, putPayoff, Real.toNNReal_zero] using hh

theorem canonicalPrice_bounds {k h : ℝ} (hk : 0 ≤ k) (x t : ℝ) :
    putPayoff x ≤ canonicalPrice k h x t ∧ canonicalPrice k h x t ≤ 1 := by
  let μ := completedMeasure gaussianLimit
  have hz : ∀ᵐ ω ∂μ, brownian 0 ω = 0 := isBrownianReal_brownian.eval_zero_ae_eq_zero
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact ⟨payoff_le_value (P := μ) (𝓕 := brownianUsualFiltration) brownian_completed_measurable hz
    (by norm_num) hk (Real.exp_pos x).le,
    value_le_strike (P := μ) (𝓕 := brownianUsualFiltration) brownian_completed_measurable
      (by norm_num) hk (Real.exp_pos x).le⟩

theorem canonicalPrice_normalization (k : ℝ) : normalizedRate k (Real.sqrt 2) = k := by
  simp only [normalizedRate,Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

theorem canonicalPrice_decay {k h : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    Tendsto (fun x => canonicalPrice k h x t) atTop (𝓝 0) := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  have hd := americanPutValue_spot_decay (P := μ) (𝓕 := brownianUsualFiltration)
    (q := h) (σ := Real.sqrt 2) (T := t.toNNReal)
    brownian_completed_measurable continuous_brownian (show (0 : ℝ) ≤ 1 by norm_num) hk
  have hh := hd.comp Real.tendsto_exp_atTop
  convert! hh using 1

theorem canonicalPrice_decay_uniform {k h : ℝ} (hk : 0 ≤ k) (T : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, ∀ t : ℝ, t ≤ T →
      0 ≤ canonicalPrice k h x t ∧ canonicalPrice k h x t < ε := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  have hd := americanPutValue_spot_decay_uniform (P := μ) (𝓕 := brownianUsualFiltration)
    (q := h) (σ := Real.sqrt 2) brownian_completed_measurable continuous_brownian
    (show (0 : ℝ) ≤ 1 by norm_num) hk T.toNNReal hε
  filter_upwards [Real.tendsto_exp_atTop.eventually hd] with x hx
  intro t ht
  exact hx t.toNNReal (Real.toNNReal_mono ht)

end MathFin.BlackScholes.AmericanPut.Stopping
