/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualOptimality
public import MathFin.BlackScholes.AmericanPut.Stopping.OptimalStoppedMartingale

/-! # Martingale and stopped mean-value property at actual first contact

These are properties of the constructed stopping value. Classical regularity,
smooth fit and the PDE are not assumptions.

## Result

Public entry points include `brownianUsualActualContactRule_value_preserving`,
`brownianUsualActualContactRule_martingale`, `canonicalPrice_contact_meanValue`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

theorem brownianUsualActualContactRule_value_preserving {k h : ℝ} (hk : 0 ≤ k)
    (x : ℝ) (T : ℝ≥0) :
    (∫ ω, canonicalDiscountedPrice k h x T (brownianUsualActualContactTime (h := h) hk x T ω) ω
      ∂completedMeasure gaussianLimit) =
      ∫ ω, canonicalDiscountedPrice k h x T 0 ω ∂completedMeasure gaussianLimit := by
  let μ := completedMeasure gaussianLimit
  have hinit : canonicalDiscountedPrice k h x T 0 =ᵐ[μ] fun _ => canonicalPrice k h x (T : ℝ) :=
    canonicalDiscountedPrice_initial k h x T
  have hopt := brownianUsualActualContactRule_optimal (h := h) hk x T
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  let τ := brownianUsualActualContactRule (h := h) hk x T
  have hc (ω : ℝ≥0 → ℝ) : canonicalDiscountedPrice k h x T (τ.time ω) ω =
      putReward brownian 1 k h (Real.sqrt 2) (Real.exp x) τ.time ω := by
    exact classicalContactRule_contact (K := 1) (r := k) (q := h) (σ := Real.sqrt 2)
      (canonicalPrice_putEnvelope (h := h) hk) brownianUsual_adapted continuous_brownian one_pos
      (Real.exp_pos x) T ω
  change (∫ ω, canonicalDiscountedPrice k h x T (τ.time ω) ω ∂μ) = _
  rw [integral_congr_ae (Eventually.of_forall hc),integral_congr_ae hinit]
  simp only [integral_const,probReal_univ,one_smul]
  convert! hopt using 1

theorem brownianUsualActualContactRule_martingale {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T : ℝ≥0) :
    Martingale (fun t ω => canonicalDiscountedPrice k h x T
      (min t (brownianUsualActualContactTime (h := h) hk x T ω)) ω)
      brownianUsualFiltration (completedMeasure gaussianLimit) := by
  let μ := completedMeasure gaussianLimit
  have hopt := brownianUsualActualContactRule_value_preserving (h := h) hk x T
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  have hh := stopped_martingale_of_expected_value_eq (P := μ)
    (canonicalDiscountedPrice_usual_supermartingale hk x T)
    (canonicalDiscountedPrice_continuous hk x T) (canonicalDiscountedPrice_bound hk x T)
    (brownianUsualActualContactRule (h := h) hk x T) hopt
  convert! hh using 1

/-- Mean-value identity at any bounded observation rule, capped at first contact. -/
theorem canonicalPrice_contact_meanValue {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T : ℝ≥0)
    (η : @StoppingRule (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit) ℝ≥0 _
        brownianUsualFiltration T) :
    (∫ ω, canonicalDiscountedPrice k h x T
      (min (@StoppingRule.time _ (completedMeasurableSpace gaussianLimit) ℝ≥0 _
          brownianUsualFiltration T η ω)
        (brownianUsualActualContactTime (h := h) hk x T ω)) ω ∂completedMeasure gaussianLimit) =
      canonicalPrice k h x (T : ℝ) := by
  let μ := completedMeasure gaussianLimit
  have hinit : canonicalDiscountedPrice k h x T 0 =ᵐ[μ] fun _ => canonicalPrice k h x (T : ℝ) :=
    canonicalDiscountedPrice_initial k h x T
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  have hh := expected_stoppedValue_eq_initial (P := μ)
    (brownianUsualActualContactRule_martingale (h := h) hk x T)
    (fun ω =>
        (canonicalDiscountedPrice_continuous hk x T ω).comp (continuous_id.min continuous_const))
    (fun t ω => canonicalDiscountedPrice_bound hk x T _ ω) η
  simp only [zero_min] at hh
  rw [integral_congr_ae hinit] at hh
  simpa only [integral_const,probReal_univ,one_smul] using hh

end MathFin.BlackScholes.AmericanPut.Stopping
