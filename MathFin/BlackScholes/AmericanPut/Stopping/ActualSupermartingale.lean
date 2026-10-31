/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.AmericanWaiting
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualContact
public import MathFin.BlackScholes.AmericanPut.Stopping.ClassicalTransition

/-! # Supermartingality of the actual normalized American price

This process is the classical candidate of the actual price, built from the stopping supremum,
not from an assumed classical solution. Its supermartingale property is the generic one
(`brownianClassicalCandidate_supermartingale`) for an envelope that waits, with dynamic
programming supplying the waiting inequality.

## Result

Public entry points include `canonicalDiscountedPrice`, `canonicalDiscountedPrice_apply`,
`canonicalDiscountedPrice_initial`, `canonicalDiscountedPrice_supermartingale`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology
open MathFin.ItoLocalMartingale (nullAugmentation supermartingale_nullAugmentation)

/-- The candidate in the normalized conventions: `Real.exp (-k*(min t T))` times the canonical
price at the Brownian log-state at remaining time `T-min t T`. -/
theorem canonicalDiscountedPrice_apply (k h x : ℝ) (T t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    canonicalDiscountedPrice k h x T t ω =
      Real.exp (-k*(min t T : ℝ≥0))*canonicalPrice k h
        (brownianLogState (k-h-1) (Real.sqrt 2) x (min t T) ω) ((T : ℝ)-(min t T : ℝ≥0)) := by
  unfold canonicalDiscountedPrice
  simp only [classicalCandidate,classicalLogSpot_canonical,sqrt_two_sq_div_two_mul,one_mul,
    brownianLogState]

theorem canonicalDiscountedPrice_initial (k h x : ℝ) (T : ℝ≥0) :
    canonicalDiscountedPrice k h x T 0 =ᵐ[gaussianLimit] fun _ => canonicalPrice k h x (T : ℝ) := by
  filter_upwards [isBrownianReal_brownian.eval_zero_ae_eq_zero] with ω hω
  simp [canonicalDiscountedPrice_apply,brownianLogState,hω]

theorem canonicalDiscountedPrice_dominates {k h : ℝ} (hk : 0 ≤ k) (x : ℝ)
    (T t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    frozenPutReward brownian 1 k h (Real.sqrt 2) (Real.exp x) T t ω ≤
      canonicalDiscountedPrice k h x T t ω :=
  sub_nonneg.mp (classicalGap_nonneg (W := brownian) (K := 1) (r := k) (q := h)
    (σ := Real.sqrt 2) (S := Real.exp x) (canonicalPrice_putEnvelope hk) one_pos
    (Real.exp_pos x) T t ω)

theorem canonicalDiscountedPrice_bound {k h : ℝ} (hk : 0 ≤ k) (x : ℝ)
    (T t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ‖canonicalDiscountedPrice k h x T t ω‖ ≤ 1 :=
  classicalCandidate_norm_le (q := h) (σ := Real.sqrt 2) (S := Real.exp x)
    (canonicalPrice_putEnvelope hk) brownian zero_le_one hk T t ω

theorem canonicalDiscountedPrice_continuous {k h : ℝ} (hk : 0 ≤ k) (x : ℝ)
    (T : ℝ≥0) (ω : ℝ≥0 → ℝ) : Continuous (fun t => canonicalDiscountedPrice k h x T t ω) :=
  classicalCandidate_continuous (canonicalPrice_putEnvelope hk) continuous_brownian T ω

theorem canonicalDiscountedPrice_adapted {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T : ℝ≥0) :
    Adapted brownianFiltration (canonicalDiscountedPrice k h x T) :=
  classicalCandidate_adapted (canonicalPrice_putEnvelope hk) brownian_adapted T

/-- The actual discounted price is a supermartingale: the generic envelope-and-waiting
argument, with dynamic programming (`canonicalPrice_putWaiting`) supplying the waiting. -/
theorem canonicalDiscountedPrice_supermartingale {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T : ℝ≥0) :
    Supermartingale (canonicalDiscountedPrice k h x T) brownianFiltration gaussianLimit := by
  refine brownianClassicalCandidate_supermartingale (K := 1) (r := k) (q := h)
    (σ := Real.sqrt 2) (S := Real.exp x) (canonicalPrice_putEnvelope hk) ?_ zero_le_one hk
    (Real.sqrt_pos.mpr two_pos) T
  rw [normalizedRate_sqrt_two,normalizedRate_sqrt_two]
  exact canonicalPrice_putWaiting hk

theorem canonicalDiscountedPrice_usual_supermartingale {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T : ℝ≥0) :
    Supermartingale (canonicalDiscountedPrice k h x T) brownianUsualFiltration
      (completedMeasure gaussianLimit) := by
  have hu := bounded_supermartingale_completion gaussianLimit
    (canonicalDiscountedPrice_supermartingale (h := h) hk x T)
        (canonicalDiscountedPrice_bound hk x T)
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact bounded_continuous_supermartingale_rightCont (supermartingale_nullAugmentation hu)
    (canonicalDiscountedPrice_continuous hk x T) (canonicalDiscountedPrice_bound hk x T)

end MathFin.BlackScholes.AmericanPut.Stopping
