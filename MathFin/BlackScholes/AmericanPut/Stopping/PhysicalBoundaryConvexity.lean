/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualBoundaryNormalization

/-! # Convexity of the actual American put option boundary in physical units

The parameter hypotheses are exactly positive strike, risk-free interest rate and volatility, with
nonnegative dividend yield at most the risk-free interest rate. The time variable is time-to-expiry.
These are convex-function results; classical second-derivative existence is not asserted.

## Result

Public entry points include `brownianUsualLogBoundary_convexOn`,
`brownianUsualStockBoundary_strictConvexOn`, and `brownianUsualStockBoundary_strictAntiOn`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Boundary

theorem convexOn_positive_time_rescale {f : ℝ → ℝ} {a : ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f) (ha : 0 < a) :
    ConvexOn ℝ (Ioi 0) (fun t => f (a*t)) := by
  refine ⟨convex_Ioi 0,?_⟩
  intro x hx y hy u v hu hv huv
  have he := hf.2 (mul_pos ha hx) (mul_pos ha hy) hu hv huv
  simpa only [smul_eq_mul,mul_add,mul_left_comm] using he

theorem strictConvexOn_positive_rescale {f : ℝ → ℝ} {K a : ℝ}
    (hf : StrictConvexOn ℝ (Ioi 0) f) (hK : 0 < K) (ha : 0 < a) :
    StrictConvexOn ℝ (Ioi 0) (fun t => K*f (a*t)) := by
  refine ⟨convex_Ioi 0,?_⟩
  intro x hx y hy hxy u v hu hv huv
  have hne : a*x ≠ a*y := fun he => hxy (mul_left_cancel₀ ha.ne' he)
  have he := mul_lt_mul_of_pos_left (hf.2 (mul_pos ha hx) (mul_pos ha hy) hne hu hv huv) hK
  simpa only [smul_eq_mul,mul_add,mul_left_comm] using he

theorem brownianUsualLogBoundary_convexOn {K r q σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ) :
    ConvexOn ℝ (Ioi 0)
      (fun τ : ℝ => Real.log (brownianUsualExerciseBoundary K r q σ τ.toNNReal/K)) := by
  obtain ⟨hk,hh,hhk⟩ := normalized_rates_admissible hr hq hqr hσ
  apply (convexOn_positive_time_rescale (canonicalLogBoundary_convexOn hk hh hhk)
    (by positivity : 0 < σ^2/2)).congr
  intro τ hτ
  exact (brownianUsualLogBoundary_normalization hK hr hq hqr hσ hτ).symm

theorem brownianUsualStockBoundary_strictConvexOn {K r q σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ) :
    StrictConvexOn ℝ (Ioi 0)
      (fun τ : ℝ => brownianUsualExerciseBoundary K r q σ τ.toNNReal) := by
  obtain ⟨hk,hh,hhk⟩ := normalized_rates_admissible hr hq hqr hσ
  apply (strictConvexOn_positive_rescale (canonicalStockBoundary_strictConvexOn hk hh hhk)
    hK (by positivity : 0 < σ^2/2)).congr
  intro τ hτ
  exact (brownianUsualExerciseBoundary_eq_scaled_canonical hK hr hq hqr hσ hτ).symm

theorem brownianUsualStockBoundary_strictAntiOn {K r q σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ) :
    StrictAntiOn (fun τ : ℝ => brownianUsualExerciseBoundary K r q σ τ.toNNReal) (Ioi 0) := by
  obtain ⟨hk,hh,hhk⟩ := normalized_rates_admissible hr hq hqr hσ
  intro s hs t ht hst
  change brownianUsualExerciseBoundary K r q σ t.toNNReal <
    brownianUsualExerciseBoundary K r q σ s.toNNReal
  rw [brownianUsualExerciseBoundary_eq_scaled_canonical hK hr hq hqr hσ hs,
    brownianUsualExerciseBoundary_eq_scaled_canonical hK hr hq hqr hσ ht]
  apply mul_lt_mul_of_pos_left _ hK
  have ha : 0 < σ^2/2 := by positivity
  exact canonicalStockBoundary_strictAntiOn hk hh hhk (mul_pos ha hs) (mul_pos ha ht)
    (mul_lt_mul_of_pos_left hst ha)

theorem brownianUsualStockBoundary_locallyLipschitzOn {K r q σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ) :
    LocallyLipschitzOn (Ioi 0)
      (fun τ : ℝ => brownianUsualExerciseBoundary K r q σ τ.toNNReal) :=
  (brownianUsualStockBoundary_strictConvexOn hK hr hq hqr hσ).convexOn.locallyLipschitzOn isOpen_Ioi

theorem brownianUsualLogBoundary_locallyLipschitzOn {K r q σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ) :
    LocallyLipschitzOn (Ioi 0)
      (fun τ : ℝ => Real.log (brownianUsualExerciseBoundary K r q σ τ.toNNReal/K)) :=
  (brownianUsualLogBoundary_convexOn hK hr hq hqr hσ).locallyLipschitzOn isOpen_Ioi

theorem zeroDividend_brownianUsualLogBoundary_convexOn {K r σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hσ : 0 < σ) :
    ConvexOn ℝ (Ioi 0)
      (fun τ : ℝ => Real.log (brownianUsualExerciseBoundary K r 0 σ τ.toNNReal/K)) :=
  brownianUsualLogBoundary_convexOn hK hr le_rfl hr.le hσ

theorem zeroDividend_brownianUsualStockBoundary_strictConvexOn {K r σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hσ : 0 < σ) :
    StrictConvexOn ℝ (Ioi 0)
      (fun τ : ℝ => brownianUsualExerciseBoundary K r 0 σ τ.toNNReal) :=
  brownianUsualStockBoundary_strictConvexOn hK hr le_rfl hr.le hσ

theorem liuRange_brownianUsualLogBoundary_convexOn {K r q σ : ℝ}
    (hK : 0 < K) (hq : 0 ≤ q) (hσ : 0 < σ) (hliu : q + σ ^ 2 / 2 ≤ r) :
    ConvexOn ℝ (Ioi 0)
      (fun τ : ℝ => Real.log (brownianUsualExerciseBoundary K r q σ τ.toNNReal/K)) := by
  have ha : 0 < σ^2/2 := by positivity
  exact brownianUsualLogBoundary_convexOn hK (by linarith) hq (by linarith) hσ

theorem liuRange_brownianUsualStockBoundary_strictConvexOn {K r q σ : ℝ}
    (hK : 0 < K) (hq : 0 ≤ q) (hσ : 0 < σ) (hliu : q + σ ^ 2 / 2 ≤ r) :
    StrictConvexOn ℝ (Ioi 0)
      (fun τ : ℝ => brownianUsualExerciseBoundary K r q σ τ.toNNReal) := by
  have ha : 0 < σ^2/2 := by positivity
  exact brownianUsualStockBoundary_strictConvexOn hK (by linarith) hq (by linarith) hσ

end MathFin.BlackScholes.AmericanPut.Stopping
