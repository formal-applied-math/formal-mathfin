/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualSpatialRegularity

/-! # Strict separation of the continuation slope from the exercise slope

Stock-price convexity bounds the derivative below by the secant from the
exercise boundary. Strict price/payoff separation makes that bound strictly
greater than -1 in stock coordinates, hence greater than -exp(x) in log spot.

## Result

Public entry points include `canonicalPrice_spatial_deriv_gt_exercise`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Boundary

theorem canonicalPrice_spatial_deriv_gt_exercise {k h x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t)
    (hx : canonicalLogBoundary k h t < x) :
    -Real.exp x < deriv (fun y => canonicalPrice k h y t) x := by
  let B := canonicalStockBoundary k h t
  have hB : 0 < B := canonicalStockBoundary_pos hk hh hhk ht.le
  have hBS : B < Real.exp x := by
    dsimp only [B]
    rw [← exp_canonicalLogBoundary hk hh hhk ht.le]
    exact Real.exp_lt_exp.mpr hx
  have hcontact : canonicalStockPrice k h B t = 1-B := by
    dsimp only [B]
    rw [← exp_canonicalLogBoundary hk hh hhk ht.le,canonicalStockPrice_exp,
      canonicalPrice_value_matching hk hh hhk ht]
  have hstrict : 1-Real.exp x < canonicalStockPrice k h (Real.exp x) t :=
    (le_max_left _ _).trans_lt ((canonicalPrice_strict_continuation_iff hk.le x ht).mpr hBS)
  have hsec := (canonicalStockPrice_convexOn (h := h) hk.le t).slope_le_deriv hB.le
    (Real.exp_pos x).le hBS
        (canonicalStockPrice_differentiableAt_spatial hk hh hhk ht (Real.exp_pos x))
  have hsecpos : -1 < slope (fun S => canonicalStockPrice k h S t) B (Real.exp x) := by
    simp only [slope,vsub_eq_sub,smul_eq_mul,← div_eq_inv_mul,hcontact]
    apply (lt_div_iff₀ (sub_pos.mpr hBS)).mpr
    linarith
  rw [canonicalPrice_spatial_deriv_eq_stock hk hh hhk ht]
  have he := mul_lt_mul_of_pos_right (hsecpos.trans_le hsec) (Real.exp_pos x)
  simpa only [neg_one_mul] using he

end MathFin.BlackScholes.AmericanPut.Stopping
