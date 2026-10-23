/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualGradientTrace
public import MathFin.BlackScholes.AmericanPut.Stopping.ConvexSliceGradient

/-! # Spatial differentiability across the actual exercise boundary

The exercise-side derivative joins the proved right smooth fit. This proves
spatial differentiability of the actual price at every positive maturity.
Convex stock slices then give joint continuity of the spatial gradient, without
differentiability of the free boundary.

## Result

Public entry points include `canonicalPrice_exercise_value`, `canonicalPrice_hasDerivAt_boundary`,
`canonicalPrice_hasDerivAt_exercise`, `canonicalPrice_differentiableAt_spatial`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary
open scoped Topology

theorem canonicalPrice_exercise_value {k h x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t)
    (hx : x ≤ canonicalLogBoundary k h t) :
    canonicalPrice k h x t = 1-Real.exp x := by
  rw [(canonicalPrice_contact_iff_logBoundary hk hh hhk ht).mpr hx]
  exact putPayoff_of_nonpos (hx.trans (canonicalLogBoundary_neg hk hh hhk ht).le)

theorem canonicalPrice_hasDerivAt_boundary {k h t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t) :
    HasDerivAt (fun x => canonicalPrice k h x t)
      (-Real.exp (canonicalLogBoundary k h t)) (canonicalLogBoundary k h t) := by
  let b := canonicalLogBoundary k h t
  have he : HasDerivAt (fun x : ℝ => 1-Real.exp x) (-Real.exp b) b := by
    exact (Real.hasDerivAt_exp b).const_sub 1
  have hl : HasDerivWithinAt (fun x => canonicalPrice k h x t) (-Real.exp b) (Iic b) b :=
    he.hasDerivWithinAt.congr_of_mem
      (fun x hx => canonicalPrice_exercise_value hk hh hhk ht hx) (by simp)
  have hu := hl.union (canonicalPrice_smooth_fit hk hh hhk ht)
  rw [Iic_union_Ici] at hu
  exact hu.hasDerivAt (by simp)

theorem canonicalPrice_hasDerivAt_exercise {k h x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t)
    (hx : x ≤ canonicalLogBoundary k h t) :
    HasDerivAt (fun y => canonicalPrice k h y t) (-Real.exp x) x := by
  rcases hx.eq_or_lt with he | hx
  · rw [he]
    exact canonicalPrice_hasDerivAt_boundary hk hh hhk ht
  · have he : HasDerivAt (fun y : ℝ => 1-Real.exp y) (-Real.exp x) x := by
      exact (Real.hasDerivAt_exp x).const_sub 1
    apply he.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact canonicalPrice_exercise_value hk hh hhk ht (le_of_lt hy)

theorem canonicalPrice_differentiableAt_spatial {k h t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t) (x : ℝ) :
    DifferentiableAt ℝ (fun y => canonicalPrice k h y t) x := by
  rcases le_or_gt x (canonicalLogBoundary k h t) with hx | hx
  · exact (canonicalPrice_hasDerivAt_exercise hk hh hhk ht hx).differentiableAt
  · apply canonicalPrice_differentiableAt_continuation hk.le ht
    rw [← exp_canonicalLogBoundary hk hh hhk ht.le]
    exact Real.exp_lt_exp.mpr hx

theorem canonicalStockPrice_differentiableAt_spatial {k h S t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t) (hS : 0 < S) :
    DifferentiableAt ℝ (fun R => canonicalStockPrice k h R t) S := by
  have hc := (canonicalPrice_differentiableAt_spatial hk hh hhk ht (Real.log S)).hasDerivAt.comp S
    (Real.hasDerivAt_log hS.ne')
  apply (hc.congr_of_eventuallyEq ?_).differentiableAt
  filter_upwards [Ioi_mem_nhds hS] with R hR
  exact canonicalStockPrice_eq_log k h t hR

theorem canonicalStockPrice_continuousAt {k h S t : ℝ} (hk : 0 ≤ k) (hS : 0 < S) :
    ContinuousAt (fun z : ℝ × ℝ => canonicalStockPrice k h z.1 z.2) (S,t) := by
  have hm : ContinuousAt (fun z : ℝ × ℝ => (Real.log z.1,z.2)) (S,t) := by
    fun_prop (disch := exact hS.ne')
  have hc := (canonicalPrice_continuous (h := h) hk).continuousAt.comp
    (f := fun z : ℝ × ℝ => (Real.log z.1,z.2)) hm
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.preimage_mem_nhds (Ioi_mem_nhds hS)] with z hz
  exact canonicalStockPrice_eq_log k h z.2 hz

theorem canonicalStockPrice_gradient_continuousAt {k h S t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t) (hS : 0 < S) :
    ContinuousAt (fun z : ℝ × ℝ => deriv (fun R => canonicalStockPrice k h R z.2) z.1) (S,t) :=
  continuousAt_deriv_convex_slices
    (fun t _ => canonicalStockPrice_convexOn hk.le t)
    (fun _ _ hS ht => canonicalStockPrice_differentiableAt_spatial hk hh hhk ht hS)
    (fun _ _ hS _ => canonicalStockPrice_continuousAt hk.le hS) hS ht

theorem canonicalPrice_spatial_deriv_eq_stock {k h x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t) :
    deriv (fun y => canonicalPrice k h y t) x =
      deriv (fun S => canonicalStockPrice k h S t) (Real.exp x)*Real.exp x :=
  ((canonicalStockPrice_differentiableAt_spatial hk hh hhk ht (Real.exp_pos x)).hasDerivAt.comp x
    (Real.hasDerivAt_exp x)).deriv

/-- Joint continuity holds across the free boundary, not just along a fixed
maturity slice or from within continuation. -/
theorem canonicalPrice_gradient_continuousAt {k h x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t) :
    ContinuousAt (fun z : ℝ × ℝ => deriv (fun y => canonicalPrice k h y z.2) z.1) (x,t) := by
  have hm : ContinuousAt (fun z : ℝ × ℝ => (Real.exp z.1,z.2)) (x,t) := by fun_prop
  have hg := (canonicalStockPrice_gradient_continuousAt hk hh hhk ht (Real.exp_pos x)).comp
    (f := fun z : ℝ × ℝ => (Real.exp z.1,z.2)) hm
  have he : ContinuousAt (fun z : ℝ × ℝ => Real.exp z.1) (x,t) := by fun_prop
  apply (hg.mul he).congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.preimage_mem_nhds (Ioi_mem_nhds ht)] with z hz
  exact canonicalPrice_spatial_deriv_eq_stock hk hh hhk hz

theorem zeroDividend_canonicalPrice_gradient_continuousAt {k x t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    ContinuousAt (fun z : ℝ × ℝ => deriv (fun y => canonicalPrice k 0 y z.2) z.1) (x,t) :=
  canonicalPrice_gradient_continuousAt hk le_rfl hk.le ht

theorem liuRange_canonicalPrice_gradient_continuousAt {k h x t : ℝ}
    (hh : 0 ≤ h) (hliu : h + 1 ≤ k) (ht : 0 < t) :
    ContinuousAt (fun z : ℝ × ℝ => deriv (fun y => canonicalPrice k h y z.2) z.1) (x,t) :=
  canonicalPrice_gradient_continuousAt (by linarith) hh (by linarith) ht

end MathFin.BlackScholes.AmericanPut.Stopping
