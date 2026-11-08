/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Models.BlackScholes.American.Boundary.ComparisonConclusion

/-!
# Zero speed would force a permanently flat boundary

This is a consequence of the now-proved weak log curvature and boundary
monotonicity. The separate parabolic exclusion is proved in `StrictBoundarySpeed`.

## Main results

* `boundary_deriv_monoOn`: for a `DividendPutSolution`, `deriv b` is monotone on `(0, ∞)`.
* `boundary_flat_tail_of_zero_speed`: if `T > 0` and `deriv b T = 0`, then `b t = b T` for all
  `t ≥ T`.

## Tags

flat boundary, zero speed, boundary derivative, log curvature, MSC 35R35, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.DividendPutSolution

open Set
open scoped Topology ContDiff

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem boundary_deriv_monoOn (hp : DividendPutSolution k h p b) :
    MonotoneOn (deriv b) (Ioi 0) := by
  have hd (t : ℝ) (ht : 0 < t) : DifferentiableAt ℝ (deriv b) t := by
    have hs : ContDiffAt ℝ 2 b t :=
      (hp.boundary_smooth.contDiffAt (Ioi_mem_nhds ht)).of_le (WithTop.coe_le_coe.mpr le_top)
    exact (hs.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableWithinAt
  · intro t ht
    exact Comparison.dividend_log_curvature hp t (interior_subset ht)

theorem boundary_flat_tail_of_zero_speed (hp : DividendPutSolution k h p b)
    {T : ℝ} (hT : 0 < T) (hz : deriv b T = 0) :
    ∀ t, T ≤ t → b t = b T := by
  have hzero (t : ℝ) (ht : T ≤ t) : deriv b t = 0 := by
    have hmono := hp.boundary_deriv_monoOn hT (hT.trans_le ht) ht
    rw [hz] at hmono
    exact le_antisymm (hp.boundary_deriv_nonpos (hT.trans_le ht)) hmono
  intro t ht
  rcases eq_or_lt_of_le ht with he | hlt
  · rw [he]
  have hd (s : ℝ) (hs : T ≤ s) : DifferentiableAt ℝ b s :=
    (hp.boundary_smooth.contDiffAt (Ioi_mem_nhds (hT.trans_le hs))).differentiableAt (by simp)
  obtain ⟨s,hs,hder⟩ := exists_deriv_eq_slope b hlt
    (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hd s hs.1.le).differentiableWithinAt)
  rw [hzero s hs.1.le,eq_div_iff (ne_of_gt (sub_pos.mpr hlt))] at hder
  linarith

end MathFin.BlackScholes.AmericanPut.Boundary.DividendPutSolution
