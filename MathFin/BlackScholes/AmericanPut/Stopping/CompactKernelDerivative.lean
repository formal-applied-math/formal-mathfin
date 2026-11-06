/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.HeatBoundarySmoothing

/-! # Differentiation of a continuous compact-data kernel integral

Only the kernel is differentiated. Compactness supplies a uniform local bound
on its derivative, so the datum needs continuity but no derivatives.

## Main results

* `compact_kernelIntegral_hasDeriv`: for continuous compactly supported `g` and a kernel `F`
  with derivative `F'` in `x` on an open set, with `F`, `F'` jointly continuous there, the
  integral `∫ F x y * g y` has derivative `∫ F' x y * g y` at each `x` in the set.

## Tags

kernel integral, differentiation under the integral, compact data, heat kernel derivative,
MSC 35R35, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory Metric
open scoped Topology

theorem compact_kernelIntegral_hasDeriv {g : ℝ → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) {F F' : ℝ → ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U)
    (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (U ×ˢ univ))
    (hF' : ContinuousOn (fun z : ℝ × ℝ => F' z.1 z.2) (U ×ˢ univ))
    (hd : ∀ x ∈ U, ∀ y, HasDerivAt (fun x => F x y) (F' x y) x)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun x => ∫ y, F x y*g y) (∫ y, F' x y*g y) x := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hKU : closedBall x (ε/2) ⊆ U := by
    intro y hy
    apply hball
    exact mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (by linarith))
  have hcompact := (isCompact_closedBall x (ε/2)).prod hc
  have hDc : ContinuousOn (fun z : ℝ × ℝ => F' z.1 z.2)
      (closedBall x (ε/2) ×ˢ tsupport g) := hF'.mono (prod_mono hKU (subset_univ _))
  obtain ⟨C,hC⟩ := (hcompact.image_of_continuousOn hDc).isBounded.exists_norm_le
  have hfc : ∀ u ∈ U, Continuous (F u) := by
    intro u hu
    exact hF.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hu,mem_univ _⟩)
  have hdc : ∀ u ∈ U, Continuous (F' u) := by
    intro u hu
    exact hF'.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hu,mem_univ _⟩)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u y => F u y*g y) (F' := fun u y => F' u y*g y)
    (bound := fun y => C*‖g y‖) (closedBall_mem_nhds x (by linarith : 0 < ε/2))
    (by
      filter_upwards [hU.mem_nhds hx] with u hu
      exact ((hfc u hu).mul hg).aestronglyMeasurable)
    (((hfc x hx).mul hg).integrable_of_hasCompactSupport hc.mul_left)
    (((hdc x hx).mul hg).aestronglyMeasurable)
    (by
      apply Eventually.of_forall
      intro y u hu
      by_cases hy : g y = 0
      · simp [hy]
      · rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact hC (F' u y) (mem_image_of_mem _
          (show (u,y) ∈ closedBall x (ε/2) ×ˢ tsupport g from ⟨hu,subset_tsupport g hy⟩)))
    ((hg.integrable_of_hasCompactSupport hc).norm.const_mul C)
    (Eventually.of_forall fun y u hu => (hd u (hKU hu) y).mul_const (g y))).2

end MathFin.BlackScholes.AmericanPut.Stopping
