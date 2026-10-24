/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FlatHeatKernel
public import MathFin.BlackScholes.AmericanPut.Stopping.HeatBoundaryExtension

/-! # Interior smoothing of continuous compact boundary data

The boundary datum is not differentiated. A smooth compact cutoff is placed
on the causal kernel, allowing Mathlib's parameter-convolution theorem to apply.

## Result

Public entry points include `causalBoundaryIntegral`, `compact_causalBoundaryIntegral_smooth`,
`heatBoundaryExtension_eq_causalBoundaryIntegral`, `compact_heatBoundaryExtension_smooth`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology ContDiff Convolution

/-- The boundary datum `g` convolved against the causal kernel at depth `x`, namely
`∫ y, causalHeatBoundaryKernel (t-y) x * g y`. -/
noncomputable def causalBoundaryIntegral (g : ℝ → ℝ) (x t : ℝ) : ℝ :=
  ∫ y, causalHeatBoundaryKernel (t-y) x * g y

theorem compact_causalBoundaryIntegral_smooth {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => causalBoundaryIntegral g z.1 z.2) {z | 0 < z.1} := by
  obtain ⟨A,hA⟩ := hc.isBounded.exists_norm_le
  let χ : ContDiffBump (0 : ℝ) := {
    rIn := max A 1
    rOut := max A 1+1
    rIn_pos := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    rIn_lt_rOut := lt_add_one _ }
  have hχ : ∀ y, g y ≠ 0 → χ y = 1 := by
    intro y hy
    apply χ.one_of_mem_closedBall
    change dist y 0 ≤ max A 1
    rw [dist_zero_right]
    exact (hA y (subset_tsupport g hy)).trans (le_max_left _ _)
  have hh := contDiffOn_convolution_left_with_param_comp (μ := volume) (n := (⊤ : ℕ∞))
    (ContinuousLinearMap.mul ℝ ℝ)
    (g := fun z : ℝ × ℝ => fun y => χ y*causalHeatBoundaryKernel (z.2-y) z.1)
    (f := fun y => g (-y)) (v := fun _ : ℝ × ℝ => (0 : ℝ)) contDiffOn_const
    (isOpen_lt continuous_const continuous_fst) χ.hasCompactSupport
    (fun z y _ hy => by rw [image_eq_zero_of_notMem_tsupport hy,zero_mul])
    ((hg.comp continuous_neg).locallyIntegrable) (by
      intro z hz
      have hk := (causalHeatBoundaryKernel_smoothAt (t := z.1.2-z.2) hz.1.ne').comp z
        (show ContDiffAt ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => (z.1.2-z.2,z.1.1)) z by fun_prop)
      exact ((χ.contDiff.contDiffAt.comp z contDiffAt_snd).mul hk).contDiffWithinAt)
  change ContDiffOn ℝ ∞ (fun z : ℝ × ℝ =>
    ∫ y, (χ y*causalHeatBoundaryKernel (z.2-y) z.1)*g (-(0-y))) _ at hh
  simp only [zero_sub,neg_neg] at hh
  apply hh.congr
  intro z _
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change causalHeatBoundaryKernel (z.2-y) z.1*g y =
    (χ y*causalHeatBoundaryKernel (z.2-y) z.1)*g y
  by_cases hy : g y = 0
  · simp [hy]
  · rw [hχ y hy,one_mul]

theorem heatBoundaryExtension_eq_causalBoundaryIntegral (g : ℝ → ℝ)
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    heatBoundaryExtension g x t = causalBoundaryIntegral g x t := by
  rw [heatBoundaryExtension_eq_integral g hx t]
  calc
    (∫ s in Ioi 0, heatBoundaryKernel s x*g (t-s)) =
        ∫ s in Ioi 0, causalHeatBoundaryKernel s x*g (t-s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      change heatBoundaryKernel s x*g (t-s) = causalHeatBoundaryKernel s x*g (t-s)
      rw [causalHeatBoundaryKernel_eq hs hx]
    _ = ∫ s, causalHeatBoundaryKernel s x*g (t-s) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro s hs
      rw [causalHeatBoundaryKernel_zero (le_of_not_gt hs),zero_mul]
    _ = causalBoundaryIntegral g x t := by
      simpa only [causalBoundaryIntegral,sub_sub_cancel] using
        integral_sub_left_eq_self (fun y => causalHeatBoundaryKernel (t-y) x*g y) volume t

theorem compact_heatBoundaryExtension_smooth {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => heatBoundaryExtension g z.1 z.2) {z | 0 < z.1} := by
  apply (compact_causalBoundaryIntegral_smooth hg hc).congr
  intro z hz
  exact heatBoundaryExtension_eq_causalBoundaryIntegral g hz z.2

end MathFin.BlackScholes.AmericanPut.Stopping
