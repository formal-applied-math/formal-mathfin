/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.CompactHeatFlow

/-! # Heat smoothing of continuous, not necessarily differentiable, data

A smooth cutoff is placed on the kernel factor in the convolution theorem.
No derivatives of the initial datum are taken.

## Result

Public entry points include `heatKernel_smoothAt`, `compact_continuous_heatFlow_smooth`,
`compact_continuous_heatFlow_contDiff`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open MathFin.FeynmanKacHeatEquation
open scoped Topology ContDiff Convolution

theorem heatKernel_smoothAt {t x : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => heatKernel z.1 z.2) (t,x) := by
  unfold heatKernel
  fun_prop (disch := positivity)

theorem compact_continuous_heatFlow_smooth {f : ℝ → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => feynmanU f z.1 z.2) {z | 0 < z.1} := by
  obtain ⟨A,hA⟩ := hc.isBounded.exists_norm_le
  let χ : ContDiffBump (0 : ℝ) := {
    rIn := max A 1
    rOut := max A 1+1
    rIn_pos := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    rIn_lt_rOut := lt_add_one _ }
  have hχ : ∀ y, f y ≠ 0 → χ y = 1 := by
    intro y hy
    apply χ.one_of_mem_closedBall
    change dist y 0 ≤ max A 1
    rw [dist_zero_right]
    exact (hA y (subset_tsupport f hy)).trans (le_max_left _ _)
  have hh := contDiffOn_convolution_left_with_param_comp (μ := volume) (n := (⊤ : ℕ∞))
    (ContinuousLinearMap.mul ℝ ℝ) (g := fun z : ℝ × ℝ => fun y => χ y*heatKernel z.1 (y-z.2))
    (f := fun y => f (-y)) (v := fun _ : ℝ × ℝ => (0 : ℝ)) contDiffOn_const
    (isOpen_lt continuous_const continuous_fst) χ.hasCompactSupport
    (fun z y _ hy => by rw [image_eq_zero_of_notMem_tsupport hy,zero_mul])
    ((hf.comp continuous_neg).locallyIntegrable) (by
      intro z hz
      have hk := (heatKernel_smoothAt (x := z.2-z.1.2) hz.1).comp z
        (show ContDiffAt ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => (z.1.1,z.2-z.1.2)) z by fun_prop)
      exact ((χ.contDiff.contDiffAt.comp z contDiffAt_snd).mul hk).contDiffWithinAt)
  change ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => ∫ y, (χ y*heatKernel z.1 (y-z.2))*f (-(0-y))) _ at hh
  simp only [zero_sub,neg_neg] at hh
  apply hh.congr
  intro z _
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change f y*heatKernel z.1 (y-z.2) = (χ y*heatKernel z.1 (y-z.2))*f y
  by_cases hy : f y = 0
  · simp [hy]
  · rw [hχ y hy,one_mul]
    exact mul_comm _ _

theorem compact_continuous_heatFlow_contDiff {f : ℝ → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    ContDiffOn ℝ 2 (fun z : ℝ × ℝ => feynmanU f z.1 z.2) {z | 0 < z.1} :=
  (compact_continuous_heatFlow_smooth hf hc).of_le (WithTop.coe_le_coe.mpr le_top)

end MathFin.BlackScholes.AmericanPut.Stopping
