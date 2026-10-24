/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.WindowComparison
public import MathFin.Foundations.FeynmanKacHeatEquation

/-!
# Smooth heat evolution of compactly supported test payoffs

These are comparison functions, not an assumption that the American price
itself is smooth across exercise. The compact-support hypothesis gives joint
smoothness; scaling extends MathFin's kernel-side heat equation to arbitrary
compactly supported continuous data.

## Result

Public entry points include `contDiffOn_compact_parameter_integral`, `heatKernel_contDiffAt`,
`compact_heatFlow_contDiff`, `compact_exponential_bound`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open MathFin.FeynmanKacHeatEquation
open scoped Topology ContDiff Convolution

theorem contDiffOn_compact_parameter_integral {H : (ℝ × ℝ) → ℝ → ℝ}
    {U : Set (ℝ × ℝ)} {C : Set ℝ} (hU : IsOpen U) (hC : IsCompact C)
    (hzero : ∀ z y, z ∈ U → y ∉ C → H z y = 0)
    (hH : ContDiffOn ℝ 2 (Function.uncurry H) (U ×ˢ univ)) :
    ContDiffOn ℝ 2 (fun z => ∫ y, H z y) U := by
  have hh := contDiffOn_convolution_left_with_param_comp (μ := volume)
    (ContinuousLinearMap.mul ℝ ℝ) (g := H) (f := fun _ : ℝ => (1 : ℝ))
    (v := fun _ : ℝ × ℝ => (0 : ℝ)) contDiffOn_const hU hC hzero
    (continuous_const.locallyIntegrable) hH
  change ContDiffOn ℝ 2 (fun z => ∫ y, H z y*1) U at hh
  simpa only [mul_one] using hh

theorem heatKernel_contDiffAt {t x : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => heatKernel z.1 z.2) (t,x) := by
  unfold heatKernel
  fun_prop (disch := positivity)

theorem compact_heatFlow_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ContDiffOn ℝ 2 (fun z : ℝ × ℝ => feynmanU f z.1 z.2) {z | 0 < z.1} := by
  apply contDiffOn_compact_parameter_integral (isOpen_lt continuous_const continuous_fst) hc
    (H := fun z y => f y*heatKernel z.1 (y-z.2))
  · intro z y _ hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  · intro z hz
    have hk := (heatKernel_contDiffAt (x := z.2-z.1.2) hz.1).comp z
      (show ContDiffAt ℝ 2 (fun z : (ℝ × ℝ) × ℝ => (z.1.1,z.2-z.1.2)) z by fun_prop)
    exact ((hf.contDiffAt.comp z contDiffAt_snd).mul hk).contDiffWithinAt

theorem compact_exponential_bound {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |f x| ≤ C*Real.exp x := by
  let F : ℝ → ℝ := fun x => |f x| * Real.exp (-x)
  have hFc : Continuous F := hf.abs.mul (by fun_prop)
  have hFs : HasCompactSupport F := hc.abs.mul_right
  obtain ⟨C,hC⟩ := (hFs.isCompact_range hFc).bddAbove
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right C 1),fun x => ?_⟩
  have hh := mul_le_mul_of_nonneg_right ((hC (mem_range_self x)).trans (le_max_left C 1))
    (Real.exp_pos x).le
  simpa [F,← mul_assoc,Real.exp_neg,mul_assoc] using hh

theorem compact_heatFlow_equation {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun s => feynmanU f s x) t = (1/2)*deriv (deriv (feynmanU f t)) x := by
  obtain ⟨C,hC,hbound⟩ := compact_exponential_bound hf hc
  let g : ℝ → ℝ := fun y => f y/C
  have hgc : Continuous g := hf.div_const C
  have hgb : ∀ y, |g y| ≤ Real.exp y := by
    intro y
    simpa [g,abs_div,abs_of_pos hC] using
      (div_le_iff₀ hC).mpr (show |f y| ≤ Real.exp y*C by simpa [mul_comm] using hbound y)
  have hscale : ∀ s y, feynmanU f s y = C*feynmanU g s y := by
    intro s y
    unfold feynmanU
    rw [← integral_const_mul]
    congr 1
    funext z
    dsimp [g]
    field_simp
  have hdx : deriv (feynmanU g t) =
      fun y => ∫ z, g z*((z-y)/t*heatKernel t (z-y)) :=
    funext (fun y => (hasDerivAt_feynmanU_x ht hgc hgb y).deriv)
  have heq : deriv (fun s => feynmanU g s x) t = (1/2)*deriv (deriv (feynmanU g t)) x := by
    rw [(hasDerivAt_feynmanU_t ht hgc hgb x).deriv,hdx,
      (hasDerivAt_feynmanU_xx ht hgc hgb x).deriv]
    exact feynmanU_heat_equation ht g x
  rw [show feynmanU f t = fun y => C*feynmanU g t y from funext (hscale t)]
  simp_rw [hscale]
  rw [deriv_const_mul_field,deriv_const_mul_field',deriv_const_mul_field,heq]
  ring

end MathFin.BlackScholes.AmericanPut.Stopping
