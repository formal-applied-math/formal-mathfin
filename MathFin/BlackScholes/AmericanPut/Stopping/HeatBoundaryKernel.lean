/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ContinuousHeatSmoothing
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # The half-line heat boundary kernel

For diffusivity 1/2 the boundary kernel is H(t,x)=x*K(t,x)/t.
This file proves its positive-time PDE and exact temporal normalization.
It does not yet construct a finite-interval boundary solution.

## Result

Public entry points include `heatBoundaryKernel`, `heatKernel_hasDeriv_time`,
`heatKernel_hasDeriv_space`, `heatBoundaryKernel_smoothAt`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open MathFin.FeynmanKacHeatEquation
open scoped Topology ContDiff

/-- The half-line heat boundary kernel `H(t,x) = x/t * heatKernel t x`. -/
noncomputable def heatBoundaryKernel (t x : ℝ) : ℝ := x/t*heatKernel t x

theorem heatKernel_hasDeriv_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatKernel s x) (heatKernel t x*(x^2-t)/(2*t^2)) t := by
  convert! (hasFDerivAt_heatKernel ht x).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)) using 1
  simp

theorem heatKernel_hasDeriv_space {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (heatKernel t) (-(x/t)*heatKernel t x) x := by
  convert! (hasFDerivAt_heatKernel ht x).comp_hasDerivAt x
    ((hasDerivAt_const x t).prodMk (hasDerivAt_id x)) using 1
  simp

theorem heatBoundaryKernel_smoothAt {t x : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => heatBoundaryKernel z.1 z.2) (t,x) :=
  (contDiffAt_snd.div contDiffAt_fst ht.ne').mul (heatKernel_smoothAt ht)

theorem heatBoundaryKernel_pos {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    0 < heatBoundaryKernel t x := by
  unfold heatBoundaryKernel heatKernel
  positivity

theorem heatBoundaryKernel_odd (t x : ℝ) : heatBoundaryKernel t (-x) = -heatBoundaryKernel t x := by
  simp [heatBoundaryKernel,heatKernel]
  ring

theorem heatBoundaryKernel_hasDeriv_space {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (heatBoundaryKernel t) ((t-x^2)/t^2*heatKernel t x) x := by
  convert! ((hasDerivAt_id x).div_const t).mul (heatKernel_hasDeriv_space ht x) using 1
  simp only [id_eq]
  field_simp
  ring

theorem heatBoundaryKernel_hasDeriv_space2 {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (deriv (heatBoundaryKernel t))
      (x*(x^2-3*t)/t^3*heatKernel t x) x := by
  have he : deriv (heatBoundaryKernel t) = fun y => (t-y^2)/t^2*heatKernel t y :=
    funext (fun y => (heatBoundaryKernel_hasDeriv_space ht y).deriv)
  rw [he]
  convert! ((((hasDerivAt_const x t).sub ((hasDerivAt_id x).pow 2)).div_const (t^2)).mul
    (heatKernel_hasDeriv_space ht x)) using 1
  simp only [id_eq,Pi.sub_apply,Pi.pow_apply]
  field_simp
  ring

theorem heatBoundaryKernel_hasDeriv_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatBoundaryKernel s x)
      (x*(x^2-3*t)/(2*t^3)*heatKernel t x) t := by
  convert! (((hasDerivAt_const t x).div (hasDerivAt_id t) ht.ne').mul
    (heatKernel_hasDeriv_time ht x)) using 1
  simp only [id_eq,Pi.div_apply]
  field_simp
  ring

theorem heatBoundaryKernel_equation {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun s => heatBoundaryKernel s x) t = (1/2)*deriv (deriv (heatBoundaryKernel t)) x := by
  rw [(heatBoundaryKernel_hasDeriv_time ht x).deriv,(heatBoundaryKernel_hasDeriv_space2 ht x).deriv]
  ring

theorem heatBoundaryKernel_inverse_square (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (2*y^(-3 : ℝ))*heatBoundaryKernel (y^(-2 : ℝ)) x =
      (2*x/Real.sqrt (2*Real.pi))*Real.exp (-(x^2/2)*y^2) := by
  have hs : Real.sqrt (2*Real.pi*(y^2)⁻¹) = Real.sqrt (2*Real.pi)/y := by
    rw [Real.sqrt_mul (by positivity),Real.sqrt_inv,Real.sqrt_sq_eq_abs,abs_of_pos hy]
    rfl
  have he : -(x^2)/(2*(y^2)⁻¹) = -(x^2/2)*y^2 := by field_simp
  unfold heatBoundaryKernel heatKernel
  simp only [Real.rpow_neg_ofNat,zpow_neg,zpow_ofNat]
  rw [hs,he]
  field_simp

/-- Unit mass in elapsed time is the normalization needed for a boundary trace. -/
theorem heatBoundaryKernel_integral {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi 0, heatBoundaryKernel t x) = 1 := by
  have he := integral_comp_rpow_Ioi (fun t => heatBoundaryKernel t x)
    (p := (-2 : ℝ)) (by norm_num)
  have hf : (∫ y in Ioi 0, (|(-2 : ℝ)| * y^((-2 : ℝ)-1)) • heatBoundaryKernel (y^(-2 : ℝ)) x) =
      ∫ y in Ioi 0, (2*x/Real.sqrt (2*Real.pi))*Real.exp (-(x^2/2)*y^2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    norm_num only [abs_neg,show |(2 : ℝ)| = 2 by norm_num,
      show (-2 : ℝ)-1 = -3 by norm_num,smul_eq_mul]
    exact heatBoundaryKernel_inverse_square x hy
  rw [← he,hf,integral_const_mul,integral_gaussian_Ioi]
  have hs : Real.sqrt (Real.pi/(x^2/2)) = Real.sqrt (2*Real.pi)/x := by
    rw [show Real.pi/(x^2/2) = (2*Real.pi)/x^2 by field_simp,
      Real.sqrt_div (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hx]
  rw [hs]
  have hsne : Real.sqrt (2*Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

theorem heatBoundaryKernel_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => heatBoundaryKernel t x) (Ioi 0) := by
  by_contra hn
  have he := heatBoundaryKernel_integral hx
  rw [integral_undef hn] at he
  norm_num at he

/-- Parabolic scaling turns the boundary kernels into a fixed probability density. -/
theorem heatBoundaryKernel_scale {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    x^2 * heatBoundaryKernel (x^2*t) x = heatBoundaryKernel t 1 := by
  have hs : Real.sqrt (2*Real.pi*(x^2*t)) = x*Real.sqrt (2*Real.pi*t) := by
    rw [show 2*Real.pi*(x^2*t) = x^2*(2*Real.pi*t) by ring,
      Real.sqrt_mul (sq_nonneg x),Real.sqrt_sq_eq_abs,abs_of_pos hx]
  have he : -(x^2)/(2*(x^2*t)) = -(1 : ℝ)^2/(2*t) := by
    field_simp
  unfold heatBoundaryKernel heatKernel
  rw [hs,he]
  field_simp

end MathFin.BlackScholes.AmericanPut.Stopping
