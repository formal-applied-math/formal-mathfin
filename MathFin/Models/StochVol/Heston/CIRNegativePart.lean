/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.CIRApproximation
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# CIRNegative Part

The C² negative-part test function used for nonnegativity of the regularized
CIR process. This file proves its calculus, not a stochastic Itô application.

## Main definitions

* `cirNegativePart`
* `cirNegativePartDeriv`
* `cirNegativePartDeriv2`

## Main results

* `contDiff_cirNegativePart`
* `cirNegativePart_diffusion_cancel`
* `cirNegativePart_drift_nonpos`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston
open Filter Set
open scoped Topology

def cirNegativePart (x : Real) : Real := (max (-x) 0)^3
def cirNegativePartDeriv (x : Real) : Real := -3 * (max (-x) 0)^2
def cirNegativePartDeriv2 (x : Real) : Real := 6 * max (-x) 0

theorem cirNegativePart_nonneg (x : Real) : 0 ≤ cirNegativePart x := by
  unfold cirNegativePart
  positivity

theorem cirNegativePart_zero_iff (x : Real) : cirNegativePart x = 0 ↔ 0 ≤ x := by
  by_cases hx : 0 ≤ x
  · simp [cirNegativePart, hx]
  · have hnx : 0 < -x := neg_pos.mpr (lt_of_not_ge hx)
    have hh : 0 < cirNegativePart x := by
      simpa only [cirNegativePart, max_eq_left hnx.le] using pow_pos hnx 3
    simp only [hh.ne', hx]

theorem hasDerivAt_cirNegativePart_zero : HasDerivAt cirNegativePart 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have he : slope cirNegativePart 0 = fun x : Real => -(max (-x) 0)^2 := by
    funext x
    by_cases hx : 0 ≤ x
    · simp [slope, cirNegativePart, max_eq_right (neg_nonpos.mpr hx)]
    · have hn : 0 < -x := neg_pos.mpr (lt_of_not_ge hx)
      simp [slope, cirNegativePart, vsub_eq_sub, max_eq_left hn.le]
      field_simp [ne_of_lt (lt_of_not_ge hx)]
  rw [he]
  have hc : Continuous (fun x : Real => -(max (-x) 0)^2) := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem hasDerivAt_cirNegativePart (x : Real) :
    HasDerivAt cirNegativePart (cirNegativePartDeriv x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : cirNegativePart =ᶠ[𝓝 x] fun y : Real => (-y)^3 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp only [cirNegativePart, max_eq_left (neg_nonneg.mpr (show y < 0 from hy).le)]
    convert! ((hasDerivAt_id x).neg.pow 3).congr_of_eventuallyEq he using 1
    simp only [cirNegativePartDeriv, max_eq_left (neg_nonneg.mpr hx.le)]
    dsimp
    ring
  · simpa [cirNegativePartDeriv] using hasDerivAt_cirNegativePart_zero
  · have he : cirNegativePart =ᶠ[𝓝 x] fun _ : Real => 0 := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [cirNegativePart, max_eq_right (neg_nonpos.mpr (show 0 < y from hy).le)]
    simpa [cirNegativePartDeriv, max_eq_right (neg_nonpos.mpr hx.le)] using
      (hasDerivAt_const x (0 : Real)).congr_of_eventuallyEq he

theorem hasDerivAt_cirNegativePartDeriv_zero : HasDerivAt cirNegativePartDeriv 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have he : slope cirNegativePartDeriv 0 = fun x : Real => 3 * max (-x) 0 := by
    funext x
    by_cases hx : 0 ≤ x
    · simp [slope, cirNegativePartDeriv, max_eq_right (neg_nonpos.mpr hx)]
    · have hn : 0 < -x := neg_pos.mpr (lt_of_not_ge hx)
      simp [slope, cirNegativePartDeriv, vsub_eq_sub, max_eq_left hn.le]
      field_simp [ne_of_lt (lt_of_not_ge hx)]
  rw [he]
  have hc : Continuous (fun x : Real => 3 * max (-x) 0) := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem hasDerivAt_cirNegativePartDeriv (x : Real) :
    HasDerivAt cirNegativePartDeriv (cirNegativePartDeriv2 x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : cirNegativePartDeriv =ᶠ[𝓝 x] fun y : Real => -3 * (-y)^2 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp only [cirNegativePartDeriv, max_eq_left (neg_nonneg.mpr (show y < 0 from hy).le)]
    convert! (((hasDerivAt_id x).neg.pow 2).const_mul (-3)).congr_of_eventuallyEq he using 1
    simp only [cirNegativePartDeriv2, max_eq_left (neg_nonneg.mpr hx.le)]
    dsimp
    ring
  · simpa [cirNegativePartDeriv2] using hasDerivAt_cirNegativePartDeriv_zero
  · have he : cirNegativePartDeriv =ᶠ[𝓝 x] fun _ : Real => 0 := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [cirNegativePartDeriv, max_eq_right (neg_nonpos.mpr (show 0 < y from hy).le)]
    simpa [cirNegativePartDeriv2, max_eq_right (neg_nonpos.mpr hx.le)] using
      (hasDerivAt_const x (0 : Real)).congr_of_eventuallyEq he

theorem continuous_cirNegativePartDeriv2 : Continuous cirNegativePartDeriv2 := by
  unfold cirNegativePartDeriv2
  fun_prop

theorem contDiff_cirNegativePart : ContDiff Real 2 cirNegativePart := by
  have hd : deriv cirNegativePart = cirNegativePartDeriv :=
    funext (fun x => (hasDerivAt_cirNegativePart x).deriv)
  have hdd : deriv cirNegativePartDeriv = cirNegativePartDeriv2 :=
    funext (fun x => (hasDerivAt_cirNegativePartDeriv x).deriv)
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_cirNegativePart x).differentiableAt, ?_, ?_⟩
  · norm_num
  · rw [hd, contDiff_one_iff_deriv, hdd]
    exact ⟨fun x => (hasDerivAt_cirNegativePartDeriv x).differentiableAt,
      continuous_cirNegativePartDeriv2⟩

theorem cirNegativePart_diffusion_cancel (ε x : Real) :
    cirNegativePartDeriv x * cirApproxDiff ε x = 0 ∧
      cirNegativePartDeriv2 x * cirApproxDiff ε x ^ 2 = 0 := by
  rcases le_total x 0 with hx | hx
  · simp [cirApproxDiff_of_nonpos hx]
  · simp [cirNegativePartDeriv, cirNegativePartDeriv2, max_eq_right (neg_nonpos.mpr hx)]

theorem cirNegativePart_drift_nonpos (κ θ x : Real) (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) :
    cirNegativePartDeriv x * (κ * (θ - x)) ≤ 0 := by
  rcases le_total x 0 with hx | hx
  · apply mul_nonpos_of_nonpos_of_nonneg
    · unfold cirNegativePartDeriv
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)
    · exact mul_nonneg hκ (by linarith)
  · simp [cirNegativePartDeriv, max_eq_right (neg_nonpos.mpr hx)]

end MathFin.Heston
