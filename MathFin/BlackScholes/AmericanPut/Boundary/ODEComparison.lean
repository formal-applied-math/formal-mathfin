/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Init
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Bound
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic

/-!
# A two-sided Cauchy comparison lemma for a factored real ODE

If `(D-u)(D-v) H ≥ 0` on an interval containing zero, and `H(0)=H'(0)=0`,
then `H ≥ 0` on that interval. Two integrating factors reduce the proof to
ordinary derivative monotonicity. No Cauchy-kernel representation is assumed.

## Main results

* `ode_nonneg_of_factored_forcing`: if `H` is smooth, `H 0 = 0`, `H' 0 = 0` and
  `H'' − (u + v) H' + u v H ≥ 0` on `[a, b]` with `a ≤ 0 ≤ b`, then `H ≥ 0` on `[a, b]`.

## Tags

ODE comparison, integrating factor, Cauchy problem, factored differential operator, MSC 35R35,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open scoped ContDiff

theorem ode_nonneg_of_factored_forcing {H : ℝ → ℝ} {a b u v : ℝ}
    (hH : ContDiff ℝ ∞ H) (ha : a ≤ 0) (hb : 0 ≤ b)
    (hzero : H 0 = 0) (hslope : deriv H 0 = 0)
    (hforcing : ∀ x ∈ Set.Icc a b,
      0 ≤ deriv (deriv H) x - (u + v) * deriv H x + u * v * H x)
    {x : ℝ} (hx : x ∈ Set.Icc a b) : 0 ≤ H x := by
  have hH' : ContDiff ℝ ∞ (deriv H) := (contDiff_infty_iff_deriv.mp hH).2
  have hd (y : ℝ) : HasDerivAt H (deriv H y) y :=
    (hH.differentiable (by simp)).differentiableAt.hasDerivAt
  have hdd (y : ℝ) : HasDerivAt (deriv H) (deriv (deriv H) y) y :=
    (hH'.differentiable (by simp)).differentiableAt.hasDerivAt
  let W : ℝ → ℝ := fun y => Real.exp (-u * y) * (deriv H y - v * H y)
  let U : ℝ → ℝ := fun y => Real.exp (-v * y) * H y
  have hdW (y : ℝ) : HasDerivAt W
      (Real.exp (-u * y) *
        (deriv (deriv H) y - (u + v) * deriv H y + u * v * H y)) y := by
    convert! ((((hasDerivAt_id y).const_mul (-u)).exp).mul
      ((hdd y).sub ((hd y).const_mul v))) using 1
    simp only [id_eq, Pi.sub_apply]
    ring
  have hdU (y : ℝ) : HasDerivAt U
      (Real.exp (-v * y) * (deriv H y - v * H y)) y := by
    convert! ((((hasDerivAt_id y).const_mul (-v)).exp).mul (hd y)) using 1
    simp only [id_eq]
    ring
  have hWcont : Continuous W := (show Differentiable ℝ W from
    fun y => (hdW y).differentiableAt).continuous
  have hUcont : Continuous U := (show Differentiable ℝ U from
    fun y => (hdU y).differentiableAt).continuous
  have hWmono : MonotoneOn W (Set.Icc a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hWcont.continuousOn
      (fun y _ => (hdW y).hasDerivWithinAt) (fun y hy =>
        mul_nonneg (Real.exp_pos _).le (hforcing y (interior_subset hy)))
  have hW0 : W 0 = 0 := by simp [W, hzero, hslope]
  have hU0 : U 0 = 0 := by simp [U, hzero]
  have hUx : 0 ≤ U x := by
    by_cases hxp : 0 ≤ x
    · have hmono : MonotoneOn U (Set.Icc 0 x) :=
        monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x) hUcont.continuousOn
          (fun y _ => (hdU y).hasDerivWithinAt) (by
            intro y hy
            have hy' : y ∈ Set.Icc 0 x := interior_subset hy
            have hWy : 0 ≤ W y := by
              rw [← hW0]
              exact hWmono ⟨ha, hb⟩ ⟨ha.trans hy'.1, hy'.2.trans hx.2⟩ hy'.1
            have hyfactor : 0 ≤ deriv H y - v * H y :=
              (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp hWy
            exact mul_nonneg (Real.exp_pos _).le hyfactor)
      rw [← hU0]
      exact hmono ⟨le_rfl, hxp⟩ ⟨hxp, le_rfl⟩ hxp
    · have hxn : x ≤ 0 := le_of_not_ge hxp
      have hanti : AntitoneOn U (Set.Icc x 0) :=
        antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x 0) hUcont.continuousOn
          (fun y _ => (hdU y).hasDerivWithinAt) (by
            intro y hy
            have hy' : y ∈ Set.Icc x 0 := interior_subset hy
            have hWy : W y ≤ 0 := by
              rw [← hW0]
              exact hWmono ⟨hx.1.trans hy'.1, hy'.2.trans hb⟩ ⟨ha, hb⟩ hy'.2
            have hyfactor : deriv H y - v * H y ≤ 0 := by
              by_contra hn
              have hp := mul_pos (Real.exp_pos (-u * y)) (lt_of_not_ge hn)
              exact (not_lt_of_ge hWy) hp
            exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hyfactor)
      rw [← hU0]
      exact hanti ⟨le_rfl, hxn⟩ ⟨hxn, le_rfl⟩ hxn
  exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp hUx

end MathFin.BlackScholes.AmericanPut.Boundary
