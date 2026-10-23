/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ParabolicMaximum
public import Mathlib

/-!
# A positive polynomial barrier for bounded-drift parabolic equations

The profile `x^2*(L-x)^2` vanishes at both ends and is positive inside.
An explicit exponential time factor makes it a subsolution for every drift
whose absolute value is bounded by `M`. This is a propagation barrier, not
an assumed strong maximum principle.

## Result

Public entry points include `positiveBump`, `positiveBump_contDiff`, `positiveBump_hasDeriv`,
`positiveBump_deriv2`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set
open scoped ContDiff

/-- The quartic `x ^ 2 * (L - x) ^ 2`, vanishing to second order at `0` and at `L`. -/
noncomputable def positiveBump (L x : ℝ) : ℝ := x^2*(L-x)^2

theorem positiveBump_contDiff (L : ℝ) : ContDiff ℝ ∞ (positiveBump L) := by
  unfold positiveBump
  fun_prop

theorem positiveBump_hasDeriv (L x : ℝ) :
    HasDerivAt (positiveBump L) (2*x*(L-x)*(L-2*x)) x := by
  convert! ((hasDerivAt_id x).pow 2).mul (((hasDerivAt_id x).const_sub L).pow 2) using 1
  simp only [id_eq, Pi.pow_apply]
  ring

theorem positiveBump_deriv2 (L x : ℝ) :
    deriv (deriv (positiveBump L)) x = 2*(L-2*x)^2-4*x*(L-x) := by
  rw [show deriv (positiveBump L) = fun y => 2*y*(L-y)*(L-2*y) from
    funext (fun y => (positiveBump_hasDeriv L y).deriv)]
  convert! ((((hasDerivAt_id x).const_mul 2).mul ((hasDerivAt_id x).const_sub L)).mul
    (((hasDerivAt_id x).const_mul 2).const_sub L)).deriv using 1
  simp only [id_eq, Pi.mul_apply]
  ring

theorem positiveBump_pos {L x : ℝ} (hx : 0 < x) (hxL : x < L) : 0 < positiveBump L x := by
  unfold positiveBump
  positivity

theorem positiveBump_operator {L M D x : ℝ} (hL : 0 < L) (hD : |D| ≤ M) :
    0 ≤ deriv (deriv (positiveBump L)) x + D*deriv (positiveBump L) x +
      (M^2+16/L^2)*positiveBump L x := by
  rw [positiveBump_deriv2, (positiveBump_hasDeriv L x).deriv]
  have hMD : 0 ≤ M^2-D^2 := by nlinarith [sq_abs D, abs_nonneg D]
  have hid : 2*(L-2*x)^2-4*x*(L-x) + D*(2*x*(L-x)*(L-2*x)) +
      (M^2+16/L^2)*positiveBump L x =
      (L-2*x+D*x*(L-x))^2 + (L-4*x*(L-x)/L)^2 + (M^2-D^2)*(x*(L-x))^2 := by
    unfold positiveBump
    field_simp
    ring
  rw [hid]
  positivity

/-- `positiveBump L` scaled by `η` and by the time factor
`Real.exp (-(M ^ 2 + 16 / L ^ 2) * (t - a))`. -/
noncomputable def decayingBump (L M η a x t : ℝ) : ℝ :=
  η*Real.exp (-(M^2+16/L^2)*(t-a))*positiveBump L x

theorem decayingBump_contDiff (L M η a : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => decayingBump L M η a z.1 z.2) := by
  unfold decayingBump positiveBump
  fun_prop

theorem decayingBump_hasDeriv_t (L M η a x t : ℝ) :
    HasDerivAt (decayingBump L M η a x)
      (-(M^2+16/L^2)*decayingBump L M η a x t) t := by
  convert! (((((hasDerivAt_id t).sub_const a).const_mul (-(M^2+16/L^2))).exp).const_mul η).mul_const
    (positiveBump L x) using 1
  dsimp [decayingBump]
  ring

theorem decayingBump_subsolution {L M η a D x t : ℝ}
    (hL : 0 < L) (hη : 0 ≤ η) (hD : |D| ≤ M) :
    deriv (decayingBump L M η a x) t ≤
      deriv (deriv (fun y => decayingBump L M η a y t)) x +
        D*deriv (fun y => decayingBump L M η a y t) x := by
  rw [(decayingBump_hasDeriv_t L M η a x t).deriv]
  simp only [decayingBump, deriv_const_mul_field', deriv_const_mul_field]
  have hh := mul_nonneg (mul_nonneg hη (Real.exp_pos (-(M^2+16/L^2)*(t-a))).le)
    (positiveBump_operator (x := x) hL hD)
  nlinarith

end MathFin.BlackScholes.AmericanPut.Boundary
