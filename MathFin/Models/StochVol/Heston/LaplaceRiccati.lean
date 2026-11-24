/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.Definitions

/-!
# Laplace Riccati

Laplace parameter convention: exp(u X + w V), with complex u and w.
The older characteristic-frequency convention is recovered by u = I * frequency.

## Main definitions

* `inClosedLaplaceStrip`
* `gramBarrier`
* `gramSlope`

## Main results

* `gramSlope_at_Q_zero`
* `laplace_energy_identity`
* `laplace_energy_bound`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston

/-- Quadratic coefficient in the maturity-time Riccati equation. -/
def laplaceA (p : Parameters) : Real := p.xi ^ 2 / 2
/-- Linear coefficient in the maturity-time Riccati equation. -/
def laplaceB (p : Parameters) (u : Complex) : Complex :=
  (p.rho : Complex) * (p.xi : Complex) * u - (p.kappa : Complex)
/-- Constant forcing term for log-spot exponent u. -/
def laplaceConstant (u : Complex) : Complex := (u ^ 2 - u) / 2
/-- Maturity-time Riccati vector field evaluated at the current variance loading. -/
def laplaceRhs (p : Parameters) (u z : Complex) : Complex :=
  (laplaceA p : Complex) * z ^ 2 + laplaceB p u * z + laplaceConstant u

/-- The real part of the log-spot exponent lies between zero and one. -/
def inClosedLaplaceStrip (u : Complex) : Prop := 0 ≤ u.re ∧ u.re ≤ 1

theorem rho_square_le_one (p : Parameters) (hρ : |p.rho| ≤ 1) : p.rho ^ 2 ≤ 1 := by
  have hh := abs_le.mp hρ
  nlinarith [sq_nonneg (p.rho - 1), sq_nonneg (p.rho + 1)]

theorem laplace_boundary_re (p : Parameters) (u : Complex) (y : Real) :
    (laplaceRhs p u (Complex.I * (y : Complex))).re =
      -((p.xi * y + p.rho * u.im) ^ 2 + (1 - p.rho ^ 2) * u.im ^ 2 +
        u.re * (1 - u.re)) / 2 := by
  simp [laplaceRhs, laplaceA, laplaceB, laplaceConstant, pow_two,
    Complex.mul_re, Complex.mul_im]
  ring

theorem laplace_boundary_re_nonpos (p : Parameters) (u : Complex) (y : Real)
    (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) :
    (laplaceRhs p u (Complex.I * (y : Complex))).re ≤ 0 := by
  rw [laplace_boundary_re]
  have h1 := mul_nonneg (sub_nonneg.mpr (rho_square_le_one p hρ)) (sq_nonneg u.im)
  have h2 := mul_nonneg hu.1 (sub_nonneg.mpr hu.2)
  nlinarith [sq_nonneg (p.xi * y + p.rho * u.im)]

theorem laplaceRhs_characteristic (p : Parameters) (u : Real) (z : Complex) :
    laplaceRhs p (Complex.I * (u : Complex)) z =
      rhsD (modelB p u) (modelS p) (modelH u) z := by
  unfold laplaceRhs laplaceA laplaceB laplaceConstant rhsD modelB modelS modelH
  push_cast
  linear_combination (u : Complex) ^ 2 / 2 * Complex.I_sq

/-- Negative real part of the numerator times the conjugated denominator. -/
def gramBarrier (P Q : Complex) : Real := -(P * star Q).re

/-- Derivative of the Gram barrier along the Heston linear system. -/
def gramSlope (p : Parameters) (u P Q : Complex) : Real :=
  -((laplaceB p u * P + laplaceConstant u * Q) * star Q +
    P * star (-(laplaceA p : Complex) * P)).re

/-- A positive-semidefinite identity for the linearized system, valid before taking P/Q. -/
theorem gramSlope_identity (p : Parameters) (u P Q : Complex) :
    gramSlope p u P Q = (laplaceB p u).re * gramBarrier P Q +
      Complex.normSq ((p.xi : Complex) * P +
        Complex.I * (p.rho : Complex) * (u.im : Complex) * Q) / 2 +
      ((1 - p.rho ^ 2) * u.im ^ 2 + u.re * (1 - u.re)) / 2 * Complex.normSq Q := by
  simp [gramSlope, gramBarrier, laplaceA, laplaceB, laplaceConstant,
    Complex.mul_re, Complex.mul_im, Complex.normSq_apply, pow_two]
  ring

theorem gramSlope_lower_bound (p : Parameters) (u P Q : Complex)
    (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) :
    (laplaceB p u).re * gramBarrier P Q ≤ gramSlope p u P Q := by
  rw [gramSlope_identity]
  have h1 := mul_nonneg (sub_nonneg.mpr (rho_square_le_one p hρ)) (sq_nonneg u.im)
  have h2 := mul_nonneg hu.1 (sub_nonneg.mpr hu.2)
  have h3 := mul_nonneg (add_nonneg h1 h2) (Complex.normSq_nonneg Q)
  have h4 := Complex.normSq_nonneg ((p.xi : Complex) * P +
    Complex.I * (p.rho : Complex) * (u.im : Complex) * Q)
  nlinarith

theorem gramSlope_at_Q_zero (p : Parameters) (u P : Complex) :
    gramSlope p u P 0 = laplaceA p * Complex.normSq P := by
  simp [gramSlope, laplaceA, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply, pow_two]
  ring

theorem laplace_energy_identity (p : Parameters) (u z : Complex) :
    2 * (star z * laplaceRhs p u z).re =
      p.xi ^ 2 * z.re * Complex.normSq z +
      2 * (laplaceB p u).re * Complex.normSq z +
      2 * (star z * laplaceConstant u).re := by
  simp [laplaceRhs, laplaceA, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply, pow_two]
  ring

theorem laplace_energy_bound (p : Parameters) (u z : Complex) (hz : z.re ≤ 0) :
    2 * (star z * laplaceRhs p u z).re ≤
      (2 * |(laplaceB p u).re| + 1) * Complex.normSq z +
        Complex.normSq (laplaceConstant u) := by
  rw [laplace_energy_identity]
  have hneg := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (sq_nonneg p.xi) (Complex.normSq_nonneg z)) hz
  have hb := mul_le_mul_of_nonneg_right (le_abs_self (laplaceB p u).re)
    (Complex.normSq_nonneg z)
  have hc : 2 * (star z * laplaceConstant u).re ≤
      Complex.normSq z + Complex.normSq (laplaceConstant u) := by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    nlinarith [sq_nonneg (z.re - (laplaceConstant u).re),
      sq_nonneg (z.im - (laplaceConstant u).im)]
  nlinarith

end MathFin.Heston
