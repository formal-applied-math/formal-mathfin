/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.DividendProblem

/-! # A quadratic localization supersolution

Subtracting a positive multiple forces negative comparison data at distant
spatial endpoints. It tends to zero pointwise as the multiple tends to zero.

## Main definitions

* `localizationBarrier`: the barrier `exp ((2 + |k − h − 1|) t) · (1 + x²)`, a quadratic in space
  with an exponential time factor.

## Main results

* `localizationBarrier_pos`, `localizationBarrier_ge_quad`: `localizationBarrier k h x t` is
  positive, and at least `1 + x²` for `t ≥ 0`.
* `localizationBarrier_contDiff`: it is `C²` in `(x, t)`.
* `localizationBarrier_hasDeriv_x`, `localizationBarrier_deriv2_x`,
  `localizationBarrier_hasDeriv_t`: its explicit space and time derivatives.
* `localizationBarrier_supersolution`: for `0 ≤ k`, the dividend spatial operator applied to the
  barrier is at most its time derivative.

## Tags

quadratic supersolution, localization, comparison data, barrier function, MSC 35R35, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open scoped ContDiff

/-- The spatial quadratic `1 + x ^ 2` carrying the exponential time factor
`Real.exp ((2 + |k - h - 1|) * t)`. -/
noncomputable def localizationBarrier (k h x t : ℝ) : ℝ :=
  Real.exp ((2+|k-h-1|)*t)*(1+x^2)

theorem localizationBarrier_pos (k h x t : ℝ) : 0 < localizationBarrier k h x t := by
  unfold localizationBarrier
  positivity

theorem localizationBarrier_contDiff (k h : ℝ) :
    ContDiff ℝ 2 (fun z : ℝ × ℝ => localizationBarrier k h z.1 z.2) := by
  unfold localizationBarrier
  fun_prop

theorem localizationBarrier_hasDeriv_x (k h x t : ℝ) :
    HasDerivAt (fun y => localizationBarrier k h y t)
      (Real.exp ((2+|k-h-1|)*t)*(2*x)) x := by
  convert! (((hasDerivAt_id x).pow 2).const_add 1).const_mul
    (Real.exp ((2+|k-h-1|)*t)) using 1
  simp only [id_eq]
  ring

theorem localizationBarrier_deriv2_x (k h x t : ℝ) :
    deriv (deriv (fun y => localizationBarrier k h y t)) x =
      2*Real.exp ((2+|k-h-1|)*t) := by
  rw [show deriv (fun y => localizationBarrier k h y t) =
    fun y => Real.exp ((2+|k-h-1|)*t)*(2*y) from
      funext (fun y => (localizationBarrier_hasDeriv_x k h y t).deriv)]
  convert! (((hasDerivAt_id x).const_mul 2).const_mul (Real.exp ((2+|k-h-1|)*t))).deriv using 1
  ring

theorem localizationBarrier_hasDeriv_t (k h x t : ℝ) :
    HasDerivAt (localizationBarrier k h x)
      (Real.exp ((2+|k-h-1|)*t)*(2+|k-h-1|)*(1+x^2)) t := by
  convert! (((hasDerivAt_id t).const_mul (2+|k-h-1|)).exp).mul_const (1+x^2) using 1
  simp only [id_eq]
  ring

theorem localizationBarrier_ge_quad (k h x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    1+x^2 ≤ localizationBarrier k h x t := by
  have he : 1 ≤ Real.exp ((2+|k-h-1|)*t) := Real.one_le_exp_iff.mpr (by positivity)
  unfold localizationBarrier
  nlinarith [sq_nonneg x]

theorem localizationBarrier_supersolution {k h : ℝ} (hk : 0 ≤ k) (x t : ℝ) :
    dividendSpatialOperator k h (fun y => localizationBarrier k h y t) x ≤
      deriv (localizationBarrier k h x) t := by
  have hax : 2*|x| ≤ 1+x^2 := by nlinarith [sq_abs x,sq_nonneg (|x|-1)]
  have hprod := mul_le_mul_of_nonneg_left hax (abs_nonneg (k-h-1))
  have hmag : (k-h-1)*x ≤ |k-h-1| * |x| := by simpa [abs_mul] using le_abs_self ((k-h-1)*x)
  have hpoly : 0 ≤ (2+|k-h-1|+k)*(1+x^2)-2-2*(k-h-1)*x := by
    nlinarith [mul_nonneg hk (sq_nonneg x),sq_nonneg x]
  unfold dividendSpatialOperator
  rw [(localizationBarrier_hasDeriv_x k h x t).deriv,localizationBarrier_deriv2_x,
    (localizationBarrier_hasDeriv_t k h x t).deriv]
  unfold localizationBarrier
  nlinarith [mul_nonneg (Real.exp_pos ((2+|k-h-1|)*t)).le hpoly]

end MathFin.BlackScholes.AmericanPut.Boundary
