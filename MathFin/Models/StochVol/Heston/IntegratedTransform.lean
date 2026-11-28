/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.GlobalRiccati
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Integrated Transform

The integrated C coefficient avoids choosing a complex logarithm branch.

## Main definitions

* `laplaceCarry`
* `globalLaplaceC`
* `globalAffineTransform`

## Main results

* `globalAffineTransform_norm_le_one`
* `globalAffineTransform_rpow_bound`
* `exists_global_integrated_riccati`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston
open MeasureTheory Set
open scoped Topology

/-- Net log-spot carry weighted by the complex exponent. -/
def laplaceCarry (p : Parameters) (u : Complex) : Complex :=
  ((p.r : Complex) - (p.q : Complex)) * u

/-- Integrated constant coefficient of the complex affine transform. -/
def globalLaplaceC (p : Parameters) (u w : Complex) (t : Real) : Complex :=
  laplaceCarry p u * (t : Complex) + modelA p * ∫ s in (0 : Real)..t, globalLaplaceD p u w s

/-- Exponential-affine transform at log-spot x, variance v and maturity t. -/
def globalAffineTransform (p : Parameters) (u w : Complex) (x v t : Real) : Complex :=
  Complex.exp (globalLaplaceC p u w t + u * (x : Complex) +
    globalLaplaceD p u w t * (v : Complex))

theorem globalLaplaceC_zero (p : Parameters) (u w : Complex) :
    globalLaplaceC p u w 0 = 0 := by simp [globalLaplaceC]

theorem globalLaplaceD_intervalIntegrable (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0)
    (t : Real) (ht : 0 ≤ t) : IntervalIntegrable (globalLaplaceD p u w) volume 0 t := by
  apply ContinuousOn.intervalIntegrable_of_Icc ht
  intro s hs
  exact (hasDerivAt_globalLaplaceD p u w hξ hρ hu hw s hs.1).continuousAt.continuousWithinAt

theorem measurable_globalLaplaceD (p : Parameters) (u w : Complex) :
    Measurable (globalLaplaceD p u w) := by
  have hp : Continuous (riccatiNumerator p u w) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_riccatiNumerator p u w t).continuousAt)
  have hq : Continuous (riccatiDenominator p u w) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_riccatiDenominator p u w t).continuousAt)
  exact hp.measurable.div hq.measurable

theorem hasDerivAt_globalLaplaceC (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0)
    (t : Real) (ht : 0 ≤ t) :
    HasDerivAt (globalLaplaceC p u w)
      (laplaceCarry p u + modelA p * globalLaplaceD p u w t) t := by
  have hI := intervalIntegral.integral_hasDerivAt_right
    (globalLaplaceD_intervalIntegrable p u w hξ hρ hu hw t ht)
    (measurable_globalLaplaceD p u w).stronglyMeasurable.stronglyMeasurableAtFilter
    (hasDerivAt_globalLaplaceD p u w hξ hρ hu hw t ht).continuousAt
  have hl : HasDerivAt (fun s : Real => laplaceCarry p u * (s : Complex)) (laplaceCarry p u) t := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (t : Complex)).const_mul (laplaceCarry p u)).comp_ofReal
  exact hl.add (hI.const_mul (modelA p))

theorem globalLaplaceC_re_bound (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0)
    (hκ : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta) (T : Real) (hT : 0 ≤ T) :
    (globalLaplaceC p u w T).re ≤ (p.r - p.q) * u.re * T := by
  have hd (t : Real) (ht : 0 ≤ t) := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_globalLaplaceC p u w hξ hρ hu hw t ht)
  have hc : ContinuousOn (fun t => (globalLaplaceC p u w t).re) (Icc 0 T) := by
    intro t ht
    exact (hd t ht.1).continuousAt.continuousWithinAt
  have hlin (t : Real) :
      HasDerivAt (fun s => (p.r - p.q) * u.re * s) ((p.r - p.q) * u.re) t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul ((p.r - p.q) * u.re)
  apply image_le_of_deriv_right_le_deriv_boundary hc
    (fun t ht => (hd t ht.1).hasDerivWithinAt) ?_
    (by fun_prop) (fun t _ => (hlin t).hasDerivWithinAt) ?_ ⟨hT, le_rfl⟩
  · simp only [globalLaplaceC_zero, Complex.zero_re, mul_zero, le_refl]
  · intro t ht
    have hn := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hκ hθ)
      (globalLaplaceD_re_nonpos p u w hρ hu hw t ht.1)
    simp only [Complex.reCLM_apply, laplaceCarry, modelA, Complex.add_re, Complex.mul_re,
          Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, sub_self, add_zero]
    nlinarith

theorem globalAffineTransform_initial (p : Parameters) (u w : Complex) (x v : Real) :
    globalAffineTransform p u w x v 0 = Complex.exp (u * (x : Complex) + w * (v : Complex)) := by
  simp only [globalAffineTransform, globalLaplaceC_zero, globalLaplaceD_zero, zero_add]

theorem globalAffineTransform_norm_bound (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0)
    (hκ : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta) (x v t : Real) (hv : 0 ≤ v) (ht : 0 ≤ t) :
    ‖globalAffineTransform p u w x v t‖ ≤
      Real.exp ((p.r - p.q) * u.re * t + u.re * x) := by
  unfold globalAffineTransform
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hc := globalLaplaceC_re_bound p u w hξ hρ hu hw hκ hθ t ht
  have hd := mul_nonpos_of_nonpos_of_nonneg
    (globalLaplaceD_re_nonpos p u w hρ hu hw t ht) hv
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  linarith

/-- At the characteristic boundary the candidate is bounded by one, with no exponential-moment
input. -/
theorem globalAffineTransform_norm_le_one (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : u.re = 0) (hw : w.re ≤ 0)
    (hκ : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta) (x v t : Real) (hv : 0 ≤ v) (ht : 0 ≤ t) :
    ‖globalAffineTransform p u w x v t‖ ≤ 1 := by
  have hs : inClosedLaplaceStrip u := by constructor <;> simp [hu]
  simpa only [hu, mul_zero, zero_mul, zero_add, Real.exp_zero] using
    globalAffineTransform_norm_bound p u w hξ hρ hs hw hκ hθ x v t hv ht

/-- The reciprocal-power estimate that feeds the open-strip uniform-integrability argument. -/
theorem globalAffineTransform_rpow_bound (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u)
    (hα : 0 < u.re) (hw : w.re ≤ 0) (hκ : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta)
    (x v t : Real) (hv : 0 ≤ v) (ht : 0 ≤ t) :
    ‖globalAffineTransform p u w x v t‖ ^ (1 / u.re) ≤ Real.exp ((p.r - p.q) * t + x) := by
  have hh := Real.rpow_le_rpow (norm_nonneg (globalAffineTransform p u w x v t))
    (globalAffineTransform_norm_bound p u w hξ hρ hu hw hκ hθ x v t hv ht)
    (one_div_nonneg.mpr hα.le)
  rw [← Real.exp_mul] at hh
  have he : ((p.r - p.q) * u.re * t + u.re * x) * (1 / u.re) = (p.r - p.q) * t + x := by
    field_simp
  rwa [he] at hh

/-- Both coefficients are constructed globally, with their half-plane and carry bounds. -/
theorem exists_global_integrated_riccati (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0)
    (hκ : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta) :
    ∃ C D : Real → Complex, C 0 = 0 ∧ D 0 = w ∧ ∀ t : Real, 0 ≤ t →
      HasDerivAt D (laplaceRhs p u (D t)) t ∧
      HasDerivAt C (laplaceCarry p u + modelA p * D t) t ∧
      (D t).re ≤ 0 ∧ (C t).re ≤ (p.r - p.q) * u.re * t := by
  refine ⟨globalLaplaceC p u w, globalLaplaceD p u w,
    globalLaplaceC_zero p u w, globalLaplaceD_zero p u w, ?_⟩
  intro t ht
  exact ⟨hasDerivAt_globalLaplaceD p u w hξ hρ hu hw t ht,
    hasDerivAt_globalLaplaceC p u w hξ hρ hu hw t ht,
    globalLaplaceD_re_nonpos p u w hρ hu hw t ht,
    globalLaplaceC_re_bound p u w hξ hρ hu hw hκ hθ t ht⟩

end MathFin.Heston
