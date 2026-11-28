/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.RiccatiUniqueness
public import MathFin.Models.StochVol.Heston.IntegratedTransform
public import MathFin.Models.StochVol.Heston

/-!
# Riccati Identification

## Main results

* `globalLaplaceD_eq_hestonBv`
* `globalLaplaceC_eq_hestonA`
* `globalAffineTransform_eq_hestonTransform`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.Heston

/-- Identification of the constructed operator-exponential solution with the library's
real Möbius coefficient, with zero terminal variance weight. -/
theorem globalLaplaceD_eq_hestonBv (p : Parameters) {u t : ℝ} (ht : 0 ≤ t)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : 0 < u) (hu' : u < 1) :
    globalLaplaceD p u 0 t = (MathFin.Heston.hestonBv p.kappa p.xi p.rho u t : ℂ) := by
  apply MathFin.Heston.eq_hestonBv_of_riccati (T := t) hξ.ne' hu hu'
      (globalLaplaceD_zero p u 0) _ t ⟨ht, le_rfl⟩
  intro s hs
  have hd := hasDerivAt_globalLaplaceD p (u : ℂ) 0 hξ hρ
    (show inClosedLaplaceStrip (u : ℂ) from ⟨hu.le, hu'.le⟩) (by simp) s hs.1
  apply hd.congr_deriv
  unfold laplaceRhs laplaceB laplaceA laplaceConstant
  push_cast
  ring

/-- The constant coefficient uses log-spot carry as its rate argument. -/
theorem globalLaplaceC_eq_hestonA (p : Parameters) {u t : ℝ} (ht : 0 ≤ t)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : 0 < u) (hu' : u < 1) :
    globalLaplaceC p u 0 t =
      (MathFin.Heston.hestonA (p.r - p.q) p.kappa p.theta p.xi p.rho u t : ℂ) := by
  apply MathFin.Heston.eq_hestonA_of_deriv (T := t) hξ.ne' hu hu'
      (globalLaplaceC_zero p u 0) _ t ⟨ht, le_rfl⟩
  intro s hs
  have hc := hasDerivAt_globalLaplaceC p (u : ℂ) 0 hξ hρ
    (show inClosedLaplaceStrip (u : ℂ) from ⟨hu.le, hu'.le⟩) (by simp) s hs.1
  apply hc.congr_deriv
  rw [globalLaplaceD_eq_hestonBv p hs.1 hξ hρ hu hu']
  simp only [laplaceCarry, modelA, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]

/-- The affine transforms coincide at valuation time zero and maturity t. -/
theorem globalAffineTransform_eq_hestonTransform (p : Parameters) {u t : ℝ} (ht : 0 ≤ t)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : 0 < u) (hu' : u < 1) (x v : ℝ) :
    globalAffineTransform p u 0 x v t =
      (MathFin.Heston.hestonTransform (p.r - p.q) p.kappa p.theta p.xi p.rho u t 0 x v : ℂ) := by
  simp only [globalAffineTransform, globalLaplaceD_eq_hestonBv p ht hξ hρ hu hu',
    globalLaplaceC_eq_hestonA p ht hξ hρ hu hu', MathFin.Heston.hestonTransform,
    MathFin.Heston.hestonProfile, sub_zero, Complex.ofReal_exp, Complex.ofReal_add,
          Complex.ofReal_mul]

end MathFin.Heston
