/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import MathFin.Models.StochVol.Heston.GramInvariant
public import MathFin.Models.StochVol.Heston.LinearFlow

/-!
# Global Riccati

A constructed global Riccati solution on the closed Laplace strip.
Existence is supplied by the operator-exponential linear flow, not an input hypothesis.

## Main definitions

* `riccatiNumerator`
* `riccatiDenominator`
* `globalLaplaceD`

## Main results

* `exists_global_laplaceRiccati`
* `hasDerivAt_complex_normSq`
* `globalLaplaceD_energy_bound`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston
open Set Filter
open scoped Topology

/-- First component of the linear flow representing the variance coefficient. -/
def riccatiNumerator (p : Parameters) (u w : Complex) (t : Real) : Complex :=
  linearSystemP (laplaceA p) (laplaceB p u) (laplaceConstant u) w t

/-- Second component of the linear flow representing the variance coefficient. -/
def riccatiDenominator (p : Parameters) (u w : Complex) (t : Real) : Complex :=
  linearSystemQ (laplaceA p) (laplaceB p u) (laplaceConstant u) w t

/-- Ratio of the two linear-flow components at maturity t. -/
def globalLaplaceD (p : Parameters) (u w : Complex) (t : Real) : Complex :=
  riccatiNumerator p u w t / riccatiDenominator p u w t

theorem riccatiNumerator_zero (p : Parameters) (u w : Complex) :
    riccatiNumerator p u w 0 = w := by simp [riccatiNumerator]

theorem riccatiDenominator_zero (p : Parameters) (u w : Complex) :
    riccatiDenominator p u w 0 = 1 := by simp [riccatiDenominator]

theorem hasDerivAt_riccatiNumerator (p : Parameters) (u w : Complex) (t : Real) :
    HasDerivAt (riccatiNumerator p u w)
      (laplaceB p u * riccatiNumerator p u w t +
        laplaceConstant u * riccatiDenominator p u w t) t :=
  hasDerivAt_linearSystemP (laplaceA p) (laplaceB p u) (laplaceConstant u) w t

theorem hasDerivAt_riccatiDenominator (p : Parameters) (u w : Complex) (t : Real) :
    HasDerivAt (riccatiDenominator p u w)
      (-(laplaceA p : Complex) * riccatiNumerator p u w t) t :=
  hasDerivAt_linearSystemQ (laplaceA p) (laplaceB p u) (laplaceConstant u) w t

theorem riccati_linear_pair_ne_zero (p : Parameters) (u w : Complex) (t : Real) :
    (riccatiNumerator p u w t, riccatiDenominator p u w t) ≠ (0, 0) :=
  linearSystemFlow_ne_zero (laplaceA p) (laplaceB p u) (laplaceConstant u) w t

theorem riccati_linear_gram_nonneg (p : Parameters) (u w : Complex)
    (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0)
    (t : Real) (ht : 0 ≤ t) :
    0 ≤ gramBarrier (riccatiNumerator p u w t) (riccatiDenominator p u w t) := by
  apply gramBarrier_nonneg_of_linear_system p u (riccatiNumerator p u w)
    (riccatiDenominator p u w) (hasDerivAt_riccatiNumerator p u w)
    (hasDerivAt_riccatiDenominator p u w) hρ hu ?_ t ht
  simpa only [riccatiNumerator_zero, riccatiDenominator_zero, gramBarrier,
    star_one, mul_one, neg_nonneg] using hw

theorem riccatiDenominator_ne_zero (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0)
    (t : Real) (ht : 0 ≤ t) : riccatiDenominator p u w t ≠ 0 := by
  apply denominator_ne_zero_of_linear_system p u (riccatiNumerator p u w)
    (riccatiDenominator p u w) (hasDerivAt_riccatiNumerator p u w)
    (hasDerivAt_riccatiDenominator p u w) hξ hρ hu ?_ ?_
    (riccati_linear_pair_ne_zero p u w) t ht
  · simpa only [riccatiNumerator_zero, riccatiDenominator_zero, gramBarrier,
      star_one, mul_one, neg_nonneg] using hw
  · simp only [riccatiDenominator_zero, ne_eq, one_ne_zero, not_false_eq_true]

theorem globalLaplaceD_zero (p : Parameters) (u w : Complex) :
    globalLaplaceD p u w 0 = w := by
  simp only [globalLaplaceD, riccatiNumerator_zero, riccatiDenominator_zero, div_one]

theorem hasDerivAt_globalLaplaceD (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0)
    (t : Real) (ht : 0 ≤ t) :
    HasDerivAt (globalLaplaceD p u w) (laplaceRhs p u (globalLaplaceD p u w t)) t := by
  have hQ := riccatiDenominator_ne_zero p u w hξ hρ hu hw t ht
  have hd := (hasDerivAt_riccatiNumerator p u w t).div
    (hasDerivAt_riccatiDenominator p u w t) hQ
  convert! hd using 1
  unfold laplaceRhs globalLaplaceD
  field_simp [hQ]
  ring

theorem globalLaplaceD_re_nonpos (p : Parameters) (u w : Complex)
    (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0)
    (t : Real) (ht : 0 ≤ t) : (globalLaplaceD p u w t).re ≤ 0 := by
  have hg := riccati_linear_gram_nonneg p u w hρ hu hw t ht
  simp only [gramBarrier, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im] at hg
  unfold globalLaplaceD
  rw [Complex.div_re, ← add_div]
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith
  · exact Complex.normSq_nonneg _

/-- Actual all-finite-times existence on the strip, with no global-solution premise. -/
theorem exists_global_laplaceRiccati (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0) :
    ∃ D : Real → Complex, D 0 = w ∧ ∀ t : Real, 0 ≤ t →
      HasDerivAt D (laplaceRhs p u (D t)) t ∧ (D t).re ≤ 0 := by
  refine ⟨globalLaplaceD p u w, globalLaplaceD_zero p u w, ?_⟩
  intro t ht
  exact ⟨hasDerivAt_globalLaplaceD p u w hξ hρ hu hw t ht,
    globalLaplaceD_re_nonpos p u w hρ hu hw t ht⟩

theorem hasDerivAt_complex_normSq {f : Real → Complex} {f' : Complex} {t : Real}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => Complex.normSq (f s)) (2 * (star (f t) * f').re) t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
  convert! (hr.pow 2).add (hi.pow 2) using 1
  · ext s
    simp only [Complex.normSq_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      pow_two, Function.comp_def, Pi.add_apply, Pi.mul_apply]
  · simp only [Complex.reCLM_apply, Complex.imCLM_apply, pow_one, Nat.cast_ofNat,
      Function.comp_apply, Nat.reduceSub, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring

theorem globalLaplaceD_energy_bound (p : Parameters) (u w : Complex)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0)
    (T : Real) (hT : 0 ≤ T) :
    Complex.normSq (globalLaplaceD p u w T) ≤
      gronwallBound (Complex.normSq w) (2 * |(laplaceB p u).re| + 1)
        (Complex.normSq (laplaceConstant u)) T := by
  let D := globalLaplaceD p u w
  have hd (t : Real) (ht : 0 ≤ t) :=
    hasDerivAt_complex_normSq (hasDerivAt_globalLaplaceD p u w hξ hρ hu hw t ht)
  have hc : ContinuousOn (fun t => Complex.normSq (D t)) (Icc 0 T) := by
    intro t ht
    exact (hd t ht.1).continuousAt.continuousWithinAt
  have he := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun t => Complex.normSq (D t))
    (f' := fun t => 2 * (star (D t) * laplaceRhs p u (D t)).re)
    (δ := Complex.normSq w) (K := 2 * |(laplaceB p u).re| + 1)
    (ε := Complex.normSq (laplaceConstant u)) hc
    (fun t ht r hr => ((hd t ht.1).hasDerivWithinAt (s := Ici t)).liminf_right_slope_le hr)
    (by simp only [D, globalLaplaceD_zero, le_refl])
    (fun t ht => laplace_energy_bound p u (D t)
      (globalLaplaceD_re_nonpos p u w hρ hu hw t ht.1)) T ⟨hT, le_rfl⟩
  simpa only [sub_zero] using he

end MathFin.Heston
