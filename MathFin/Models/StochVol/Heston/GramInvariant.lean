/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.LaplaceRiccati
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Gram Invariant

## Main results

* `hasDerivAt_gramBarrier`
* `gramBarrier_nonneg_of_linear_system`
* `denominator_ne_zero_of_linear_system`

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

/-- A scalar differential inequality preserves nonnegativity on nonnegative time. -/
theorem nonneg_of_linear_derivative_lower (f f' : Real → Real) (b : Real)
    (hd : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t)
    (h0 : 0 ≤ f 0) (hb : ∀ t, 0 ≤ t → b * f t ≤ f' t) :
    ∀ t, 0 ≤ t → 0 ≤ f t := by
  intro T hT
  have hc : ContinuousOn (fun t => -f t) (Icc 0 T) := by
    intro t ht
    exact (hd t ht.1).neg.continuousAt.continuousWithinAt
  have he := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun t => -f t) (f' := fun t => -f' t) (δ := 0) (K := b) (ε := 0) hc
    (fun t ht r hr => ((hd t ht.1).neg.hasDerivWithinAt (s := Ici t)).liminf_right_slope_le hr)
    (by linarith : -f 0 ≤ 0)
    (fun t ht => by nlinarith [hb t ht.1]) T ⟨hT, le_rfl⟩
  simpa only [gronwallBound_ε0_δ0, neg_nonpos] using he

theorem hasDerivAt_gramBarrier (p : Parameters) (u : Complex)
    (P Q : Real → Complex) (t : Real)
    (hP : HasDerivAt P (laplaceB p u * P t + laplaceConstant u * Q t) t)
    (hQ : HasDerivAt Q (-(laplaceA p : Complex) * P t) t) :
    HasDerivAt (fun s => gramBarrier (P s) (Q s)) (gramSlope p u (P t) (Q t)) t := by
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hP.mul hQ.star)).neg

theorem gramBarrier_nonneg_of_linear_system (p : Parameters) (u : Complex)
    (P Q : Real → Complex)
    (hP : ∀ t, HasDerivAt P (laplaceB p u * P t + laplaceConstant u * Q t) t)
    (hQ : ∀ t, HasDerivAt Q (-(laplaceA p : Complex) * P t) t)
    (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u)
    (h0 : 0 ≤ gramBarrier (P 0) (Q 0)) :
    ∀ t, 0 ≤ t → 0 ≤ gramBarrier (P t) (Q t) := by
  apply nonneg_of_linear_derivative_lower
    (fun t => gramBarrier (P t) (Q t)) (fun t => gramSlope p u (P t) (Q t))
    (laplaceB p u).re
  · intro t _
    exact hasDerivAt_gramBarrier p u P Q t (hP t) (hQ t)
  · exact h0
  · intro t _
    exact gramSlope_lower_bound p u (P t) (Q t) hρ hu

/-- The denominator cannot vanish: at a positive-time zero the nonnegative barrier
would have a local minimum, but its derivative forces P=0 as well. -/
theorem denominator_ne_zero_of_linear_system (p : Parameters) (u : Complex)
    (P Q : Real → Complex)
    (hP : ∀ t, HasDerivAt P (laplaceB p u * P t + laplaceConstant u * Q t) t)
    (hQ : ∀ t, HasDerivAt Q (-(laplaceA p : Complex) * P t) t)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u)
    (h0 : 0 ≤ gramBarrier (P 0) (Q 0)) (hQ0 : Q 0 ≠ 0)
    (hpair : ∀ t, (P t, Q t) ≠ (0, 0)) :
    ∀ t, 0 ≤ t → Q t ≠ 0 := by
  have hR := gramBarrier_nonneg_of_linear_system p u P Q hP hQ hρ hu h0
  intro t ht hzero
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · exact hQ0 (ht0 ▸ hzero)
  · have hmin : IsLocalMin (fun s => gramBarrier (P s) (Q s)) t := by
      change ∀ᶠ s in 𝓝 t, gramBarrier (P t) (Q t) ≤ gramBarrier (P s) (Q s)
      filter_upwards [Ioi_mem_nhds htpos] with s hs
      simpa only [gramBarrier, hzero, star_zero, mul_zero, Complex.zero_re, neg_zero] using
        hR s hs.le
    have hd0 := hmin.hasDerivAt_eq_zero (hasDerivAt_gramBarrier p u P Q t (hP t) (hQ t))
    rw [hzero, gramSlope_at_Q_zero] at hd0
    have ha : 0 < laplaceA p := by unfold laplaceA; positivity
    have hnorm : Complex.normSq (P t) = 0 := (mul_eq_zero.mp hd0).resolve_left ha.ne'
    have hp0 : P t = 0 := Complex.normSq_eq_zero.mp hnorm
    exact hpair t (by simp only [hp0, hzero])

end MathFin.Heston
