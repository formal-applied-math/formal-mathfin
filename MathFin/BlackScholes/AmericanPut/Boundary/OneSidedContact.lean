/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ExerciseGeometry

/-!
# Spatial test functions at exercise contact

A stationary maximum on the exercise side suffices for a second-derivative
bound on a smooth test function. The price itself need not be twice
differentiable across the free boundary.

## Result

Public entry points include `second_deriv_nonpos_at_left_stationary_max`,
`spatial_test_at_boundary`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology

theorem second_deriv_nonpos_at_left_stationary_max {F : ℝ → ℝ} {x : ℝ}
    (hF : ContinuousAt F x) (hstationary : deriv F x = 0)
    (hmax : ∀ᶠ y in 𝓝[<] x, F y ≤ F x) : deriv (deriv F) x ≤ 0 := by
  by_contra hn
  have hpos : 0 < deriv (deriv F) x := lt_of_not_ge hn
  have hneg : ∀ᶠ y in 𝓝[<] x, deriv F y < 0 :=
    deriv_neg_left_of_sign_deriv (nhdsWithin_le_nhds
      (eventually_nhdsWithin_sign_eq_of_deriv_pos hpos hstationary))
  obtain ⟨l,hl,hall⟩ := (nhdsLT_basis x).eventually_iff.mp (hneg.and hmax)
  let m := (l+x)/2
  have hlm : l < m := by dsimp [m]; linarith
  have hmx : m < x := by dsimp [m]; linarith
  have hanti : StrictAntiOn F (Icc m x) :=
    strictAntiOn_of_deriv_neg (convex_Icc m x)
      (by
        intro y hy
        rcases eq_or_lt_of_le hy.2 with he | he
        · simpa [he] using hF.continuousWithinAt
        · exact (differentiableAt_of_deriv_ne_zero
            (hall ⟨hlm.trans_le hy.1,he⟩).1.ne).continuousAt.continuousWithinAt) (by
        intro y hy
        rw [interior_Icc] at hy
        exact (hall ⟨hlm.trans hy.1,hy.2⟩).1)
  have hlt := hanti ⟨le_rfl,hmx.le⟩ ⟨hmx.le,le_rfl⟩ hmx
  have hle := (hall ⟨hlm,hmx⟩).2
  linarith

namespace DividendPutSolution

/-- At a local maximum of test minus price, the test has the payoff slope
and at most the payoff curvature at exercise contact. After subtracting the
contact value, this is a test touching the price from below. Only the test
function has a second derivative across the boundary. -/
theorem spatial_test_at_boundary {k h : ℝ} {p : ℝ → ℝ → ℝ} {b F : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) {t : ℝ} (ht : 0 < t)
    (hF : ContDiffAt ℝ 2 F (b t))
    (hmax : IsLocalMax (fun x => F x - p x t) (b t)) :
    deriv F (b t) = -Real.exp (b t) ∧
      deriv (deriv F) (b t) ≤ -Real.exp (b t) := by
  have hdF : DifferentiableAt ℝ F (b t) := hF.differentiableAt (by norm_num)
  have hfit := (hp.price_hasDerivAt_boundary ht)
  have hsub := (hdF.hasDerivAt.sub hfit).deriv
  change deriv (fun x => F x - p x t) (b t) = deriv F (b t) - -Real.exp (b t) at hsub
  rw [hmax.deriv_eq_zero] at hsub
  have hslope : deriv F (b t) = -Real.exp (b t) := by linarith
  refine ⟨hslope,?_⟩
  let G : ℝ → ℝ := fun x => F x - (1 - Real.exp x)
  have hpayoff : ContDiffAt ℝ 2 (fun x : ℝ => 1-Real.exp x) (b t) := by fun_prop
  have hG : ContinuousAt G (b t) := hF.continuousAt.sub hpayoff.continuousAt
  have hGzero : deriv G (b t) = 0 := by
    have hd := (hdF.hasDerivAt.sub ((Real.hasDerivAt_exp (b t)).const_sub 1)).deriv
    change deriv G (b t) = deriv F (b t) - -Real.exp (b t) at hd
    simpa [hslope] using hd
  have hGsecond : deriv (deriv G) (b t) = deriv (deriv F) (b t) + Real.exp (b t) := by
    have he : deriv (fun x : ℝ => 1-Real.exp x) = fun x => -Real.exp x :=
      funext (fun x => ((Real.hasDerivAt_exp x).const_sub 1).deriv)
    have hh : deriv (deriv (fun x : ℝ => 1-Real.exp x)) (b t) = -Real.exp (b t) := by
      rw [he]
      exact (Real.hasDerivAt_exp (b t)).neg.deriv
    have hd := iteratedDeriv_fun_sub (n := 2) hF hpayoff
    simpa [iteratedDeriv_succ,hh,G] using hd
  have hGmax : ∀ᶠ x in 𝓝[<] (b t), G x ≤ G (b t) := by
    filter_upwards [nhdsWithin_le_nhds hmax, self_mem_nhdsWithin] with x hx hxb
    change F x - p x t ≤ F (b t) - p (b t) t at hx
    simpa only [G, hp.exercise x t ht (show x < b t from hxb).le,
      hp.exercise (b t) t ht le_rfl] using hx
  have hsecond := second_deriv_nonpos_at_left_stationary_max hG hGzero hGmax
  rw [hGsecond] at hsecond
  linarith

end DividendPutSolution

end MathFin.BlackScholes.AmericanPut.Boundary
