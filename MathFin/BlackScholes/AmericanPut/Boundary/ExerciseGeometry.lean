/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.DividendProblem
public import MathFin.BlackScholes.AmericanPut.Boundary.ParabolicMaximum

/-!
# Exercise-boundary calculus from the classical pricing contract

Smooth fit and the exercise formula give an ordinary spatial derivative at
the boundary, although no second derivative across it is asserted. Positivity
then excludes a boundary at the strike at any positive time.

## Result

Public entry points include `price_hasDerivAt_boundary`, `boundary_neg`,
`boundary_forcing_pos`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.DividendPutSolution

open Set Filter
open scoped Topology ContDiff

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

/-- The two one-sided derivatives agree, so the spatial derivative exists
on the whole line at contact. This does not assert joint or second-order
smoothness across the free boundary. -/
theorem price_hasDerivAt_boundary (hp : DividendPutSolution k h p b)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => p x t) (-Real.exp (b t)) (b t) := by
  have he : HasDerivWithinAt (fun x => p x t) (-Real.exp (b t)) (Iic (b t)) (b t) :=
    ((Real.hasDerivAt_exp (b t)).const_sub 1).hasDerivWithinAt.congr_of_mem
      (fun x hx => hp.exercise x t ht hx) (by simp)
  have hu := he.union (hp.smooth_fit t ht)
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hu

/-- A zero exercise boundary would make a nonnegative price attain zero
with derivative minus one, contradicting the first derivative test. -/
theorem boundary_neg (hp : DividendPutSolution k h p b)
    {t : ℝ} (ht : 0 < t) : b t < 0 := by
  apply lt_of_le_of_ne (hp.boundary_nonpos ht)
  intro he
  have hm : IsLocalMin (fun x => p x t) (b t) := by
    apply Filter.Eventually.of_forall
    intro x
    have hz : p (b t) t = 0 := by rw [hp.exercise (b t) t ht le_rfl, he]; simp
    change p (b t) t ≤ p x t
    rw [hz]
    exact hp.nonneg x ht.le
  have hd := (hp.price_hasDerivAt_boundary ht).deriv
  rw [hm.deriv_eq_zero, he, Real.exp_zero] at hd
  norm_num at hd

/-- The exercise-side forcing is strictly positive, even when `h=k`.
This strictness uses the just-proved strict separation from the strike. -/
theorem boundary_forcing_pos (hp : DividendPutSolution k h p b)
    {t : ℝ} (ht : 0 < t) : 0 < k - h * Real.exp (b t) := by
  have he : Real.exp (b t) < 1 := Real.exp_lt_one_iff.mpr (hp.boundary_neg ht)
  have hprod : h * Real.exp (b t) ≤ k * Real.exp (b t) :=
    mul_le_mul_of_nonneg_right hp.dividend_le_rate (Real.exp_pos _).le
  have hstrict : k * Real.exp (b t) < k := by nlinarith [hp.rate_pos]
  linarith

/-- In the open exercise region the price is locally the smooth payoff,
jointly in space and time. Nothing is extended through the free boundary. -/
theorem price_eventuallyEq_exercise (hp : DividendPutSolution k h p b)
    {x t : ℝ} (ht : 0 < t) (hx : x < b t) :
    (fun z : ℝ × ℝ => p z.1 z.2) =ᶠ[𝓝 (x,t)] (fun z => 1 - Real.exp z.1) := by
  have hb : ContinuousAt b t := hp.boundary_continuous.continuousAt (Ici_mem_nhds ht)
  have hbt : ContinuousAt (fun z : ℝ × ℝ => b z.2) (x,t) := hb.comp continuousAt_snd
  have hinside : ∀ᶠ z : ℝ × ℝ in 𝓝 (x,t), z.1 < b z.2 :=
    continuousAt_fst.eventually_lt hbt hx
  have htime : ∀ᶠ z : ℝ × ℝ in 𝓝 (x,t), 0 < z.2 :=
    continuousAt_const.eventually_lt continuousAt_snd ht
  filter_upwards [hinside,htime] with z hz hzt
  exact hp.exercise z.1 z.2 hzt hz.le

theorem price_contDiffAt_exercise (hp : DividendPutSolution k h p b)
    {x t : ℝ} (ht : 0 < t) (hx : x < b t) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => p z.1 z.2) (x,t) := by
  have hpayoff : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => 1 - Real.exp z.1) (x,t) := by fun_prop
  exact hpayoff.congr_of_eventuallyEq (hp.price_eventuallyEq_exercise ht hx)

/-- Away from the boundary the price is a classical supersolution on BOTH
sides of the obstacle. The exercise-side residual is `k-h*exp x`. -/
theorem price_supersolution_off_boundary (hp : DividendPutSolution k h p b)
    {x t : ℝ} (ht : 0 < t) (hx : x ≠ b t) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => p z.1 z.2) (x,t) ∧
      dividendSpatialOperator k h (fun y => p y t) x ≤ deriv (p x) t := by
  rcases hx.lt_or_gt with he | hc
  · refine ⟨hp.price_contDiffAt_exercise ht he,?_⟩
    have hlocal := hp.price_eventuallyEq_exercise ht he
    have hs : (fun y => p y t) =ᶠ[𝓝 x] (fun y => 1 - Real.exp y) :=
      hlocal.comp_tendsto (continuousAt_id.prodMk continuousAt_const)
    have htime : p x =ᶠ[𝓝 t] (fun _ => 1 - Real.exp x) :=
      hlocal.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
    have hderiv : deriv (fun y : ℝ => 1 - Real.exp y) = fun y => -Real.exp y := by
      funext y
      exact ((Real.hasDerivAt_exp y).const_sub 1).deriv
    have hsecond : deriv (deriv (fun y : ℝ => 1 - Real.exp y)) x = -Real.exp x := by
      rw [hderiv]
      exact (Real.hasDerivAt_exp x).neg.deriv
    unfold dividendSpatialOperator
    rw [hs.deriv_eq, hs.deriv.deriv_eq, htime.deriv_eq, deriv_const, hsecond,
      hderiv]
    change -Real.exp x + (k - h - 1) * -Real.exp x - k * p x t ≤ 0
    rw [hp.exercise x t ht he.le]
    have hexp : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr (he.le.trans (hp.boundary_nonpos ht))
    have hprod : h * Real.exp x ≤ h := by nlinarith [hp.dividend_nonneg]
    nlinarith [hp.dividend_le_rate]
  · exact ⟨hp.price_contDiffAt ht hc,(hp.equation x t ht hc).ge⟩

end MathFin.BlackScholes.AmericanPut.Boundary.DividendPutSolution
