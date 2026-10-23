/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ClassicalHeatComparison
public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianTransition
public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianVerification

/-! # Classical Gaussian comparison in physical time and price coordinates 
## Result

Public entry points include `classicalPrice_physical_transition`,
`classicalCandidate_condExp_le_before_maturity`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

theorem classicalPrice_physical_transition {K r q σ : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 ≤ K) (hσ : 0 < σ) {i j T : ℝ≥0} (hij : i ≤ j) (hjT : j ≤ T) (x : ℝ) :
    Real.exp (-r*(j : ℝ))*K*
        brownianHeatFlow (fun y => p y (σ^2/2*((T : ℝ)-(j : ℝ))))
          (σ^2*((j : ℝ)-(i : ℝ))).toNNReal (x+(r-q-σ^2/2)*((j : ℝ)-(i : ℝ))) ≤
      Real.exp (-r*(i : ℝ))*K*p x (σ^2/2*((T : ℝ)-(i : ℝ))) := by
  let a := σ^2/2*((T : ℝ)-(j : ℝ))
  let t := σ^2/2*((T : ℝ)-(i : ℝ))
  have ha : 0 ≤ a := mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hjT))
  have hat : a ≤ t := by
    dsimp [a,t]
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_left (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij) (T : ℝ)) (by positivity)
  have htime : 2*(t-a) = σ^2*((j : ℝ)-(i : ℝ)) := by dsimp [a,t]; ring
  have hrate : normalizedRate r σ*(t-a) = r*((j : ℝ)-(i : ℝ)) := by
    dsimp [normalizedRate,a,t]
    field_simp [ne_of_gt hσ]
    ring
  have hdrift : (normalizedRate r σ-normalizedRate q σ-1)*(t-a) =
      (r-q-σ^2/2)*((j : ℝ)-(i : ℝ)) := by
    dsimp [normalizedRate,a,t]
    field_simp [ne_of_gt hσ]
    ring
  have he := mul_le_mul_of_nonneg_left (classicalPrice_gaussian_comparison hp ha hat x)
    (mul_nonneg (Real.exp_pos (-r*(i : ℝ))).le hK)
  have hw : Real.exp (-r*(i : ℝ))*Real.exp (-normalizedRate r σ*(t-a)) =
      Real.exp (-r*(j : ℝ)) := by
    rw [← Real.exp_add]
    simp only [neg_mul]
    rw [hrate]
    congr 1
    ring
  dsimp only [linearPriceEvolution] at he
  rw [htime,hdrift] at he
  convert! he using 1
  rw [← hw]
  ring

theorem classicalCandidate_condExp_le_before_maturity {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 ≤ K) (hσ : 0 < σ) {i j T : ℝ≥0} (hij : i ≤ j) (hjT : j ≤ T) :
    gaussianLimit[classicalCandidate brownian K r q σ S p T j | brownianFiltration i]
        ≤ᵐ[gaussianLimit]
      classicalCandidate brownian K r q σ S p T i := by
  let a := σ^2/2*((T : ℝ)-(j : ℝ))
  let f : ℝ → ℝ := fun y => Real.exp (-r*(j : ℝ))*K*p y a
  let X : (ℝ≥0 → ℝ) → ℝ := fun ω => classicalLogSpot brownian K r q σ S i ω+
    (r-q-σ^2/2)*((j : ℝ)-(i : ℝ))
  have ha : 0 ≤ a := mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hjT))
  have hpcont : Continuous (fun y => p y a) := hp.price_continuous.comp_continuous
    (continuous_id.prodMk continuous_const) (fun _ => ha)
  have hf : Continuous f := continuous_const.mul hpcont
  have hb (y : ℝ) : ‖f y‖ ≤ ‖Real.exp (-r*(j : ℝ))*K‖ := by
    have hpy : ‖p y a‖ ≤ 1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (hp.price_nonneg y ha)]
      exact hp.bounded y a ha
    simpa only [f,norm_mul,mul_one] using
      mul_le_mul_of_nonneg_left hpy (norm_nonneg (Real.exp (-r*(j : ℝ))*K))
  have hX : Measurable[brownianFiltration i] X := by
    exact ((measurable_const.add (measurable_const.mul (brownian_adapted i))).add measurable_const)
  have he := brownian_condExp_transition hf hb hij hX σ
  have heq : (fun ω => f (X ω+σ*(brownian j ω-brownian i ω))) =
      classicalCandidate brownian K r q σ S p T j := by
    funext ω
    dsimp only [f,X,a,classicalCandidate]
    rw [min_eq_left hjT]
    rw [mul_assoc]
    congr 3
    dsimp [classicalLogSpot]
    ring
  rw [heq] at he
  filter_upwards [he] with ω hω
  rw [hω]
  have hcomp := classicalPrice_physical_transition hp hK hσ hij hjT
    (classicalLogSpot brownian K r q σ S i ω)
  simpa only [brownianHeatFlow,f,X,a,integral_const_mul,classicalCandidate,
    min_eq_left (hij.trans hjT),mul_assoc] using hcomp

end MathFin.BlackScholes.AmericanPut.Stopping
