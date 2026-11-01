/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianHeatFlow
public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianTransition
public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianVerification

/-! # Waiting in physical time and price coordinates: the supermartingale step

The step is generic: it needs `PutEnvelope p` and `PutWaiting`, whoever supplies them.

## Result

Public entry points include `PutWaiting.physical_transition`,
`classicalCandidate_condExp_le_before_maturity`,
`brownianClassicalCandidate_supermartingale`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

/-- Waiting in physical time and price coordinates: from time `i` to `j ≤ T` at volatility `σ`,
a price that waits at the normalized rates dominates its discounted heat flow. -/
theorem PutWaiting.physical_transition {K r q σ : ℝ} {p : ℝ → ℝ → ℝ}
    (hw : PutWaiting (normalizedRate r σ) (normalizedRate q σ) p) (hK : 0 ≤ K) (hσ : 0 < σ)
    {i j T : ℝ≥0} (hij : i ≤ j) (hjT : j ≤ T) (x : ℝ) :
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
  have he := mul_le_mul_of_nonneg_left (hw.evolution_le ha hat x)
    (mul_nonneg (Real.exp_pos (-r*(i : ℝ))).le hK)
  have hexp : Real.exp (-r*(i : ℝ))*Real.exp (-normalizedRate r σ*(t-a)) =
      Real.exp (-r*(j : ℝ)) := by
    rw [← Real.exp_add]
    simp only [neg_mul]
    rw [hrate]
    congr 1
    ring
  dsimp only [linearPriceEvolution] at he
  rw [htime,hdrift] at he
  convert! he using 1
  rw [← hexp]
  ring

/-- An envelope that waits makes the discounted candidate a supermartingale step: before
maturity, its conditional expectation in the Brownian filtration is at most its present value. -/
theorem classicalCandidate_condExp_le_before_maturity {K r q σ S : ℝ} {p : ℝ → ℝ → ℝ}
    (hE : PutEnvelope p)
    (hw : PutWaiting (normalizedRate r σ) (normalizedRate q σ) p) (hK : 0 ≤ K) (hσ : 0 < σ)
    {i j T : ℝ≥0} (hij : i ≤ j) (hjT : j ≤ T) :
    gaussianLimit[classicalCandidate brownian K r q σ S p T j | brownianFiltration i]
        ≤ᵐ[gaussianLimit]
      classicalCandidate brownian K r q σ S p T i := by
  let a := σ^2/2*((T : ℝ)-(j : ℝ))
  let f : ℝ → ℝ := fun y => Real.exp (-r*(j : ℝ))*K*p y a
  let X : (ℝ≥0 → ℝ) → ℝ := fun ω => classicalLogSpot brownian K r q σ S i ω+
    (r-q-σ^2/2)*((j : ℝ)-(i : ℝ))
  have ha : 0 ≤ a := mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hjT))
  have hpcont : Continuous (fun y => p y a) := hE.price_continuous.comp_continuous
    (continuous_id.prodMk continuous_const) (fun _ => ha)
  have hf : Continuous f := continuous_const.mul hpcont
  have hb (y : ℝ) : ‖f y‖ ≤ ‖Real.exp (-r*(j : ℝ))*K‖ := by
    have hpy : ‖p y a‖ ≤ 1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (hE.nonneg y ha)]
      exact hE.bounded y a ha
    simpa only [f,norm_mul,mul_one] using
      mul_le_mul_of_nonneg_left hpy (norm_nonneg (Real.exp (-r*(j : ℝ))*K))
  have hX : Measurable[brownianFiltration i] X :=
    (measurable_const.add (measurable_const.mul (brownian_adapted i))).add measurable_const
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
  have hcomp := hw.physical_transition hK hσ hij hjT
    (classicalLogSpot brownian K r q σ S i ω)
  simpa only [brownianHeatFlow,f,X,a,integral_const_mul,classicalCandidate,
    min_eq_left (hij.trans hjT),mul_assoc] using hcomp

/-- An envelope that waits makes the discounted candidate a supermartingale in the Brownian
filtration, frozen at maturity. -/
theorem brownianClassicalCandidate_supermartingale {K r q σ S : ℝ} {p : ℝ → ℝ → ℝ}
    (hE : PutEnvelope p)
    (hw : PutWaiting (normalizedRate r σ) (normalizedRate q σ) p)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hσ : 0 < σ) (T : ℝ≥0) :
    Supermartingale (classicalCandidate brownian K r q σ S p T) brownianFiltration
        gaussianLimit := by
  let U := classicalCandidate brownian K r q σ S p T
  have hadapt : StronglyAdapted brownianFiltration U :=
    fun t => (classicalCandidate_adapted hE brownian_adapted T t).stronglyMeasurable
  have hint (t : ℝ≥0) : Integrable (U t) gaussianLimit := by
    apply (integrable_const K).mono'
      ((hadapt t).mono (brownianFiltration.le t)).aestronglyMeasurable
    exact Eventually.of_forall (classicalCandidate_norm_le hE brownian hK hr T t)
  refine ⟨hadapt,?_,hint⟩
  intro i j hij
  change gaussianLimit[U j | brownianFiltration i] ≤ᵐ[gaussianLimit] U i
  have hfreeze (j : ℝ≥0) (hj : T ≤ j) : U j = U T := by
    funext ω
    simp only [U,classicalCandidate,min_eq_right hj,min_self]
  by_cases hjT : j ≤ T
  · exact classicalCandidate_condExp_le_before_maturity hE hw hK hσ hij hjT
  · rw [hfreeze j (not_le.mp hjT).le]
    by_cases hiT : i ≤ T
    · exact classicalCandidate_condExp_le_before_maturity hE hw hK hσ hiT le_rfl
    · rw [← hfreeze i (not_le.mp hiT).le,
        condExp_of_stronglyMeasurable (brownianFiltration.le i) (hadapt i) (hint i)]

end MathFin.BlackScholes.AmericanPut.Stopping
