/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Foundations.IndepFreezing
public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianHeatFlow

/-! # Conditional Brownian transitions in the raw natural filtration 
## Result

Public entry points include `brownianLogState`, `brownian_scaled_increment_heatFlow`, `brownian_condExp_transition`, `brownianLogState_condExp_transition`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

/-- The log state `x+β*t+σ*B_t`: drift `β` and volatility `σ` applied to the constructed
Brownian motion, started at `x`. -/
noncomputable def brownianLogState (β σ x : ℝ) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  x+β*(t : ℝ)+σ*brownian t ω

theorem brownian_scaled_increment_heatFlow {f : ℝ → ℝ} (hf : Continuous f)
    {i j : ℝ≥0} (hij : i ≤ j) (σ x : ℝ) :
    (∫ ω, f (x+σ*(brownian j ω-brownian i ω)) ∂gaussianLimit) =
      brownianHeatFlow f (σ^2*((j : ℝ)-(i : ℝ))).toNNReal x := by
  have hΔ : 0 ≤ (j : ℝ)-(i : ℝ) := sub_nonneg.mpr (by exact_mod_cast hij)
  have hv : (NNReal.mk (σ^2) (sq_nonneg σ))*nndist j i =
      (σ^2*((j : ℝ)-(i : ℝ))).toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_mul,coe_nndist,NNReal.dist_eq,
      abs_of_nonneg hΔ,Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) hΔ)]
    rfl
  have hl := gaussianReal_const_mul (hasLaw_brownian_sub (s := j) (t := i)) σ
  simp only [mul_zero,hv] at hl
  have hm : Continuous (fun y => f (x+y)) := hf.comp (continuous_const.add continuous_id)
  have he := hl.integral_comp hm.aestronglyMeasurable
  have he' := (hasLaw_brownian_eval (t := (σ^2*((j : ℝ)-(i : ℝ))).toNNReal)).integral_comp
    hm.aestronglyMeasurable
  exact he.trans he'.symm

theorem brownian_condExp_transition {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ C) {i j : ℝ≥0} (hij : i ≤ j)
    {X : (ℝ≥0 → ℝ) → ℝ} (hX : Measurable[brownianFiltration i] X) (σ : ℝ) :
    gaussianLimit[fun ω => f (X ω+σ*(brownian j ω-brownian i ω)) | brownianFiltration i] =ᵐ[gaussianLimit]
      fun ω => brownianHeatFlow f (σ^2*((j : ℝ)-(i : ℝ))).toNNReal (X ω) := by
  have hY : Measurable (fun ω => brownian j ω-brownian i ω) :=
    (measurable_brownian j).sub (measurable_brownian i)
  have hH : Continuous (fun z : ℝ × ℝ => f (z.1+σ*z.2)) := by fun_prop
  have hint : Integrable (fun ω => f (X ω+σ*(brownian j ω-brownian i ω))) gaussianLimit :=
    (integrable_const C).mono' (hH.measurable.comp
      ((hX.mono (brownianFiltration.le i) le_rfl).prodMk hY)).aestronglyMeasurable
      (Eventually.of_forall fun ω => hb _)
  have he := condExp_comp_prodMk_of_indep (brownianFiltration.le i) hX hY.aemeasurable
    (brownian_filtered.indep i j hij) hH.stronglyMeasurable hint
  filter_upwards [he] with ω hω
  rw [hω]
  have hmap := integral_map (μ := gaussianLimit) hY.aemeasurable
    (hf.comp (show Continuous (fun y : ℝ => X ω+σ*y) by fun_prop)).aestronglyMeasurable
  exact hmap.trans (brownian_scaled_increment_heatFlow hf hij σ (X ω))

theorem brownianLogState_condExp_transition {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ C) {i j : ℝ≥0} (hij : i ≤ j) (β σ x : ℝ) :
    gaussianLimit[fun ω => f (brownianLogState β σ x j ω) | brownianFiltration i] =ᵐ[gaussianLimit]
      fun ω => brownianHeatFlow f (σ^2*((j : ℝ)-(i : ℝ))).toNNReal
        (brownianLogState β σ x i ω+β*((j : ℝ)-(i : ℝ))) := by
  let X : (ℝ≥0 → ℝ) → ℝ := fun ω => brownianLogState β σ x i ω+β*((j : ℝ)-(i : ℝ))
  have hX : Measurable[brownianFiltration i] X :=
    (measurable_const.add (measurable_const.mul (brownian_adapted i))).add measurable_const
  have he := brownian_condExp_transition hf hb hij hX σ
  have heq : (fun ω => f (X ω+σ*(brownian j ω-brownian i ω))) =
      fun ω => f (brownianLogState β σ x j ω) := by
    funext ω
    congr 1
    dsimp [X,brownianLogState]
    ring
  rw [heq] at he
  exact he

end MathFin.BlackScholes.AmericanPut.Stopping
