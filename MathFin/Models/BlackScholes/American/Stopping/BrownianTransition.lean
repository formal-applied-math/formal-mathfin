/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Probability.Analysis.IndepFreezing
public import MathFin.Models.BlackScholes.American.Stopping.BrownianHeatFlow
public import MathFin.Models.BlackScholes.American.Stopping.BrownianModel

/-! # Conditional transitions of a filtered pre-Brownian motion

## Main definitions

* `logState`: the log state `x + β*t + σ*W_t`, with drift `β` and volatility `σ` applied to the
  process `W`, started at `x`.
* `IsGaussianMarkov`: the Gaussian Markov property of a log state `L` with drift `β` and volatility
  `σ` in the filtration `𝓕` under `P`.

## Main results

* `scaled_increment_heatFlow`: for a pre-Brownian motion `W`, continuous `f` and `i ≤ j`, the
  expectation of `f (x + σ (W_j - W_i))` is `brownianHeatFlow f (σ² (j - i)) x`.
* `condExp_transition`: for a filtered pre-Brownian motion `W`, continuous bounded `f`, `i ≤ j` and
  an `𝓕 i`-measurable `X`, the conditional expectation of `f (X + σ (W_j - W_i))` given `𝓕 i` is
  almost surely `brownianHeatFlow f (σ² (j - i)) (X ω)`.
* `logState_isGaussianMarkov`: for a filtered pre-Brownian motion `W`, `logState W β σ x` is
  `IsGaussianMarkov` in `𝓕` under `P`.

## Tags

Gaussian Markov, conditional transition, raw filtration, heat flow, Brownian motion, MSC 60G40,
MSC 60J65
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

/-- The **Gaussian Markov property** of a log state `L` with drift `β` and volatility `σ` in the
filtration `𝓕` under `P`: for bounded continuous `f` and `i ≤ j`, the conditional expectation of
`f (L j)` given `𝓕 i` is the `brownianHeatFlow` of `f` over the variance `σ^2*(j-i)`, started at the
drift-shifted `L i`. -/
def IsGaussianMarkov {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (β σ : ℝ) (L : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ ⦃f : ℝ → ℝ⦄ ⦃C : ℝ⦄, Continuous f → (∀ y, ‖f y‖ ≤ C) → ∀ ⦃i j : ℝ≥0⦄, i ≤ j →
    P[fun ω => f (L j ω) | 𝓕 i] =ᵐ[P]
      fun ω => brownianHeatFlow f (σ^2*((j : ℝ)-(i : ℝ))).toNNReal
        (L i ω+β*((j : ℝ)-(i : ℝ)))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}

/-- The log state `x+β*t+σ*W_t`: drift `β` and volatility `σ` applied to the process `W`, started
at `x`. -/
noncomputable def logState (W : ℝ≥0 → Ω → ℝ) (β σ x : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x+β*(t : ℝ)+σ*W t ω

/-- For a pre-Brownian motion `W` and `i ≤ j`, the expectation of `f (x + σ (W_j - W_i))` is the
heat flow of `f` over the variance `σ² (j - i)`, from `x`. -/
theorem scaled_increment_heatFlow (hW : IsPreBrownianReal W P) {f : ℝ → ℝ} (hf : Continuous f)
    {i j : ℝ≥0} (hij : i ≤ j) (σ x : ℝ) :
    (∫ ω, f (x+σ*(W j ω-W i ω)) ∂P) =
      brownianHeatFlow f (σ^2*((j : ℝ)-(i : ℝ))).toNNReal x := by
  have hΔ : 0 ≤ (j : ℝ)-(i : ℝ) := sub_nonneg.mpr (by exact_mod_cast hij)
  have hv : (NNReal.mk (σ^2) (sq_nonneg σ))*(j-i) = (σ^2*((j : ℝ)-(i : ℝ))).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_mul, NNReal.coe_sub hij, Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) hΔ)]
    rfl
  have hl : HasLaw (fun ω ↦ σ*(W j ω-W i ω))
      (gaussianReal 0 (σ^2*((j : ℝ)-(i : ℝ))).toNNReal) P := by
    convert gaussianReal_const_mul (hasLaw_increment hW hij) σ using 2
    · simp
    · exact hv.symm
  have hm : Continuous (fun y => f (x+y)) := hf.comp (continuous_const.add continuous_id)
  have he := hl.integral_comp hm.aestronglyMeasurable
  have he' := (hasLaw_brownian_eval (t := (σ^2*((j : ℝ)-(i : ℝ))).toNNReal)).integral_comp
    hm.aestronglyMeasurable
  exact he.trans he'.symm

/-- **The conditional transition of a filtered pre-Brownian motion.** For continuous bounded `f`,
`i ≤ j` and an `𝓕 i`-measurable `X`, the conditional expectation of `f (X + σ (W_j - W_i))` given
`𝓕 i` is almost surely the heat flow of `f` over `σ² (j - i)`, evaluated at `X`. -/
theorem condExp_transition (hW : IsFilteredPreBrownian W 𝓕 P) {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) {i j : ℝ≥0} (hij : i ≤ j)
    {X : Ω → ℝ} (hX : Measurable[𝓕 i] X) (σ : ℝ) :
    P[fun ω => f (X ω+σ*(W j ω-W i ω)) | 𝓕 i] =ᵐ[P]
      fun ω => brownianHeatFlow f (σ^2*((j : ℝ)-(i : ℝ))).toNNReal (X ω) := by
  have hY : AEMeasurable (fun ω => W j ω-W i ω) P := (hW.hasLaw_sub j i).aemeasurable
  have hH : Continuous (fun z : ℝ × ℝ => f (z.1+σ*z.2)) := by fun_prop
  have hint : Integrable (fun ω => f (X ω+σ*(W j ω-W i ω))) P :=
    (integrable_const C).mono' (hH.measurable.comp_aemeasurable
      ((hX.mono (𝓕.le i) le_rfl).aemeasurable.prodMk hY)).aestronglyMeasurable
      (Eventually.of_forall fun ω => hb _)
  have he := condExp_comp_prodMk_of_indep (𝓕.le i) hX hY (hW.indep i j hij)
    hH.stronglyMeasurable hint
  filter_upwards [he] with ω hω
  rw [hω]
  have hmap := integral_map (μ := P) hY
    (hf.comp (show Continuous (fun y : ℝ => X ω+σ*y) by fun_prop)).aestronglyMeasurable
  exact hmap.trans (scaled_increment_heatFlow hW.toIsPreBrownianReal hf hij σ (X ω))

/-- A filtered pre-Brownian motion has a Gaussian Markov log state, whatever its probability
space and filtration. -/
theorem logState_isGaussianMarkov (hW : IsFilteredPreBrownian W 𝓕 P) (β σ x : ℝ) :
    IsGaussianMarkov P 𝓕 β σ (logState W β σ x) := by
  intro f C hf hb i j hij
  let X : Ω → ℝ := fun ω => logState W β σ x i ω+β*((j : ℝ)-(i : ℝ))
  have hX : Measurable[𝓕 i] X :=
    (measurable_const.add (measurable_const.mul (hW.stronglyAdapted i).measurable)).add
      measurable_const
  have he := condExp_transition hW hf hb hij hX σ
  have heq : (fun ω => f (X ω+σ*(W j ω-W i ω))) = fun ω => f (logState W β σ x j ω) := by
    funext ω
    congr 1
    dsimp [X,logState]
    ring
  rw [heq] at he
  exact he

end MathFin.BlackScholes.AmericanPut.Stopping
