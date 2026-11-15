/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Probability.Discrete.FiniteBellmanOptimality
public import MathFin.Probability.Martingales.StoppingRule

/-! # Snell envelope (the Bellman recursion) and the stopping value over `ℕ`

For an adapted integrable reward process on a discrete filtration, `stoppingValue` (the supremum
over all rules with horizon `N`) is the expectation of the finite Snell envelope at index `0`,
and the Snell first-contact rule attains it.

## Main definitions

* `snellRule`: the Snell first-contact time of `Z`, packaged as a discrete rule with horizon `N`.

## Main results

* `stoppingValue_eq_integral_snellEnvelope`: for an adapted integrable reward `Z`, the stopping
  value with horizon `N` is the expectation of the Snell envelope at index `0`.
* `snellRule_attains_value`: the expected reward at the Snell first-contact rule equals the
  stopping value.
* `snellEnvelope_optimalStopping`: Snell's theorem — the envelope is the least supermartingale
  dominating the reward, and its expectation at `0` is the stopping value, attained at first
  contact.

## Tags

Snell envelope, Bellman recursion, discrete optimal stopping, stopping value, first-contact rule,
MSC 60G40, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Set Filter MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Snell first-contact time of `Z`, packaged as a discrete rule with horizon `N`. -/
noncomputable def snellRule {P : Measure Ω} {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›}
    {Z : ℕ → Ω → ℝ} (ha : Adapted 𝓕 Z) (N : ℕ) : StoppingRule 𝓕 N :=
  ⟨snellContact P 𝓕 Z N,snellContact_stopping ha N,snellContact_le N⟩

theorem stoppingValue_eq_integral_snellEnvelope {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ}
    (ha : Adapted 𝓕 Z) (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    stoppingValue P 𝓕 Z N = ∫ ω, snellEnvelope P 𝓕 Set.univ Z N 0 ω ∂P := by
  have hle (θ : StoppingRule 𝓕 N) :
      (∫ ω, Z (θ.time ω) ω ∂P) ≤ ∫ ω, snellEnvelope P 𝓕 Set.univ Z N 0 ω ∂P :=
    expected_discrete_payoff_le_snellEnvelope ha hi θ.stopping θ.le_horizon
  apply le_antisymm
  · exact stoppingValue_le univ_nonempty fun θ _ ↦ hle θ
  · rw [← snellContact_expected_payoff ha hi N]
    exact integral_le_stoppingValue (fun θ _ ↦ hle θ) (mem_univ (snellRule ha N))

theorem snellRule_attains_value {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ}
    (ha : Adapted 𝓕 Z) (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    (∫ ω, Z ((snellRule (P := P) ha N).time ω) ω ∂P) = stoppingValue P 𝓕 Z N := by
  rw [stoppingValue_eq_integral_snellEnvelope ha hi N]
  exact snellContact_expected_payoff ha hi N

/-- **Snell's theorem.** For an adapted integrable reward `Z` with horizon `N`, exercisable at every
date, the Snell envelope is a supermartingale, it lies almost surely below every supermartingale
that dominates `Z` up to `N`, and its expectation at `0` is the value of the optimal stopping
problem, attained by the first time it meets the reward. -/
theorem snellEnvelope_optimalStopping {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ}
    (ha : Adapted 𝓕 Z) (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    Supermartingale (snellEnvelope P 𝓕 univ Z N) 𝓕 P ∧
      (∀ ⦃U : ℕ → Ω → ℝ⦄, Supermartingale U 𝓕 P → (∀ j ≤ N, Z j ≤ᵐ[P] U j) →
        ∀ i ≤ N, snellEnvelope P 𝓕 univ Z N i ≤ᵐ[P] U i) ∧
      stoppingValue P 𝓕 Z N = ∫ ω, snellEnvelope P 𝓕 univ Z N 0 ω ∂P ∧
      ∫ ω, Z ((snellRule (P := P) ha N).time ω) ω ∂P = stoppingValue P 𝓕 Z N :=
  ⟨snellEnvelope_supermartingale ha hi N,
    fun _ hU hdom _ hiN ↦ snellEnvelope_le_supermartingale hU hi (fun j hj _ ↦ hdom j hj) hiN,
    stoppingValue_eq_integral_snellEnvelope ha hi N, snellRule_attains_value ha hi N⟩

end MathFin
