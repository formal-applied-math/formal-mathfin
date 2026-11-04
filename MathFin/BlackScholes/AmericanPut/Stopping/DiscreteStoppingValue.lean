/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FiniteBellmanOptimality
public import MathFin.BlackScholes.AmericanPut.Stopping.Rules

/-! # Snell envelope (the Bellman recursion) and the stopping value over `ℕ`

For an adapted integrable reward process on a discrete filtration, `stoppingValue` (the supremum
over all rules with horizon `N`) is the expectation of the finite Snell envelope at index `0`,
and the Snell first-contact rule attains it.

## Result

Public entry points include `snellRule`, `stoppingValue_eq_integral_snellEnvelope`,
`snellRule_attains_value`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

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

end MathFin.BlackScholes.AmericanPut.Stopping
