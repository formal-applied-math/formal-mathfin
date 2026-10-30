/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FiniteBellmanOptimality
public import MathFin.BlackScholes.AmericanPut.Stopping.Rules

/-! # Bellman identification of the stopping value over `ℕ`

For an adapted integrable reward process on a discrete filtration, `stoppingValue` (the supremum
over all rules with horizon `N`) is the expectation of the finite Bellman envelope at index `0`,
and the Bellman first-contact rule attains it.

## Result

Public entry points include `finiteBellmanRule`, `stoppingValue_eq_bellman`,
`finiteBellmanRule_attains_value`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Bellman first-contact time of `Z`, packaged as a discrete rule with horizon `N`. -/
noncomputable def finiteBellmanRule {P : Measure Ω} {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›}
    {Z : ℕ → Ω → ℝ} (ha : Adapted 𝓕 Z) (N : ℕ) : StoppingRule 𝓕 N :=
  ⟨finiteBellmanContact P 𝓕 Z N,finiteBellmanContact_stopping ha N,finiteBellmanContact_le N⟩

theorem stoppingValue_eq_bellman {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ}
    (ha : Adapted 𝓕 Z) (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    stoppingValue P 𝓕 Z N = ∫ ω, finiteBellman P 𝓕 Z N 0 ω ∂P := by
  have hle (θ : StoppingRule 𝓕 N) :
      (∫ ω, Z (θ.time ω) ω ∂P) ≤ ∫ ω, finiteBellman P 𝓕 Z N 0 ω ∂P :=
    expected_discrete_payoff_le_bellman ha hi θ.stopping θ.le_horizon
  apply le_antisymm
  · exact stoppingValue_le univ_nonempty fun θ _ ↦ hle θ
  · rw [← finiteBellmanContact_expected_payoff ha hi N]
    exact integral_le_stoppingValue (fun θ _ ↦ hle θ) (mem_univ (finiteBellmanRule ha N))

theorem finiteBellmanRule_attains_value {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ}
    (ha : Adapted 𝓕 Z) (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    (∫ ω, Z ((finiteBellmanRule (P := P) ha N).time ω) ω ∂P) = stoppingValue P 𝓕 Z N := by
  rw [stoppingValue_eq_bellman ha hi N]
  exact finiteBellmanContact_expected_payoff ha hi N

end MathFin.BlackScholes.AmericanPut.Stopping
