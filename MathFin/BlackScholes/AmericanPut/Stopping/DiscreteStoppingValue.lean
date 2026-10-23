/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FiniteBellmanOptimality

/-! # Bellman identification with a supremum over discrete stopping rules 
## Result

Public entry points include `DiscreteRule`, `DiscreteRule.zero`, `discreteStoppingValue`,
`finiteBellmanRule`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An exercise rule indexed by `ℕ`: an `𝓕`-stopping time bounded by the horizon `N`. -/
structure DiscreteRule (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (N : ℕ) where
  /-- The index at which the rule exercises. -/
  time : Ω → ℕ
  stopping : IsStoppingTime 𝓕 (fun ω => (time ω : WithTop ℕ))
  le_horizon : ∀ ω, time ω ≤ N

/-- The rule that exercises immediately, at index `0`. -/
def DiscreteRule.zero (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (N : ℕ) : DiscreteRule 𝓕 N :=
  ⟨fun _ => 0,isStoppingTime_const 𝓕 0,fun _ => Nat.zero_le _⟩

instance discreteRule_nonempty (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (N : ℕ) :
    Nonempty (DiscreteRule 𝓕 N) := ⟨DiscreteRule.zero 𝓕 N⟩

/-- The supremum of the expected payoffs `∫ ω, Z (θ.time ω) ω ∂P` over all discrete rules with
horizon `N`. -/
noncomputable def discreteStoppingValue (P : Measure Ω) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›)
    (Z : ℕ → Ω → ℝ) (N : ℕ) : ℝ :=
  sSup (range (fun θ : DiscreteRule 𝓕 N => ∫ ω, Z (θ.time ω) ω ∂P))

/-- The Bellman first-contact time of `Z`, packaged as a discrete rule with horizon `N`. -/
noncomputable def finiteBellmanRule {P : Measure Ω} {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›}
    {Z : ℕ → Ω → ℝ} (ha : Adapted 𝓕 Z) (N : ℕ) : DiscreteRule 𝓕 N :=
  ⟨finiteBellmanContact P 𝓕 Z N,finiteBellmanContact_stopping ha N,finiteBellmanContact_le N⟩

theorem discreteStoppingValue_eq_bellman {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ}
    (ha : Adapted 𝓕 Z) (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    discreteStoppingValue P 𝓕 Z N = ∫ ω, finiteBellman P 𝓕 Z N 0 ω ∂P := by
  have hb : BddAbove (range (fun θ : DiscreteRule 𝓕 N => ∫ ω, Z (θ.time ω) ω ∂P)) := by
    refine ⟨∫ ω, finiteBellman P 𝓕 Z N 0 ω ∂P,?_⟩
    rintro _ ⟨θ,rfl⟩
    exact expected_discrete_payoff_le_bellman ha hi θ.stopping θ.le_horizon
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro _ ⟨θ,rfl⟩
    exact expected_discrete_payoff_le_bellman ha hi θ.stopping θ.le_horizon
  · rw [← finiteBellmanContact_expected_payoff ha hi N]
    exact le_csSup hb ⟨finiteBellmanRule ha N,rfl⟩

theorem finiteBellmanRule_attains_value {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ}
    (ha : Adapted 𝓕 Z) (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    (∫ ω, Z ((finiteBellmanRule (P := P) ha N).time ω) ω ∂P) = discreteStoppingValue P 𝓕 Z N := by
  rw [discreteStoppingValue_eq_bellman ha hi N]
  exact finiteBellmanContact_expected_payoff ha hi N

end MathFin.BlackScholes.AmericanPut.Stopping
