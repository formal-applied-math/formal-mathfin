/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.DiscreteStoppingValue
public import MathFin.BlackScholes.AmericanPut.Stopping.AmericanValue
public import MathFin.Foundations.ContinuousMarket

/-! # Discrete rules sampled at arbitrary deterministic increasing times 
## Result

Public entry points include `StoppingRule.toSampledRule`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A discrete rule `η` for `ContinuousMarket.sampledFiltration 𝓕 hs` read back in continuous
time as `ω ↦ s (η.time ω)`, with horizon `s N`. -/
def StoppingRule.toSampledRule {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {s : ℕ → ℝ≥0} {hs : Monotone s} {N : ℕ}
    (η : StoppingRule (ContinuousMarket.sampledFiltration 𝓕 hs) N) : StoppingRule 𝓕 (s N) where
  time := fun ω => s (η.time ω)
  stopping := by
    intro t
    have he : {ω | (s (η.time ω) : WithTop ℝ≥0) ≤ t} =
        ⋃ i : ℕ, if s i ≤ t then {ω | (η.time ω : WithTop ℕ) ≤ i} else ∅ := by
      ext ω
      simp only [mem_ofPred_eq,WithTop.coe_le_coe,mem_iUnion]
      constructor
      · intro hω
        refine ⟨η.time ω,?_⟩
        simp [hω]
      · rintro ⟨i,hi⟩
        split_ifs at hi with hit
        · exact (hs (by simpa using hi)).trans hit
        · exact False.elim (notMem_empty ω hi)
    rw [he]
    apply MeasurableSet.iUnion
    intro i
    split_ifs with hit
    · exact 𝓕.mono hit _ (η.stopping i)
    · exact @MeasurableSet.empty Ω (𝓕 t)
  le_horizon := fun ω => hs (η.le_horizon ω)

end MathFin.BlackScholes.AmericanPut.Stopping
