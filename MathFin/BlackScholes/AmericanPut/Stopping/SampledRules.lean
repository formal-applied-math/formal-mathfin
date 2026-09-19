/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.DiscreteStoppingValue
public import MathFin.BlackScholes.AmericanPut.Stopping.AmericanValue

/-! # Discrete rules sampled at arbitrary deterministic increasing times 
## Result

Public entry points include `sampledFiltration`, `DiscreteRule.toSampledRule`, `bellmanAux_const_mul`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The discrete filtration `i ↦ 𝓕 (s i)` obtained by sampling `𝓕` along the monotone times `s`. -/
def sampledFiltration (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (s : ℕ → ℝ≥0) (hs : Monotone s) : Filtration ℕ ‹MeasurableSpace Ω› where
  seq := fun i => 𝓕 (s i)
  mono' := fun _ _ hij => 𝓕.mono (hs hij)
  le' := fun i => 𝓕.le (s i)

/-- A discrete rule `η` for `sampledFiltration 𝓕 s hs` read back in continuous time as
`ω ↦ s (η.time ω)`, with horizon `s N`. -/
def DiscreteRule.toSampledRule {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {s : ℕ → ℝ≥0} {hs : Monotone s} {N : ℕ}
    (η : DiscreteRule (sampledFiltration 𝓕 s hs) N) : BoundedRule 𝓕 (s N) where
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

theorem bellmanAux_const_mul {P : Measure Ω} {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›}
    (Z : ℕ → Ω → ℝ) {a : ℝ} (ha : 0 ≤ a) (n i : ℕ) :
    bellmanAux P 𝓕 (fun j ω => a*Z j ω) n i =ᵐ[P]
      fun ω => a*bellmanAux P 𝓕 Z n i ω := by
  induction n generalizing i with
  | zero => exact Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    have hc := condExp_congr_ae (m := 𝓕 i) (ih (i+1))
    have hm := condExp_smul (μ := P) a (bellmanAux P 𝓕 Z n (i+1)) (𝓕 i)
    filter_upwards [hc,hm] with ω hω hmω
    change max (a*Z i ω) _ = a*max (Z i ω) _
    rw [hω]
    change P[fun ω => a*bellmanAux P 𝓕 Z n (i+1) ω | 𝓕 i] ω = _ at hmω
    rw [hmω]
    exact (mul_max_of_nonneg _ _ ha).symm

end MathFin.BlackScholes.AmericanPut.Stopping
