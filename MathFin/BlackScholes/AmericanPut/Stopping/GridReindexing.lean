/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.BermudanConvergence
public import MathFin.BlackScholes.AmericanPut.Stopping.DiscreteStoppingValue

/-! # Reindexing capped physical-time exercise grids

Both conversions preserve the original filtration's information at the actual
exercise time. The possibly shorter last interval and maturity zero are included.

## Result

Public entry points include `rounded_grid_time_eq`, `StoppingRule.toGridIndexRule_time`,
`gridReward`, `gridValue_eq_discreteValue`. The capped grid and the two conversions
(`StoppingRule.toGridIndexRule`, `StoppingRule.toPhysicalRule`) are in `FiniteExerciseGrid`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

theorem rounded_grid_time_eq {T δ t : ℝ≥0} (hδ : 0 < δ) (ht : t ∈ exerciseGrid T δ) :
    min ((⌈t/δ⌉₊ : ℝ≥0)*δ) T = t := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
  by_cases hj : (j : ℝ≥0)*δ ≤ T
  · simp [cappedGridTime,min_eq_left hj,hδ.ne']
  · have hT : T ≤ (⌈T/δ⌉₊ : ℝ≥0)*δ := (div_le_iff₀ hδ).mp (Nat.le_ceil (T/δ))
    simp only [cappedGridTime,min_eq_right (le_of_not_ge hj),min_eq_right hT]

variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T δ : ℝ≥0}

theorem StoppingRule.toGridIndexRule_time (θ : StoppingRule 𝓕 T)
    (hθ : θ ∈ StoppingRule.valuedIn 𝓕 T (exerciseGrid T δ)) (hδ : 0 < δ) (ω : Ω) :
    cappedGridTime T δ ((θ.toGridIndexRule hδ).time ω) = θ.time ω :=
  rounded_grid_time_eq hδ (hθ ω)

/-- The put reward collected at the deterministic capped grid time `min (i*δ) T`. -/
noncomputable def gridReward (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T δ : ℝ≥0)
    (i : ℕ) : Ω → ℝ :=
  putRewardAt W K r q σ S (cappedGridTime T δ i)

theorem gridValue_eq_discreteValue (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (K r q σ S : ℝ) (hδ : 0 < δ) :
    gridAmericanPutValue P 𝓕 W K r q σ S T δ =
      stoppingValue P (cappedGridFiltration 𝓕 T δ) (gridReward W K r q σ S T δ) ⌈T/δ⌉₊ := by
  unfold gridAmericanPutValue stoppingValue
  congr 1
  ext v
  constructor
  · rintro ⟨θ,hθ,rfl⟩
    refine ⟨θ.toGridIndexRule hδ,mem_univ _,?_⟩
    apply integral_congr_ae
    apply Eventually.of_forall
    intro ω
    simp only [gridReward,← θ.toGridIndexRule_time hθ hδ ω]
  · rintro ⟨η,-,rfl⟩
    exact ⟨η.toPhysicalRule hδ,η.toPhysicalRule_mem_grid hδ,rfl⟩

end MathFin.BlackScholes.AmericanPut.Stopping
