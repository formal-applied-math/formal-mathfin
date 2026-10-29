/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FiltrationExtension

/-! # Completing the ambient probability space

Original measurable integrals are unchanged, and bounded supermartingales lift
to the same filtration regarded inside the completed ambient space.

## Result

Public entry points include `completedMeasure`, `ambient_le_completion`, `completion_trim_original`,
`integral_completion_original`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)

/-- The `P`-completion of the ambient σ-algebra: the sets that agree `P`-almost everywhere
with an `mΩ`-measurable set. -/
@[reducible] noncomputable def completedMeasurableSpace : MeasurableSpace Ω :=
  eventuallyMeasurableSpace mΩ (ae P)

/-- The completion of `P`, read as a measure on the completed σ-algebra. -/
noncomputable def completedMeasure : @Measure Ω (completedMeasurableSpace P) := P.completion

theorem ambient_le_completion : mΩ ≤ completedMeasurableSpace P :=
  fun _ hs => hs.nullMeasurableSet

theorem completion_trim_original : (completedMeasure P).trim (ambient_le_completion P) = P := by
  ext s hs
  rw [trim_measurableSet_eq (ambient_le_completion P) hs]
  rfl

theorem integral_completion_original {f : Ω → ℝ} (hf : StronglyMeasurable f) :
    (∫ ω, f ω ∂completedMeasure P) = ∫ ω, f ω ∂P := by
  rw [integral_trim (ambient_le_completion P) hf,completion_trim_original]

/-- The same filtration `𝓕`, regarded as a filtration of the completed ambient σ-algebra. -/
noncomputable def completedAmbientFiltration (𝓕 : Filtration ℝ≥0 mΩ) :
    Filtration ℝ≥0 (completedMeasurableSpace P) where
  seq := fun t => 𝓕 t
  mono' := fun _ _ h => 𝓕.mono h
  le' := fun t => (𝓕.le t).trans (ambient_le_completion P)

instance completion_isProbabilityMeasure [IsProbabilityMeasure P] : IsProbabilityMeasure
    (completedMeasure P) :=
  ⟨by change P Set.univ = 1; exact measure_univ⟩

instance completedMeasure_isComplete : (completedMeasure P).IsComplete :=
  ⟨fun _ hs => NullMeasurableSet.of_null hs⟩

theorem bounded_supermartingale_completion [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {U : ℝ≥0 → Ω → ℝ}
    (hU : Supermartingale U 𝓕 P) {C : ℝ} (hb : ∀ t ω, ‖U t ω‖ ≤ C) :
    Supermartingale U (completedAmbientFiltration P 𝓕) (completedMeasure P) := by
  have hA := hU.stronglyAdapted
  apply supermartingale_of_setIntegral_ge (mΩ := completedMeasurableSpace P)
    (𝓕 := completedAmbientFiltration P 𝓕)
    (P := completedMeasure P) (fun t => hA t)
    (fun t => (integrable_const C).mono'
      ((hA t).mono (((𝓕.le t).trans (ambient_le_completion P)))).aestronglyMeasurable
      (Eventually.of_forall (hb t)))
  intro i j hij s hs
  have hs0 : MeasurableSet[mΩ] s := 𝓕.le i s hs
  have hs1 : MeasurableSet[completedMeasurableSpace P] s :=
    ambient_le_completion P s hs0
  have he (t : ℝ≥0) : (∫ ω in s, U t ω ∂completedMeasure P) = ∫ ω in s, U t ω ∂P := by
    rw [← integral_indicator hs1,← integral_indicator hs0]
    exact integral_completion_original P (((hA t).mono (𝓕.le t)).indicator hs0)
  rw [he j,he i]
  exact hU.setIntegral_le hij hs

end MathFin.BlackScholes.AmericanPut.Stopping
