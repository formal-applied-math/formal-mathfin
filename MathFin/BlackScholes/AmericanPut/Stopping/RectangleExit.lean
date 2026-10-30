/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FirstContact

/-! # Admissible exit from a backward space-time rectangle 
## Result

Public entry points include `rectangleMargin`, `rectangleMargin_continuous`,
`rectangleMargin_adapted`, `rectangleMargin_nonneg`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {X : ℝ≥0 → Ω → ℝ}

/-- The margin `max 0 (min (R-|X t ω-x|) (δ-t))`: how far the path still is from the spatial
radius `R` around `x` or from the terminal time `δ`, whichever is closer. -/
noncomputable def rectangleMargin (X : ℝ≥0 → Ω → ℝ) (x R : ℝ) (δ t : ℝ≥0) (ω : Ω) : ℝ :=
  max 0 (min (R-|X t ω-x|) ((δ : ℝ)-(t : ℝ)))

omit [MeasurableSpace Ω] in
theorem rectangleMargin_continuous (hc : ∀ ω, Continuous (fun t => X t ω))
    (x R : ℝ) (δ : ℝ≥0) (ω : Ω) : Continuous (fun t => rectangleMargin X x R δ t ω) := by
  unfold rectangleMargin
  fun_prop

theorem rectangleMargin_adapted (ha : Adapted 𝓕 X) (x R : ℝ) (δ : ℝ≥0) :
    Adapted 𝓕 (rectangleMargin X x R δ) := by
  intro t
  have ht := ha t
  letI : MeasurableSpace Ω := 𝓕 t
  exact measurable_const.max
      ((measurable_const.sub (ht.sub measurable_const).abs).min measurable_const)

omit [MeasurableSpace Ω] in
theorem rectangleMargin_nonneg (x R : ℝ) (δ t : ℝ≥0) (ω : Ω) : 0 ≤ rectangleMargin X x R δ t ω :=
  le_max_left _ _

omit [MeasurableSpace Ω] in
theorem rectangleMargin_terminal (x R : ℝ) (δ : ℝ≥0) (ω : Ω) : rectangleMargin X x R δ δ ω = 0 := by
  unfold rectangleMargin
  rw [sub_self]
  exact max_eq_left (min_le_right _ _)

/-- The first time the margin `rectangleMargin X x R δ` vanishes, as a rule with horizon `δ`. -/
noncomputable def rectangleExitRule (ha : Adapted 𝓕 X) (hc : ∀ ω, Continuous (fun t => X t ω))
    (x R : ℝ) (δ : ℝ≥0) : StoppingRule 𝓕 δ :=
  firstContactRule (rectangleMargin_adapted ha x R δ) (rectangleMargin_continuous hc x R δ)
    (rectangleMargin_nonneg x R δ) δ (rectangleMargin_terminal x R δ)

theorem rectangleExitRule_before (ha : Adapted 𝓕 X) (hc : ∀ ω, Continuous (fun t => X t ω))
    {x R : ℝ} {δ t : ℝ≥0} (ω : Ω) (ht : t < (rectangleExitRule ha hc x R δ).time ω) :
    |X t ω-x| < R ∧ t < δ := by
  have hh := firstContactTime_pos_before (rectangleMargin_continuous hc x R δ)
    (rectangleMargin_nonneg x R δ) (rectangleMargin_terminal x R δ) ω ht
  change 0 < max 0 (min _ _) at hh
  simp only [lt_max_iff,lt_self_iff_false,false_or,lt_min_iff,sub_pos] at hh
  exact ⟨hh.1,by exact_mod_cast hh.2⟩

theorem rectangleExitRule_pos (ha : Adapted 𝓕 X) (hc : ∀ ω, Continuous (fun t => X t ω))
    {x R : ℝ} {δ : ℝ≥0} (hδ : 0 < δ) (ω : Ω) (hstart : |X 0 ω - x| < R) :
    0 < (rectangleExitRule ha hc x R δ).time ω := by
  have hz := (firstContactTime_mem (rectangleMargin_continuous hc x R δ)
    (rectangleMargin_terminal x R δ) ω).2
  change rectangleMargin X x R δ ((rectangleExitRule ha hc x R δ).time ω) ω = 0 at hz
  by_contra! hn
  have he : (rectangleExitRule ha hc x R δ).time ω = 0 := le_antisymm hn zero_le
  rw [he] at hz
  have hp : 0 < rectangleMargin X x R δ 0 ω := by
    apply lt_max_of_lt_right
    exact lt_min (sub_pos.mpr hstart) (by simpa using (show (0 : ℝ) < δ by exact_mod_cast hδ))
  exact (ne_of_gt hp) hz

theorem rectangleExitRule_spatial_bound (ha : Adapted 𝓕 X) (hc : ∀ ω, Continuous (fun t => X t ω))
    {x R : ℝ} {δ : ℝ≥0} (ω : Ω) (hτ : 0 < (rectangleExitRule ha hc x R δ).time ω) :
    |X ((rectangleExitRule ha hc x R δ).time ω) ω-x| ≤ R := by
  let τ := (rectangleExitRule ha hc x R δ).time ω
  have hclosed : IsClosed {t : ℝ≥0 | |X t ω-x| ≤ R} :=
    isClosed_le ((hc ω).sub continuous_const).abs continuous_const
  have hsub : Iio τ ⊆ {t | |X t ω-x| ≤ R} :=
    fun t ht => (rectangleExitRule_before ha hc ω ht).1.le
  have hm : τ ∈ closure (Iio τ) := by
    rw [closure_Iio' (show (Iio τ).Nonempty from ⟨0,hτ⟩)]
    exact (show τ ≤ τ from le_rfl)
  exact hclosed.closure_subset_iff.mpr hsub hm

theorem rectangleExitRule_boundary (ha : Adapted 𝓕 X) (hc : ∀ ω, Continuous (fun t => X t ω))
    {x R : ℝ} {δ : ℝ≥0} (ω : Ω) (hτ : 0 < (rectangleExitRule ha hc x R δ).time ω) :
    let τ := (rectangleExitRule ha hc x R δ).time ω
    |X τ ω-x| = R ∨ τ = δ := by
  let τ := (rectangleExitRule ha hc x R δ).time ω
  have hs := rectangleExitRule_spatial_bound ha hc ω hτ
  have ht := (rectangleExitRule ha hc x R δ).le_horizon ω
  have hz := (firstContactTime_mem (rectangleMargin_continuous hc x R δ)
    (rectangleMargin_terminal x R δ) ω).2
  change max 0 (min (R-|X τ ω-x|) ((δ : ℝ)-(τ : ℝ))) = 0 at hz
  have hm := (le_max_right 0 (min (R-|X τ ω-x|) ((δ : ℝ)-(τ : ℝ)))).trans hz.le
  rcases min_le_iff.mp hm with hspace | htime
  · left
    linarith
  · right
    apply le_antisymm ht
    exact_mod_cast (show (δ : ℝ) ≤ (τ : ℝ) by linarith)

end MathFin.BlackScholes.AmericanPut.Stopping
