/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.GridSampling
public import MathFin.BlackScholes.AmericanPut.Stopping.MaturityTruncation

/-! # Finite exercise grids within the original continuous-time model

Upward rounding, capped at maturity, preserves stopping-time admissibility.
No Brownian law, usual-filtration property or PDE solution is needed here.

## Result

Public entry points include `exerciseGrid`, `zero_mem_exerciseGrid`, `maturity_mem_exerciseGrid`, `rounded_time_stopping`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

/-- The finite set of exercise times `min ((i : ℝ≥0)*δ) T` for `i ≤ ⌈T/δ⌉₊`. -/
noncomputable def exerciseGrid (T δ : ℝ≥0) : Finset ℝ≥0 :=
  (Finset.range (⌈T/δ⌉₊+1)).image (fun i : ℕ => min ((i : ℝ≥0)*δ) T)

theorem zero_mem_exerciseGrid (T δ : ℝ≥0) : 0 ∈ exerciseGrid T δ := by
  apply Finset.mem_image.mpr
  exact ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _),by simp⟩

theorem maturity_mem_exerciseGrid (T : ℝ≥0) {δ : ℝ≥0} (hδ : 0 < δ) :
    T ∈ exerciseGrid T δ := by
  have hT : T ≤ (⌈T/δ⌉₊ : ℝ≥0)*δ := (div_le_iff₀ hδ).mp (Nat.le_ceil (T/δ))
  apply Finset.mem_image.mpr
  exact ⟨⌈T/δ⌉₊,Finset.mem_range.mpr (Nat.lt_succ_self _),min_eq_right hT⟩

variable {Ω : Type*} [MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T δ : ℝ≥0}

theorem rounded_time_stopping (θ : BoundedRule 𝓕 T) (hδ : 0 < δ) :
    IsStoppingTime 𝓕 (fun ω => ((min ((gridIndex θ δ ω : ℝ≥0)*δ) T : ℝ≥0) : WithTop ℝ≥0)) := by
  intro t
  by_cases hT : T ≤ t
  · have he : {ω | ((min ((gridIndex θ δ ω : ℝ≥0)*δ) T : ℝ≥0) : WithTop ℝ≥0) ≤ t} = univ := by
      ext ω
      simp only [mem_ofPred_eq,WithTop.coe_le_coe,mem_univ,iff_true]
      exact (min_le_right _ _).trans hT
    rw [he]
    exact MeasurableSet.univ
  · have hfloor : (⌊t/δ⌋₊ : ℝ≥0)*δ ≤ t := by
      exact (le_div_iff₀ hδ).mp (Nat.floor_le (show (0 : ℝ≥0) ≤ t/δ from bot_le))
    have he : {ω | ((min ((gridIndex θ δ ω : ℝ≥0)*δ) T : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
        {ω | θ.time ω ≤ (⌊t/δ⌋₊ : ℝ≥0)*δ} := by
      ext ω
      simp only [mem_ofPred_eq,WithTop.coe_le_coe,min_le_iff,hT,or_false]
      rw [← le_div_iff₀ hδ,← Nat.le_floor_iff (show (0 : ℝ≥0) ≤ t/δ from bot_le),
        gridIndex_le_iff θ hδ]
    rw [he]
    exact 𝓕.mono hfloor _ (by simpa only [WithTop.coe_le_coe] using θ.stopping ((⌊t/δ⌋₊ : ℝ≥0)*δ))

/-- The rule `θ` rounded up to the next multiple of `δ` and capped at maturity, exercising at
`min ((⌈θ.time ω/δ⌉₊ : ℝ≥0)*δ) T`. -/
noncomputable def BoundedRule.roundUp (θ : BoundedRule 𝓕 T) (hδ : 0 < δ) : BoundedRule 𝓕 T where
  time := fun ω => min ((gridIndex θ δ ω : ℝ≥0)*δ) T
  stopping := rounded_time_stopping θ hδ
  le_horizon := fun _ => min_le_right _ _

theorem BoundedRule.le_roundUp (θ : BoundedRule 𝓕 T) (hδ : 0 < δ) (ω : Ω) :
    θ.time ω ≤ (θ.roundUp hδ).time ω :=
  le_min ((div_le_iff₀ hδ).mp (Nat.le_ceil (θ.time ω/δ))) (θ.le_horizon ω)

theorem BoundedRule.roundUp_mem_grid (θ : BoundedRule 𝓕 T) (hδ : 0 < δ) (ω : Ω) :
    (θ.roundUp hδ).time ω ∈ exerciseGrid T δ := by
  apply Finset.mem_image.mpr
  exact ⟨gridIndex θ δ ω,Finset.mem_range.mpr (Nat.lt_succ_of_le (gridIndex_bounded θ ω)),rfl⟩

theorem BoundedRule.roundUp_time_tendsto (θ : BoundedRule 𝓕 T) (ω : Ω) :
    Tendsto (fun n => (θ.roundUp (gridStep_pos n)).time ω) atTop (𝓝 (θ.time ω)) := by
  have hh := (gridValue_time_tendsto θ ω).min (tendsto_const_nhds (x := T))
  simpa only [BoundedRule.roundUp,min_eq_left (θ.le_horizon ω)] using hh

theorem expectedReward_roundUp_tendsto {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    {K r q σ S : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (θ : BoundedRule 𝓕 T) :
    Tendsto (fun n => ∫ ω, putReward W K r q σ S (θ.roundUp (gridStep_pos n)).time ω ∂P)
      atTop (𝓝 (∫ ω, putReward W K r q σ S θ.time ω ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => K)
  · intro n
    exact (putReward_measurable hW K r q σ S (θ.roundUp (gridStep_pos n)).measurable_time).aestronglyMeasurable
  · exact integrable_const K
  · intro n
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_of_nonneg (putReward_nonneg W K r q σ S _ ω)]
    exact putReward_le_strike W hK hr hS _ ω
  · exact Eventually.of_forall (fun ω =>
      ((putReward_time_continuous hpaths K r q σ S ω).tendsto (θ.time ω)).comp
        (θ.roundUp_time_tendsto ω))

end MathFin.BlackScholes.AmericanPut.Stopping
