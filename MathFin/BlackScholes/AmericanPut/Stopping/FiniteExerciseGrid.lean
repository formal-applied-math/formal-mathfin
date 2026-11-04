/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.GridSampling
public import MathFin.BlackScholes.AmericanPut.Stopping.MaturityTruncation
public import MathFin.BlackScholes.AmericanPut.Stopping.SampledRules

/-! # Finite exercise grids within the original continuous-time model

Upward rounding, capped at maturity, preserves stopping-time admissibility. The capped grid
`cappedGridTime T δ` samples the filtration (`cappedGridFiltration`), a rule is read on the sampled
filtration by `StoppingRule.toGridIndexRule` and back in physical time by
`StoppingRule.toPhysicalRule`, and rounding up is the composite of the two: its admissibility is
that of the sampled rule, not a separate argument. No Brownian law, usual-filtration property or
PDE solution is needed here.

## Result

Public entry points include `exerciseGrid`, `zero_mem_exerciseGrid`, `maturity_mem_exerciseGrid`,
`cappedGridTime`, `cappedGridFiltration`, `StoppingRule.toGridIndexRule`,
`StoppingRule.toPhysicalRule`, `StoppingRule.roundUp`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

/-- The `i`-th grid time `i*δ`, capped at the horizon `T`. -/
def cappedGridTime (T δ : ℝ≥0) (i : ℕ) : ℝ≥0 := min ((i : ℝ≥0)*δ) T

theorem cappedGridTime_mono (T δ : ℝ≥0) : Monotone (cappedGridTime T δ) :=
  (gridTime_mono δ).min monotone_const

theorem cappedGridTime_ceil (T : ℝ≥0) {δ : ℝ≥0} (hδ : 0 < δ) : cappedGridTime T δ ⌈T/δ⌉₊ = T :=
  min_eq_right ((div_le_iff₀ hδ).mp (Nat.le_ceil (T/δ)))

/-- The finite set of exercise times `cappedGridTime T δ i = min ((i : ℝ≥0)*δ) T` for
`i ≤ ⌈T/δ⌉₊`. -/
noncomputable def exerciseGrid (T δ : ℝ≥0) : Finset ℝ≥0 :=
  (Finset.range (⌈T/δ⌉₊+1)).image (cappedGridTime T δ)

theorem zero_mem_exerciseGrid (T δ : ℝ≥0) : 0 ∈ exerciseGrid T δ :=
  Finset.mem_image.mpr ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _),by simp [cappedGridTime]⟩

theorem maturity_mem_exerciseGrid (T : ℝ≥0) {δ : ℝ≥0} (hδ : 0 < δ) :
    T ∈ exerciseGrid T δ :=
  Finset.mem_image.mpr ⟨⌈T/δ⌉₊,Finset.mem_range.mpr (Nat.lt_succ_self _),cappedGridTime_ceil T hδ⟩

variable {Ω : Type*} [MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T δ : ℝ≥0}

/-- The continuous filtration sampled at the capped grid times `min (i*δ) T`: the sampled
filtration `ContinuousMarket.sampledFiltration` along `cappedGridTime T δ`. -/
def cappedGridFiltration (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T δ : ℝ≥0) :
    Filtration ℕ ‹MeasurableSpace Ω› :=
  ContinuousMarket.sampledFiltration 𝓕 (cappedGridTime_mono T δ)

/-- A rule read as a rule for `cappedGridFiltration`, indexed by `gridIndex θ δ` and bounded by
`⌈T/δ⌉₊`: the first capped grid time at or after `θ.time ω`. -/
noncomputable def StoppingRule.toGridIndexRule (θ : StoppingRule 𝓕 T) (hδ : 0 < δ) :
    StoppingRule (cappedGridFiltration 𝓕 T δ) ⌈T/δ⌉₊ where
  time := gridIndex θ δ
  stopping := isStoppingTime_sampledFiltration (cappedGridTime_mono T δ) θ (i := gridIndex θ δ)
    fun ω n ↦ by
    rw [gridIndex_le_iff θ hδ, cappedGridTime, le_min_iff, and_iff_left (θ.le_horizon ω)]
  le_horizon := gridIndex_bounded θ

/-- A rule for `cappedGridFiltration` read back in physical time, stopping at the capped grid
time `cappedGridTime T δ (η.time ω)`: `StoppingRule.toSampledRule` along the capped grid, which
ends at the horizon `T`. -/
noncomputable def StoppingRule.toPhysicalRule
    (η : StoppingRule (cappedGridFiltration 𝓕 T δ) ⌈T / δ⌉₊) (hδ : 0 < δ) : StoppingRule 𝓕 T :=
  η.toSampledRule.extend (cappedGridTime_ceil T hδ).le

theorem StoppingRule.toPhysicalRule_mem_grid
    (η : StoppingRule (cappedGridFiltration 𝓕 T δ) ⌈T / δ⌉₊) (hδ : 0 < δ) :
    η.toPhysicalRule hδ ∈ StoppingRule.valuedIn 𝓕 T (exerciseGrid T δ) := fun ω ↦
  Finset.mem_image.mpr ⟨η.time ω,Finset.mem_range.mpr (Nat.lt_succ_of_le (η.le_horizon ω)),rfl⟩

/-- The rule `θ` rounded up to the next multiple of `δ` and capped at maturity, exercising at
`min ((⌈θ.time ω/δ⌉₊ : ℝ≥0)*δ) T`: the rule sampled on the capped grid and read back in physical
time. -/
noncomputable def StoppingRule.roundUp (θ : StoppingRule 𝓕 T) (hδ : 0 < δ) : StoppingRule 𝓕 T :=
  (θ.toGridIndexRule hδ).toPhysicalRule hδ

theorem StoppingRule.roundUp_time (θ : StoppingRule 𝓕 T) (hδ : 0 < δ) (ω : Ω) :
    (θ.roundUp hδ).time ω = min ((gridIndex θ δ ω : ℝ≥0)*δ) T := rfl

theorem StoppingRule.le_roundUp (θ : StoppingRule 𝓕 T) (hδ : 0 < δ) (ω : Ω) :
    θ.time ω ≤ (θ.roundUp hδ).time ω :=
  le_min ((div_le_iff₀ hδ).mp (Nat.le_ceil (θ.time ω/δ))) (θ.le_horizon ω)

theorem StoppingRule.roundUp_mem_grid (θ : StoppingRule 𝓕 T) (hδ : 0 < δ) (ω : Ω) :
    (θ.roundUp hδ).time ω ∈ exerciseGrid T δ :=
  ((θ.toGridIndexRule hδ).toPhysicalRule_mem_grid hδ) ω

theorem StoppingRule.roundUp_time_tendsto (θ : StoppingRule 𝓕 T) (ω : Ω) :
    Tendsto (fun n => (θ.roundUp (gridStep_pos n)).time ω) atTop (𝓝 (θ.time ω)) := by
  have hh := (gridValue_time_tendsto θ ω).min (tendsto_const_nhds (x := T))
  simpa only [StoppingRule.roundUp_time,min_eq_left (θ.le_horizon ω)] using hh

theorem expectedReward_roundUp_tendsto {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    {K r q σ S : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (θ : StoppingRule 𝓕 T) :
    Tendsto (fun n => ∫ ω, putReward W K r q σ S (θ.roundUp (gridStep_pos n)).time ω ∂P)
      atTop (𝓝 (∫ ω, putReward W K r q σ S θ.time ω ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => K)
  · intro n
    exact (putReward_measurable hW K r q σ S
        (θ.roundUp (gridStep_pos n)).measurable_time).aestronglyMeasurable
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
