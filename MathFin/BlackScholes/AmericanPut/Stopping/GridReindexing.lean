/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.BermudanConvergence
public import MathFin.BlackScholes.AmericanPut.Stopping.DiscreteStoppingValue
public import MathFin.BlackScholes.AmericanPut.Stopping.SampledRules

/-! # Reindexing capped physical-time exercise grids

Both conversions preserve the original filtration's information at the actual
exercise time. The possibly shorter last interval and maturity zero are included.

## Result

Public entry points include `cappedGridFiltration`, `rounded_grid_time_eq`,
`StoppingRule.toGridIndexRule`, `StoppingRule.toPhysicalRule`, `gridValue_eq_discreteValue`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `i`-th grid time `i*δ`, capped at the horizon `T`. -/
def cappedGridTime (T δ : ℝ≥0) (i : ℕ) : ℝ≥0 := min ((i : ℝ≥0)*δ) T

theorem cappedGridTime_mono (T δ : ℝ≥0) : Monotone (cappedGridTime T δ) := by
  intro i j hij
  exact min_le_min (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) zero_le) le_rfl

/-- The continuous filtration sampled at the capped grid times `min (i*δ) T`: the sampled
filtration `ContinuousMarket.sampledFiltration` along `cappedGridTime T δ`. -/
def cappedGridFiltration (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T δ : ℝ≥0) :
    Filtration ℕ ‹MeasurableSpace Ω› :=
  ContinuousMarket.sampledFiltration 𝓕 (cappedGridTime_mono T δ)

theorem rounded_grid_time_eq {T δ t : ℝ≥0} (hδ : 0 < δ) (ht : t ∈ exerciseGrid T δ) :
    min ((⌈t/δ⌉₊ : ℝ≥0)*δ) T = t := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
  by_cases hj : (j : ℝ≥0)*δ ≤ T
  · simp [min_eq_left hj,hδ.ne']
  · have hT : T ≤ (⌈T/δ⌉₊ : ℝ≥0)*δ := (div_le_iff₀ hδ).mp (Nat.le_ceil (T/δ))
    simp only [min_eq_right (le_of_not_ge hj),min_eq_right hT]

variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T δ : ℝ≥0}

/-- A grid-valued rule read as a rule for `cappedGridFiltration`, indexed by `gridIndex θ δ`
and bounded by `⌈T/δ⌉₊`. -/
noncomputable def StoppingRule.toGridIndexRule (θ : StoppingRule 𝓕 T) (hδ : 0 < δ) :
    StoppingRule (cappedGridFiltration 𝓕 T δ) ⌈T/δ⌉₊ where
  time := gridIndex θ δ
  stopping := by
    intro i
    have hs := θ.stopping (min ((i : ℝ≥0)*δ) T)
    convert! hs using 1
    ext ω
    simp only [WithTop.coe_le_coe,le_min_iff,
      θ.le_horizon ω,and_true,mem_ofPred_eq]
    convert! (gridIndex_le_iff θ hδ ω i) using 1
  le_horizon := gridIndex_bounded θ

theorem StoppingRule.toGridIndexRule_time (θ : StoppingRule 𝓕 T)
    (hθ : θ ∈ StoppingRule.valuedIn 𝓕 T (exerciseGrid T δ)) (hδ : 0 < δ) (ω : Ω) :
    cappedGridTime T δ ((θ.toGridIndexRule hδ).time ω) = θ.time ω :=
  rounded_grid_time_eq hδ (hθ ω)

theorem cappedGridTime_ceil (T : ℝ≥0) (hδ : 0 < δ) : cappedGridTime T δ ⌈T/δ⌉₊ = T :=
  min_eq_right ((div_le_iff₀ hδ).mp (Nat.le_ceil (T/δ)))

/-- A rule for `cappedGridFiltration` read back in physical time, stopping at the capped grid
time `cappedGridTime T δ (η.time ω)`: `StoppingRule.toSampledRule` along the capped grid, which
ends at the horizon `T`. -/
noncomputable def StoppingRule.toPhysicalRule
    (η : StoppingRule (cappedGridFiltration 𝓕 T δ) ⌈T / δ⌉₊) (hδ : 0 < δ) : StoppingRule 𝓕 T :=
  η.toSampledRule.extend (cappedGridTime_ceil T hδ).le

theorem StoppingRule.toPhysicalRule_mem_grid
    (η : StoppingRule (cappedGridFiltration 𝓕 T δ) ⌈T / δ⌉₊) (hδ : 0 < δ) :
    η.toPhysicalRule hδ ∈ StoppingRule.valuedIn 𝓕 T (exerciseGrid T δ) := by
  intro ω
  apply Finset.mem_image.mpr
  exact ⟨η.time ω,Finset.mem_range.mpr (Nat.lt_succ_of_le (η.le_horizon ω)),rfl⟩

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
