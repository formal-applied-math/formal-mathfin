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

Public entry points include `cappedGridFiltration`, `rounded_grid_time_eq`, `GridRule.toDiscreteRule`, `GridRule.toDiscreteRule_time`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The continuous filtration sampled at the capped grid times `min (i*δ) T`. -/
def cappedGridFiltration (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T δ : ℝ≥0) :
    Filtration ℕ ‹MeasurableSpace Ω› where
  seq := fun i => 𝓕 (min ((i : ℝ≥0)*δ) T)
  mono' := fun _ _ hij => 𝓕.mono (min_le_min
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) zero_le) le_rfl)
  le' := fun _ => 𝓕.le _

theorem rounded_grid_time_eq {T δ t : ℝ≥0} (hδ : 0 < δ) (ht : t ∈ exerciseGrid T δ) :
    min ((⌈t/δ⌉₊ : ℝ≥0)*δ) T = t := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
  by_cases hj : (j : ℝ≥0)*δ ≤ T
  · simp [min_eq_left hj,hδ.ne']
  · have hT : T ≤ (⌈T/δ⌉₊ : ℝ≥0)*δ := (div_le_iff₀ hδ).mp (Nat.le_ceil (T/δ))
    simp only [min_eq_right (le_of_not_ge hj),min_eq_right hT]

variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T δ : ℝ≥0}

/-- A grid-valued rule read as a rule for `cappedGridFiltration`, indexed by `gridIndex θ.val δ`
and bounded by `⌈T/δ⌉₊`. -/
noncomputable def GridRule.toDiscreteRule (θ : GridRule 𝓕 T δ) (hδ : 0 < δ) :
    DiscreteRule (cappedGridFiltration 𝓕 T δ) ⌈T/δ⌉₊ where
  time := gridIndex θ.val δ
  stopping := by
    intro i
    have hs := θ.val.stopping (min ((i : ℝ≥0)*δ) T)
    convert! hs using 1
    ext ω
    simp only [WithTop.coe_le_coe,le_min_iff,
      θ.val.le_horizon ω,and_true,mem_ofPred_eq]
    convert! (gridIndex_le_iff θ.val hδ ω i) using 1
    simp
  le_horizon := gridIndex_bounded θ.val

theorem GridRule.toDiscreteRule_time (θ : GridRule 𝓕 T δ) (hδ : 0 < δ) (ω : Ω) :
    min (((θ.toDiscreteRule hδ).time ω : ℝ≥0)*δ) T = θ.val.time ω :=
  rounded_grid_time_eq hδ (θ.property ω)

/-- A rule for `cappedGridFiltration` read back in physical time, stopping at the capped grid
time `min (η.time ω*δ) T`. -/
noncomputable def DiscreteRule.toPhysicalBoundedRule
    (η : DiscreteRule (cappedGridFiltration 𝓕 T δ) ⌈T/δ⌉₊) (hδ : 0 < δ) : BoundedRule 𝓕 T where
  time := fun ω => min ((η.time ω : ℝ≥0)*δ) T
  stopping := by
    intro t
    by_cases hT : T ≤ t
    · have he : {ω | ((min ((η.time ω : ℝ≥0)*δ) T : ℝ≥0) : WithTop ℝ≥0) ≤ t} = univ := by
        ext ω
        simp only [mem_ofPred_eq,WithTop.coe_le_coe,mem_univ,iff_true]
        exact (min_le_right _ _).trans hT
      rw [he]
      exact MeasurableSet.univ
    · have hfloor : (⌊t/δ⌋₊ : ℝ≥0)*δ ≤ t :=
        (le_div_iff₀ hδ).mp (Nat.floor_le (show (0 : ℝ≥0) ≤ t/δ from bot_le))
      have hm : MeasurableSet[𝓕 t] {ω | (η.time ω : WithTop ℕ) ≤ (⌊t/δ⌋₊ : WithTop ℕ)} :=
        𝓕.mono ((min_le_left _ _).trans hfloor) _ (η.stopping ⌊t/δ⌋₊)
      convert! hm using 1
      ext ω
      simp only [mem_ofPred_eq,WithTop.coe_le_coe,min_le_iff,hT,or_false]
      rw [← le_div_iff₀ hδ,← Nat.le_floor_iff (show (0 : ℝ≥0) ≤ t/δ from bot_le)]
      constructor <;> intro hh <;> exact_mod_cast hh
  le_horizon := fun _ => min_le_right _ _

/-- `DiscreteRule.toPhysicalBoundedRule` together with the proof that its times lie in
`exerciseGrid T δ`. -/
noncomputable def DiscreteRule.toPhysicalGridRule
    (η : DiscreteRule (cappedGridFiltration 𝓕 T δ) ⌈T/δ⌉₊) (hδ : 0 < δ) : GridRule 𝓕 T δ := by
  refine ⟨η.toPhysicalBoundedRule hδ,?_⟩
  intro ω
  apply Finset.mem_image.mpr
  exact ⟨η.time ω,Finset.mem_range.mpr (Nat.lt_succ_of_le (η.le_horizon ω)),rfl⟩

/-- The put reward collected at the deterministic capped grid time `min (i*δ) T`. -/
noncomputable def gridReward (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T δ : ℝ≥0)
    (i : ℕ) : Ω → ℝ :=
  putReward W K r q σ S (fun _ => min ((i : ℝ≥0)*δ) T)

theorem gridValue_eq_discreteValue (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (K r q σ S : ℝ) (hδ : 0 < δ) :
    gridAmericanPutValue P 𝓕 W K r q σ S T δ =
      discreteStoppingValue P (cappedGridFiltration 𝓕 T δ) (gridReward W K r q σ S T δ) ⌈T/δ⌉₊ := by
  unfold gridAmericanPutValue discreteStoppingValue
  congr 1
  ext v
  constructor
  · rintro ⟨θ,rfl⟩
    refine ⟨θ.toDiscreteRule hδ,?_⟩
    apply integral_congr_ae
    apply Eventually.of_forall
    intro ω
    unfold gridReward putReward
    dsimp only
    simp only [θ.toDiscreteRule_time hδ ω]
  · rintro ⟨η,rfl⟩
    exact ⟨η.toPhysicalGridRule hδ,rfl⟩

end MathFin.BlackScholes.AmericanPut.Stopping
