/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FiniteExerciseGrid
public import MathFin.BlackScholes.AmericanPut.Stopping.CanonicalPrice

/-! # Finite exercise-grid values converge to the actual American supremum

Only exercise opportunities are discretized; the underlying stochastic process
and filtration are unchanged. No optimal-rule or dynamic-programming premise
is needed for this approximation theorem.

## Result

Public entry points include `GridRule`, `GridRule.zero`, `GridRule.maturity`,
`BoundedRule.toGridRule`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded rule for `𝓕` whose exercise time always lands in the finite grid
`exerciseGrid T δ`. -/
def GridRule (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T δ : ℝ≥0) :=
  {θ : BoundedRule 𝓕 T // ∀ ω, θ.time ω ∈ exerciseGrid T δ}

/-- The grid rule that exercises immediately at time `0`. -/
def GridRule.zero (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T δ : ℝ≥0) : GridRule 𝓕 T δ :=
  ⟨BoundedRule.zero 𝓕 T,fun _ => zero_mem_exerciseGrid T δ⟩

/-- The grid rule that always waits until maturity `T`, which is a grid time once `0 < δ`. -/
def GridRule.maturity (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) : GridRule 𝓕 T δ :=
  ⟨BoundedRule.constant 𝓕 T T le_rfl,fun _ => maturity_mem_exerciseGrid T hδ⟩

instance gridRule_nonempty (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T δ : ℝ≥0) :
    Nonempty (GridRule 𝓕 T δ) := ⟨GridRule.zero 𝓕 T δ⟩

/-- The grid rule obtained from `θ` by rounding its exercise time up to the next grid time
(`BoundedRule.roundUp`). -/
noncomputable def BoundedRule.toGridRule {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {T δ : ℝ≥0} (θ : BoundedRule 𝓕 T) (hδ : 0 < δ) : GridRule 𝓕 T δ :=
  ⟨θ.roundUp hδ,θ.roundUp_mem_grid hδ⟩

/-- The supremum of the expected discounted put reward over rules that exercise only on the
grid `exerciseGrid T δ`. -/
noncomputable def gridAmericanPutValue (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T δ : ℝ≥0) : ℝ :=
  sSup (range (fun θ : GridRule 𝓕 T δ => ∫ ω, putReward W K r q σ S θ.val.time ω ∂P))

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
  {K r q σ S : ℝ} {T δ : ℝ≥0}

theorem gridValue_le_value (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    gridAmericanPutValue P 𝓕 W K r q σ S T δ ≤ americanPutValue P 𝓕 W K r q σ S T := by
  apply csSup_le (range_nonempty _)
  rintro _ ⟨θ,rfl⟩
  exact expectedReward_le_value hW hK hr hS θ.val

theorem expectedReward_le_gridValue (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (θ : GridRule 𝓕 T δ) :
    (∫ ω, putReward W K r q σ S θ.val.time ω ∂P) ≤ gridAmericanPutValue P 𝓕 W K r q σ S T δ := by
  unfold gridAmericanPutValue
  apply le_csSup
  · refine ⟨K,?_⟩
    rintro _ ⟨η,rfl⟩
    exact expectedReward_le_strike hW hK hr hS η.val
  · exact ⟨θ,rfl⟩

theorem gridValue_nonneg (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    0 ≤ gridAmericanPutValue P 𝓕 W K r q σ S T δ :=
  (integral_nonneg (putReward_nonneg W K r q σ S _)).trans
    (expectedReward_le_gridValue hW hK hr hS (GridRule.zero 𝓕 T δ))

theorem payoff_le_gridValue (hW : Measurable W.uncurry)
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    max (K-S) 0 ≤ gridAmericanPutValue P 𝓕 W K r q σ S T δ := by
  rw [← expectedReward_zero (𝓕 := 𝓕) (T := T) hzero]
  exact expectedReward_le_gridValue hW hK hr hS (GridRule.zero 𝓕 T δ)

theorem european_expectation_le_gridValue (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (hδ : 0 < δ) :
    (∫ ω, putReward W K r q σ S (fun _ => T) ω ∂P) ≤ gridAmericanPutValue P 𝓕 W K r q σ S T δ :=
  expectedReward_le_gridValue hW hK hr hS (GridRule.maturity 𝓕 T hδ)

theorem gridValue_tendsto_americanValue (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    Tendsto (fun n => gridAmericanPutValue P 𝓕 W K r q σ S T (gridStep n)) atTop
      (𝓝 (americanPutValue P 𝓕 W K r q σ S T)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨_,⟨θ,rfl⟩,hθ⟩ := exists_lt_of_lt_csSup
      (exerciseValues_nonempty (P := P) (𝓕 := 𝓕) (W := W) (K := K) (r := r)
        (q := q) (σ := σ) (S := S) (T := T)) ha
    have he := expectedReward_roundUp_tendsto (P := P) (q := q) (σ := σ) hW hpaths hK hr hS θ
    filter_upwards [he.eventually (Ioi_mem_nhds hθ)] with n hn
    exact hn.trans_le (expectedReward_le_gridValue hW hK hr hS (θ.toGridRule (gridStep_pos n)))
  · intro a ha
    exact Eventually.of_forall (fun _ => (gridValue_le_value hW hK hr hS).trans_lt ha)

/-- The limiting value is also the supremum of these genuine finite-grid values.
The sequence need not be monotone, since meshes `1/(n+1)` are not nested. -/
theorem americanValue_eq_sup_gridValues (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    americanPutValue P 𝓕 W K r q σ S T =
      sSup (range (fun n => gridAmericanPutValue P 𝓕 W K r q σ S T (gridStep n))) := by
  have hb : BddAbove (range (fun n => gridAmericanPutValue P 𝓕 W K r q σ S T (gridStep n))) := by
    refine ⟨americanPutValue P 𝓕 W K r q σ S T,?_⟩
    rintro _ ⟨n,rfl⟩
    exact gridValue_le_value hW hK hr hS
  apply le_antisymm
  · exact le_of_tendsto (gridValue_tendsto_americanValue hW hpaths hK hr hS)
      (Eventually.of_forall (fun n => le_csSup hb ⟨n,rfl⟩))
  · apply csSup_le (range_nonempty _)
    rintro _ ⟨n,rfl⟩
    exact gridValue_le_value hW hK hr hS

/-- The finite-grid counterpart of `canonicalPrice`: `gridAmericanPutValue` on the completed
usual Brownian filtration at strike `1`, rate `k`, dividend `h`, volatility `Real.sqrt 2`,
spot `Real.exp x`, horizon `t.toNNReal` and mesh `gridStep n`. -/
noncomputable def canonicalGridPrice (k h x t : ℝ) (n : ℕ) : ℝ :=
  @gridAmericanPutValue (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit)
    (completedMeasure gaussianLimit) brownianUsualFiltration brownian
    1 k h (Real.sqrt 2) (Real.exp x) t.toNNReal (gridStep n)

theorem canonicalGridPrice_tendsto {k h : ℝ} (hk : 0 ≤ k) (x t : ℝ) :
    Tendsto (canonicalGridPrice k h x t) atTop (𝓝 (canonicalPrice k h x t)) := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact gridValue_tendsto_americanValue (P := μ) (𝓕 := brownianUsualFiltration)
    brownian_completed_measurable continuous_brownian (by norm_num) hk (Real.exp_pos x).le

end MathFin.BlackScholes.AmericanPut.Stopping
