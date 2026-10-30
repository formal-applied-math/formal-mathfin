/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.GridReindexing
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualContact

/-! # Bellman identification and attained optimality on physical exercise grids 
## Result

Public entry points include `gridReward_adapted`, `gridReward_integrable`, `optimalGridRule`,
`gridValue_eq_bellman`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {W : ℝ≥0 → Ω → ℝ}

theorem gridReward_adapted (ha : Adapted 𝓕 W) (K r q σ S : ℝ) (T δ : ℝ≥0) :
    Adapted (cappedGridFiltration 𝓕 T δ) (gridReward W K r q σ S T δ) := by
  intro i
  have hw := ha (min ((i : ℝ≥0)*δ) T)
  unfold gridReward putRewardAt putReward MathFin.gbmValue
  dsimp only
  fun_prop

theorem gridReward_integrable {P : Measure Ω} [IsProbabilityMeasure P]
    (hW : Measurable W.uncurry) {K r q σ S : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (T δ : ℝ≥0) (i : ℕ) :
    Integrable (gridReward W K r q σ S T δ i) P :=
  putReward_integrable hW P hK hr hS measurable_const

/-- The Bellman first-contact rule for the grid rewards, carried back to physical grid times. -/
noncomputable def optimalGridRule (P : Measure Ω) (ha : Adapted 𝓕 W)
    (K r q σ S : ℝ) (T : ℝ≥0) {δ : ℝ≥0} (hδ : 0 < δ) : StoppingRule 𝓕 T :=
  (finiteBellmanRule (P := P) (gridReward_adapted ha K r q σ S T δ) ⌈T/δ⌉₊).toPhysicalRule hδ

theorem optimalGridRule_mem_grid (P : Measure Ω) (ha : Adapted 𝓕 W) (K r q σ S : ℝ) (T : ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) :
    optimalGridRule P ha K r q σ S T hδ ∈ StoppingRule.valuedIn 𝓕 T (exerciseGrid T δ) :=
  StoppingRule.toPhysicalRule_mem_grid _ hδ

variable {P : Measure Ω} [IsProbabilityMeasure P] {K r q σ S : ℝ} {T δ : ℝ≥0}

theorem gridValue_eq_bellman (hW : Measurable W.uncurry) (ha : Adapted 𝓕 W)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (hδ : 0 < δ) :
    gridAmericanPutValue P 𝓕 W K r q σ S T δ =
      ∫ ω, finiteBellman P (cappedGridFiltration 𝓕 T δ)
        (gridReward W K r q σ S T δ) ⌈T/δ⌉₊ 0 ω ∂P := by
  rw [gridValue_eq_discreteValue P W K r q σ S hδ]
  exact stoppingValue_eq_bellman (gridReward_adapted ha K r q σ S T δ)
    (gridReward_integrable hW hK hr hS T δ) _

theorem optimalGridRule_attains_value (hW : Measurable W.uncurry) (ha : Adapted 𝓕 W)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (hδ : 0 < δ) :
    (∫ ω, putReward W K r q σ S (optimalGridRule P ha K r q σ S T hδ).time ω ∂P) =
      gridAmericanPutValue P 𝓕 W K r q σ S T δ := by
  rw [gridValue_eq_discreteValue P W K r q σ S hδ]
  have he := finiteBellmanRule_attains_value (P := P) (gridReward_adapted ha K r q σ S T δ)
    (gridReward_integrable hW hK hr hS T δ) ⌈T/δ⌉₊
  convert! he using 1

theorem optimalGridRule_payoffs_tendsto (hW : Measurable W.uncurry) (ha : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    Tendsto (fun n => ∫ ω, putReward W K r q σ S
      (optimalGridRule P ha K r q σ S T (gridStep_pos n)).time ω ∂P)
      atTop (𝓝 (americanPutValue P 𝓕 W K r q σ S T)) := by
  have he : (fun n => ∫ ω, putReward W K r q σ S
      (optimalGridRule P ha K r q σ S T (gridStep_pos n)).time ω ∂P) =
      (fun n => gridAmericanPutValue P 𝓕 W K r q σ S T (gridStep n)) :=
    funext (fun n => optimalGridRule_attains_value hW ha hK hr hS (gridStep_pos n))
  rw [he]
  exact gridValue_tendsto_americanValue hW hpaths hK hr hS

/-- The optimal grid rule of the canonical model (strike `1`, rates `k` and `h`, volatility
`Real.sqrt 2`, spot `Real.exp x`, horizon `t.toNNReal`) at grid step `gridStep n`. -/
noncomputable def canonicalOptimalGridRule (k h x t : ℝ) (n : ℕ) :
    @StoppingRule (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit) ℝ≥0 _
      brownianUsualFiltration t.toNNReal :=
  @optimalGridRule (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit)
      brownianUsualFiltration brownian
    (completedMeasure gaussianLimit) brownianUsual_adapted 1 k h (Real.sqrt 2) (Real.exp x)
    t.toNNReal (gridStep n) (gridStep_pos n)

/-- The exercise time of the canonical optimal grid rule. -/
noncomputable def canonicalOptimalGridTime (k h x t : ℝ) (n : ℕ) : (ℝ≥0 → ℝ) → ℝ≥0 :=
  @StoppingRule.time (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit) ℝ≥0 _
    brownianUsualFiltration
    t.toNNReal (canonicalOptimalGridRule k h x t n)

theorem canonicalOptimalGridRule_payoffs_tendsto {k h : ℝ} (hk : 0 ≤ k) (x t : ℝ) :
    Tendsto (fun n => ∫ ω, putReward brownian 1 k h (Real.sqrt 2) (Real.exp x)
      (canonicalOptimalGridTime k h x t n) ω ∂completedMeasure gaussianLimit)
      atTop (𝓝 (canonicalPrice k h x t)) := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  have hh := optimalGridRule_payoffs_tendsto (P := μ) (𝓕 := brownianUsualFiltration)
    (K := 1) (r := k) (q := h) (σ := Real.sqrt 2) (S := Real.exp x) (T := t.toNNReal)
    brownian_completed_measurable brownianUsual_adapted continuous_brownian
    (by norm_num) hk (Real.exp_pos x).le
  convert! hh using 1

end MathFin.BlackScholes.AmericanPut.Stopping
