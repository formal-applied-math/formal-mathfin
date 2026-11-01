/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.UsualGridMarkov

/-! # Convergence along any positive shrinking exercise mesh

Time rescaling changes the mesh `1/(n+1)` to a constant multiple of it.
Upward rounding and bounded convergence work for every positive mesh tending
to zero, with no nesting assumption and no classical pricing contract.

## Result

Public entry points include `StoppingRule.roundUp_time_tendsto_of_mesh`,
`expectedReward_roundUp_tendsto_of_mesh`, `gridValue_tendsto_americanValue_of_mesh`,
`brownianGridPrice_tendsto_usual_of_mesh`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {T : ℝ≥0} {δ : ℕ → ℝ≥0}

theorem StoppingRule.roundUp_time_tendsto_of_mesh (θ : StoppingRule 𝓕 T)
    (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) (ω : Ω) :
    Tendsto (fun n => (θ.roundUp (hδ n)).time ω) atTop (𝓝 (θ.time ω)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n => θ.time ω+δ n) atTop (𝓝 (θ.time ω)) by
      simpa only [add_zero] using tendsto_const_nhds.add hlim)
    (fun n => θ.le_roundUp (hδ n) ω)
  intro n
  have hceil := mul_le_mul_of_nonneg_right
    (Nat.ceil_lt_add_one (show (0 : ℝ≥0) ≤ θ.time ω/δ n from zero_le)).le
    (show (0 : ℝ≥0) ≤ δ n from zero_le)
  rw [add_mul,div_mul_cancel₀ _ (hδ n).ne',one_mul] at hceil
  exact (min_le_left _ _).trans hceil

theorem expectedReward_roundUp_tendsto_of_mesh {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    {K r q σ S : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S)
    (θ : StoppingRule 𝓕 T) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, putReward W K r q σ S (θ.roundUp (hδ n)).time ω ∂P) atTop
      (𝓝 (∫ ω, putReward W K r q σ S θ.time ω ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => K)
  · intro n
    exact (putReward_measurable hW K r q σ S
        (θ.roundUp (hδ n)).measurable_time).aestronglyMeasurable
  · exact integrable_const K
  · intro n
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_of_nonneg (putReward_nonneg W K r q σ S _ ω)]
    exact putReward_le_strike W hK hr hS _ ω
  · exact Eventually.of_forall (fun ω =>
      ((putReward_time_continuous hpaths K r q σ S ω).tendsto (θ.time ω)).comp
        (θ.roundUp_time_tendsto_of_mesh hδ hlim ω))

theorem gridValue_tendsto_americanValue_of_mesh {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    {K r q σ S : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S)
    (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => gridAmericanPutValue P 𝓕 W K r q σ S T (δ n)) atTop
      (𝓝 (americanPutValue P 𝓕 W K r q σ S T)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨θ,-,hθ⟩ := exists_lt_of_lt_stoppingValue ha univ_nonempty
    have he := expectedReward_roundUp_tendsto_of_mesh (P := P) (q := q) (σ := σ)
      hW hpaths hK hr hS θ hδ hlim
    filter_upwards [he.eventually (Ioi_mem_nhds hθ)] with n hn
    exact hn.trans_le (expectedReward_le_gridValue hW hK hr hS (θ.roundUp (hδ n))
      (θ.roundUp_mem_grid (hδ n)))
  · intro a ha
    exact Eventually.of_forall (fun _ => (gridValue_le_value hW hK hr hS).trans_lt ha)

theorem brownianGridPrice_tendsto_usual_of_mesh {K r q σ : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (T : ℝ≥0) (x : ℝ)
    (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => brownianGridPrice K r q σ T (δ n) x) atTop
      (𝓝 (brownianUsualAmericanPut K r q σ (Real.exp x) T)) := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  have he : (fun n => brownianGridPrice K r q σ T (δ n) x) =
      fun n => gridAmericanPutValue μ brownianUsualFiltration brownian
        K r q σ (Real.exp x) T (δ n) :=
    funext (fun n => brownianGridPrice_eq_usualGridValue hK hr T (hδ n) x)
  rw [he]
  exact gridValue_tendsto_americanValue_of_mesh brownian_completed_measurable continuous_brownian
    hK hr (Real.exp_pos x).le hδ hlim

theorem gridStep_tendsto_zero : Tendsto gridStep atTop (𝓝 0) := by
  apply NNReal.tendsto_coe.mp
  simpa only [gridStep,NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,
    NNReal.coe_zero,Function.comp_def] using
    (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))

end MathFin.BlackScholes.AmericanPut.Stopping
