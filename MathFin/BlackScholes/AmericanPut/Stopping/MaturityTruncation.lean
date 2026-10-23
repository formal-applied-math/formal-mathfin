/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.AmericanValue
public import MathFin.BlackScholes.AmericanPut.Stopping.LocalizationTimes

/-! # Stability of stopping rewards under small maturity changes 
## Result

Public entry points include `BoundedRule.truncate`, `continuous_reward_truncation`,
`putReward_time_continuous`, `expectedReward_truncate_tendsto`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The rule `θ` capped at the new horizon `U`, stopping at `min (θ.time ω) U`. -/
def BoundedRule.truncate {T : ℝ≥0} (θ : BoundedRule 𝓕 T) (U : ℝ≥0) : BoundedRule 𝓕 U where
  time := fun ω => min (θ.time ω) U
  stopping := by
    convert! θ.stopping.min (isStoppingTime_const 𝓕 U) using 1
  le_horizon := fun _ => min_le_right _ _

theorem continuous_reward_truncation {f : ℝ≥0 → ℝ} (hf : Continuous f)
    {T : ℝ≥0} {Tn s : ℕ → ℝ≥0} (hT : Tendsto Tn atTop (𝓝 T)) (hs : ∀ n, s n ≤ Tn n) :
    Tendsto (fun n => f (s n)-f (min (s n) T)) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := T)) ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hT δ hδ
  refine ⟨N,fun n hn => ?_⟩
  by_cases hnT : s n ≤ T
  · simpa [min_eq_left hnT] using hε
  · have hTs : T ≤ s n := le_of_not_ge hnT
    have hTTn := hTs.trans (hs n)
    have hd : dist (s n) T < δ := by
      rw [NNReal.dist_eq,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hTs))]
      have hh := hN n hn
      rw [NNReal.dist_eq,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hTTn))] at hh
      have hh' : (s n : ℝ) ≤ (Tn n : ℝ) := by exact_mod_cast hs n
      linarith
    have hh := hfδ hd
    simpa [min_eq_right hTs,Real.dist_eq,Real.norm_eq_abs,abs_abs] using hh

omit [MeasurableSpace Ω] in
theorem putReward_time_continuous {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ ω, Continuous (fun t => W t ω)) (K r q σ S : ℝ) (ω : Ω) :
    Continuous (fun t => putReward W K r q σ S (fun _ => t) ω) := by
  unfold putReward MathFin.gbmValue
  fun_prop

theorem expectedReward_truncate_tendsto {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    {K r q σ S : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S)
    {T : ℝ≥0} {Tn : ℕ → ℝ≥0} (hT : Tendsto Tn atTop (𝓝 T))
    (θ : ∀ n, BoundedRule 𝓕 (Tn n)) :
    Tendsto (fun n => (∫ ω, putReward W K r q σ S (θ n).time ω ∂P) -
      ∫ ω, putReward W K r q σ S ((θ n).truncate T).time ω ∂P) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => ∫ ω,
      (putReward W K r q σ S (θ n).time ω-putReward W K r q σ S ((θ n).truncate T).time ω) ∂P)
      atTop (𝓝 (∫ _ : Ω, (0 : ℝ) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 2*K)
    · intro n
      exact ((putReward_measurable hW K r q σ S (θ n).measurable_time).sub
        (putReward_measurable hW K r q σ S ((θ n).truncate T).measurable_time)).aestronglyMeasurable
    · exact integrable_const (2*K)
    · intro n
      apply Eventually.of_forall
      intro ω
      rw [Real.norm_eq_abs,abs_le]
      have h0 := putReward_nonneg W K r q σ S (θ n).time ω
      have h1 := putReward_nonneg W K r q σ S ((θ n).truncate T).time ω
      have h2 := putReward_le_strike (q := q) (σ := σ) W hK hr hS (θ n).time ω
      have h3 := putReward_le_strike (q := q) (σ := σ) W hK hr hS ((θ n).truncate T).time ω
      constructor <;> linarith
    · exact Eventually.of_forall (fun ω => continuous_reward_truncation
        (putReward_time_continuous hpaths K r q σ S ω) hT (fun n => (θ n).le_horizon ω))
  simpa only [integral_sub (putReward_integrable hW P hK hr hS (θ _).measurable_time)
    (putReward_integrable hW P hK hr hS ((θ _).truncate T).measurable_time),integral_zero] using
        hlim

theorem expectedReward_fixed_truncate_tendsto {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    {K r q σ S : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S)
    {T : ℝ≥0} {Tn : ℕ → ℝ≥0} (hT : Tendsto Tn atTop (𝓝 T)) (θ : BoundedRule 𝓕 T) :
    Tendsto (fun n => ∫ ω, putReward W K r q σ S (θ.truncate (Tn n)).time ω ∂P) atTop
      (𝓝 (∫ ω, putReward W K r q σ S θ.time ω ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => K)
  · intro n
    exact (putReward_measurable hW K r q σ S
        (θ.truncate (Tn n)).measurable_time).aestronglyMeasurable
  · exact integrable_const K
  · intro n
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_of_nonneg (putReward_nonneg W K r q σ S _ ω)]
    exact putReward_le_strike W hK hr hS _ ω
  · apply Eventually.of_forall
    intro ω
    have ht : Tendsto (fun n => min (θ.time ω) (Tn n)) atTop (𝓝 (θ.time ω)) := by
      simpa only [min_eq_left (θ.le_horizon ω)] using
        (tendsto_const_nhds (x := θ.time ω)).min hT
    exact ((putReward_time_continuous hpaths K r q σ S ω).tendsto (θ.time ω)).comp ht

end MathFin.BlackScholes.AmericanPut.Stopping
