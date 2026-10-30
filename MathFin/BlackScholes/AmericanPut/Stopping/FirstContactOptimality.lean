/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.OrderedSampling
public import MathFin.BlackScholes.AmericanPut.Stopping.VanishingGap

/-! # Optimal first contact from a bounded supermartingale and nearly optimal rules

The initial expected supermartingale value is approached by admissible rewards.
This forces their expected nonnegative gaps to zero. A subsequence and continuity
then recover the expected value at first contact by ordered optional sampling.

## Result

Public entry points include `expected_firstContact_eq_initial`,
`firstContact_expectedReward_eq_initial`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {U Z : ℝ≥0 → Ω → ℝ} {C D : ℝ} {T : ℝ≥0}

theorem expected_firstContact_eq_initial
    (hU : Supermartingale U 𝓕 P) (hUc : ∀ ω, Continuous (fun t => U t ω))
    (hUb : ∀ t ω, ‖U t ω‖ ≤ C) (hZm : Measurable Z.uncurry)
    (hZc : ∀ ω, Continuous (fun t => Z t ω)) (hZb : ∀ t ω, ‖Z t ω‖ ≤ D)
    (hdom : ∀ t, t ≤ T → ∀ ω, Z t ω ≤ U t ω)
    (τ : StoppingRule 𝓕 T) (hbefore : ∀ ω t, t < τ.time ω → Z t ω < U t ω)
    (θ : ℕ → StoppingRule 𝓕 T)
    (happrox : Tendsto (fun n => ∫ ω, Z ((θ n).time ω) ω ∂P) atTop (𝓝 (∫ ω, U 0 ω ∂P))) :
    (∫ ω, U (τ.time ω) ω ∂P) = ∫ ω, U 0 ω ∂P := by
  have hUi (η : StoppingRule 𝓕 T) : Integrable (fun ω => U (η.time ω) ω) P :=
    candidate_stopped_integrable hU hUc hUb η
  have hZi (η : StoppingRule 𝓕 T) : Integrable (fun ω => Z (η.time ω) ω) P :=
    (integrable_const D).mono'
        (hZm.comp (η.measurable_time.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hZb _ ω))
  let G : ℕ → Ω → ℝ := fun n ω => U ((θ n).time ω) ω-Z ((θ n).time ω) ω
  have hGi (n : ℕ) : Integrable (G n) P := (hUi (θ n)).sub (hZi (θ n))
  have hG0 (n : ℕ) (ω : Ω) : 0 ≤ G n ω := sub_nonneg.mpr (hdom _ ((θ n).le_horizon ω) ω)
  have hupper (n : ℕ) : (∫ ω, G n ω ∂P) ≤ (∫ ω, U 0 ω ∂P)-(∫ ω, Z ((θ n).time ω) ω ∂P) := by
    change (∫ ω, U ((θ n).time ω) ω-Z ((θ n).time ω) ω ∂P) ≤ _
    rw [integral_sub (hUi (θ n)) (hZi (θ n))]
    exact sub_le_sub_right (expected_stoppedValue_le_initial hU hUc hUb (θ n)) _
  have hGe : Tendsto (fun n => ∫ ω, G n ω ∂P) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg (hG0 n)) hupper
    simpa only [sub_self] using (tendsto_const_nhds (x := ∫ ω, U 0 ω ∂P)).sub happrox
  obtain ⟨ns,hns,hgap⟩ := exists_subseq_gap_tendsto_zero hGi hG0 hGe
  let η : ℕ → StoppingRule 𝓕 T := fun n => (θ (ns n)).minimum τ
  have htime : ∀ᵐ ω ∂P, Tendsto (fun n => (η n).time ω) atTop (𝓝 (τ.time ω)) := by
    filter_upwards [hgap] with ω hω
    exact min_time_tendsto_firstContact ((hUc ω).sub (hZc ω))
      (fun t ht => sub_pos.mpr (hbefore ω t ht)) hω
  have hlim := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => C)
    (F := fun n ω => U ((η n).time ω) ω) (f := fun ω => U (τ.time ω) ω)
    (fun n => (hUi (η n)).aestronglyMeasurable) (integrable_const C)
    (fun _ => Eventually.of_forall (fun ω => hUb _ ω))
    (htime.mono (fun ω hω => ((hUc ω).tendsto (τ.time ω)).comp hω))
  apply le_antisymm (expected_stoppedValue_le_initial hU hUc hUb τ)
  apply le_of_tendsto_of_tendsto (happrox.comp hns.tendsto_atTop) hlim
  apply Eventually.of_forall
  intro n
  exact (integral_mono (hZi (θ (ns n))) (hUi (θ (ns n)))
    (fun ω => hdom _ ((θ (ns n)).le_horizon ω) ω)).trans
      (expected_stoppedValue_le_of_le hU hUc hUb (η n) (θ (ns n)) (fun _ => min_le_left _ _))

theorem firstContact_expectedReward_eq_initial
    (hU : Supermartingale U 𝓕 P) (hUc : ∀ ω, Continuous (fun t => U t ω))
    (hUb : ∀ t ω, ‖U t ω‖ ≤ C) (hZm : Measurable Z.uncurry)
    (hZc : ∀ ω, Continuous (fun t => Z t ω)) (hZb : ∀ t ω, ‖Z t ω‖ ≤ D)
    (hdom : ∀ t, t ≤ T → ∀ ω, Z t ω ≤ U t ω)
    (τ : StoppingRule 𝓕 T) (hbefore : ∀ ω t, t < τ.time ω → Z t ω < U t ω)
    (hcontact : ∀ᵐ ω ∂P, U (τ.time ω) ω = Z (τ.time ω) ω)
    (θ : ℕ → StoppingRule 𝓕 T)
    (happrox : Tendsto (fun n => ∫ ω, Z ((θ n).time ω) ω ∂P) atTop (𝓝 (∫ ω, U 0 ω ∂P))) :
    (∫ ω, Z (τ.time ω) ω ∂P) = ∫ ω, U 0 ω ∂P := by
  rw [← integral_congr_ae hcontact]
  exact expected_firstContact_eq_initial hU hUc hUb hZm hZc hZb hdom τ hbefore θ happrox

end MathFin.BlackScholes.AmericanPut.Stopping
