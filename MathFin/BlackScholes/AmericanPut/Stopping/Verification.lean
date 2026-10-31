/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.GridSampling
public import MathFin.BlackScholes.AmericanPut.Stopping.AmericanValue

/-!
# A bounded continuous-path verification principle for the American value

A supermartingale dominating the discounted reward bounds the actual supremum over stopping
rules, and any admissible rule attaining the initial value gives equality (`value_eq_of_attained`).
A contact rule with a martingale stopped candidate attains it. This file assumes the stochastic
properties; the classical free-boundary contract supplies them in `ContactMartingale` and
`ClassicalSupermartingale`, and the actual price supplies them in `Actual*`.

## Result

Public entry points include `candidate_stopped_integrable`, `value_le_supermartingale_candidate`,
`value_eq_of_attained`, `expectedReward_eq_initial_of_contact_martingale`,
`value_eq_of_contact_martingale`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W U : ℝ≥0 → Ω → ℝ}
  {K r q σ S C : ℝ} {T : ℝ≥0}

theorem candidate_stopped_integrable
    (hU : Supermartingale U 𝓕 P) (hcont : ∀ ω, Continuous (fun t => U t ω))
    (hbound : ∀ t ω, ‖U t ω‖ ≤ C) (θ : StoppingRule 𝓕 T) :
    Integrable (fun ω => U (θ.time ω) ω) P := by
  have hmeas : Measurable U.uncurry :=
    measurable_uncurry_of_continuous_of_measurable hcont
      (fun t => (hU.stronglyAdapted t).measurable.mono (𝓕.le t) le_rfl)
  exact (integrable_const C).mono'
    (hmeas.comp (θ.measurable_time.prodMk measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => hbound _ ω))

theorem value_le_supermartingale_candidate
    (hW : Measurable W.uncurry) (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S)
    (hU : Supermartingale U 𝓕 P) (hcont : ∀ ω, Continuous (fun t => U t ω))
    (hbound : ∀ t ω, ‖U t ω‖ ≤ C)
    (hdom : ∀ t, t ≤ T → ∀ ω, putReward W K r q σ S (fun _ => t) ω ≤ U t ω) :
    americanPutValue P 𝓕 W K r q σ S T ≤ ∫ ω, U 0 ω ∂P := by
  refine stoppingValue_le univ_nonempty fun θ _ ↦ ?_
  exact (integral_mono
    (putReward_integrable hW P hK hr hS θ.measurable_time)
    (candidate_stopped_integrable hU hcont hbound θ)
    (fun ω => hdom (θ.time ω) (θ.le_horizon ω) ω)).trans
      (expected_stoppedValue_le_initial hU hcont hbound θ)

/-- The verification principle: a supermartingale `U` dominating the discounted reward bounds the
value from above by `∫ U 0`, and any admissible rule whose expected reward is already `∫ U 0`
attains it. So the price is the value and that rule is optimal. How a rule is shown to attain is
the only thing that differs between tracks: `expectedReward_eq_initial_of_contact_martingale`
(the classical route, from a martingale contact-stopped candidate) and
`firstContact_expectedReward_eq_initial` (the actual route, from grid rules approaching the
price). -/
theorem value_eq_of_attained
    (hW : Measurable W.uncurry) (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S)
    (hU : Supermartingale U 𝓕 P) (hcont : ∀ ω, Continuous (fun t => U t ω))
    (hbound : ∀ t ω, ‖U t ω‖ ≤ C)
    (hdom : ∀ t, t ≤ T → ∀ ω, putReward W K r q σ S (fun _ => t) ω ≤ U t ω)
    (θ : StoppingRule 𝓕 T)
    (hatt : (∫ ω, putReward W K r q σ S θ.time ω ∂P) = ∫ ω, U 0 ω ∂P) :
    americanPutValue P 𝓕 W K r q σ S T = ∫ ω, U 0 ω ∂P :=
  le_antisymm (value_le_supermartingale_candidate hW hK hr hS hU hcont hbound hdom)
    (hatt.ge.trans (expectedReward_le_value hW hK hr hS θ))

/-- A contact rule whose stopped candidate is a martingale attains the initial value. -/
theorem expectedReward_eq_initial_of_contact_martingale
    (hcont : ∀ ω, Continuous (fun t => U t ω)) (hbound : ∀ t ω, ‖U t ω‖ ≤ C)
    (θ : StoppingRule 𝓕 T)
    (hcontact : ∀ᵐ ω ∂P, U (θ.time ω) ω = putReward W K r q σ S θ.time ω)
    (hmart : Martingale (fun t ω => U (min t (θ.time ω)) ω) 𝓕 P) :
    (∫ ω, putReward W K r q σ S θ.time ω ∂P) = ∫ ω, U 0 ω ∂P := by
  have hh := expected_stoppedValue_eq_initial hmart
    (fun ω => (hcont ω).comp (continuous_id.min continuous_const))
    (fun t ω => hbound _ ω) θ
  simp only [min_self,zero_min] at hh
  exact (integral_congr_ae hcontact).symm.trans hh

/-- Verification with an explicit admissible contact rule. Neither optimality
nor equality with the stopping-value supremum is among the hypotheses. -/
theorem value_eq_of_contact_martingale
    (hW : Measurable W.uncurry) (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S)
    (hU : Supermartingale U 𝓕 P) (hcont : ∀ ω, Continuous (fun t => U t ω))
    (hbound : ∀ t ω, ‖U t ω‖ ≤ C)
    (hdom : ∀ t, t ≤ T → ∀ ω, putReward W K r q σ S (fun _ => t) ω ≤ U t ω)
    (θ : StoppingRule 𝓕 T)
    (hcontact : ∀ᵐ ω ∂P, U (θ.time ω) ω = putReward W K r q σ S θ.time ω)
    (hmart : Martingale (fun t ω => U (min t (θ.time ω)) ω) 𝓕 P) :
    americanPutValue P 𝓕 W K r q σ S T = ∫ ω, U 0 ω ∂P :=
  value_eq_of_attained hW hK hr hS hU hcont hbound hdom θ
    (expectedReward_eq_initial_of_contact_martingale hcont hbound θ hcontact hmart)

end MathFin.BlackScholes.AmericanPut.Stopping
