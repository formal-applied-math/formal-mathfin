/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.Rules
public import MathFin.Foundations.ItoLemma2D

/-!
# Discounted stopped put payoff for dividend-paying geometric Brownian motion

The drift of the stock is `r-q`; `r` is the discount rate. At any admissible
rule the reward is measurable and, for nonnegative rates and spot, lies in
`[0,K]`. Its integrability follows without any optional-stopping assumption.
The process need only be jointly measurable for these elementary facts.

## Result

Public entry points include `putReward`, `putReward_measurable`, `putReward_nonneg`,
`putReward_le_strike`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The put payoff `max (K - gbmValue S (r-q) σ (θ ω) (W (θ ω) ω)) 0` at the stopped stock value,
discounted by `exp (-r*θ ω)`. -/
noncomputable def putReward (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (θ : Ω → ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-r*(θ ω : ℝ))*max (K-MathFin.gbmValue S (r-q) σ (θ ω) (W (θ ω) ω)) 0

theorem putReward_measurable {W : ℝ≥0 → Ω → ℝ} (hW : Measurable W.uncurry)
    (K r q σ S : ℝ) {θ : Ω → ℝ≥0} (hθ : Measurable θ) :
    Measurable (putReward W K r q σ S θ) := by
  have hstopped : Measurable (fun ω => W (θ ω) ω) := hW.comp (hθ.prodMk measurable_id)
  have htime : Measurable (fun ω => (θ ω : ℝ)) := NNReal.continuous_coe.measurable.comp hθ
  unfold putReward MathFin.gbmValue
  fun_prop

omit [MeasurableSpace Ω] in
theorem putReward_nonneg (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (θ : Ω → ℝ≥0) (ω : Ω) :
    0 ≤ putReward W K r q σ S θ ω :=
  mul_nonneg (Real.exp_pos _).le (le_max_right _ _)

omit [MeasurableSpace Ω] in
theorem putReward_le_strike (W : ℝ≥0 → Ω → ℝ) {K r q σ S : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (θ : Ω → ℝ≥0) (ω : Ω) :
    putReward W K r q σ S θ ω ≤ K := by
  have hstock : 0 ≤ MathFin.gbmValue S (r-q) σ (θ ω) (W (θ ω) ω) :=
    mul_nonneg hS (Real.exp_pos _).le
  have hpay : max (K-MathFin.gbmValue S (r-q) σ (θ ω) (W (θ ω) ω)) 0 ≤ K :=
    max_le (by linarith) hK
  have he : Real.exp (-r*(θ ω : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr) (θ ω).coe_nonneg)
  unfold putReward
  calc
    _ ≤ 1*max (K-MathFin.gbmValue S (r-q) σ (θ ω) (W (θ ω) ω)) 0 :=
      mul_le_mul_of_nonneg_right he (le_max_right _ _)
    _ ≤ K := by simpa only [one_mul] using hpay

theorem putReward_integrable {W : ℝ≥0 → Ω → ℝ} (hW : Measurable W.uncurry)
    (P : Measure Ω) [IsFiniteMeasure P] {K r q σ S : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) {θ : Ω → ℝ≥0} (hθ : Measurable θ) :
    Integrable (putReward W K r q σ S θ) P :=
  (integrable_const K).mono_nonneg (putReward_measurable hW K r q σ S hθ).aestronglyMeasurable
    (Filter.Eventually.of_forall (putReward_nonneg W K r q σ S θ))
    (Filter.Eventually.of_forall (putReward_le_strike W hK hr hS θ))

theorem putReward_zero_ae {W : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) (K r q σ S : ℝ) :
    putReward W K r q σ S (fun _ => 0) =ᵐ[P] fun _ => max (K-S) 0 := by
  filter_upwards [hzero] with ω hω
  simp [putReward,MathFin.gbmValue,hω]

end MathFin.BlackScholes.AmericanPut.Stopping
