/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.Reward

/-!
# The continuous-time American put value as a supremum over stopping rules

This is a financial definition, not the classical PDE solution predicate.
The nonempty bounded payoff-value set is proved explicitly. Elementary value
bounds, immediate exercise, the terminal payoff, and maturity monotonicity
follow from the actual stopping rules. No PDE identification is asserted.

## Result

Public entry points include `putRewardAt`, `americanPutValue`, `expectedReward_le_strike`,
`expectedReward_le_value`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The discounted put payoff process `t ↦ putReward W K r q σ S (fun _ => t)`. -/
noncomputable def putRewardAt (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (t : ℝ≥0) : Ω → ℝ :=
  putReward W K r q σ S fun _ => t

/-- The American put value: `stoppingValue` of the discounted put payoff process `putRewardAt` over
the rules bounded by the horizon `T`. -/
noncomputable def americanPutValue (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T : ℝ≥0) : ℝ :=
  stoppingValue P 𝓕 (putRewardAt W K r q σ S) T

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
  {K r q σ S : ℝ} {T U : ℝ≥0}

theorem expectedReward_le_strike (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (θ : StoppingRule 𝓕 T) :
    (∫ ω, putReward W K r q σ S θ.time ω ∂P) ≤ K := by
  have hh := integral_mono (putReward_integrable (q := q) (σ := σ) hW P hK hr hS θ.measurable_time)
    (integrable_const K) (putReward_le_strike W hK hr hS θ.time)
  simpa only [integral_const,probReal_univ,one_smul] using hh

theorem expectedReward_le_value (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (θ : StoppingRule 𝓕 T) :
    (∫ ω, putReward W K r q σ S θ.time ω ∂P) ≤ americanPutValue P 𝓕 W K r q σ S T :=
  integral_le_stoppingValue (Z := putRewardAt W K r q σ S)
    (fun η _ ↦ expectedReward_le_strike hW hK hr hS η) (mem_univ θ)

omit [IsProbabilityMeasure P] in
/-- Some bounded rule comes within `ε` of the value. -/
theorem exists_expectedReward_gt_value_sub {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : StoppingRule 𝓕 T, americanPutValue P 𝓕 W K r q σ S T-ε <
      ∫ ω, putReward W K r q σ S θ.time ω ∂P := by
  obtain ⟨θ,-,h⟩ := exists_lt_of_lt_stoppingValue
    (sub_lt_self (americanPutValue P 𝓕 W K r q σ S T) hε) univ_nonempty
  exact ⟨θ,h⟩

theorem value_le_strike (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) : americanPutValue P 𝓕 W K r q σ S T ≤ K := by
  exact stoppingValue_le univ_nonempty fun θ _ ↦ expectedReward_le_strike hW hK hr hS θ

theorem value_nonneg (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) : 0 ≤ americanPutValue P 𝓕 W K r q σ S T :=
  (integral_nonneg (putReward_nonneg W K r q σ S (StoppingRule.zero 𝓕 T).time)).trans
    (expectedReward_le_value hW hK hr hS (StoppingRule.zero 𝓕 T))

theorem expectedReward_zero (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    (∫ ω, putReward W K r q σ S (StoppingRule.zero 𝓕 T).time ω ∂P) = max (K-S) 0 := by
  change (∫ ω, putReward W K r q σ S (fun _ => 0) ω ∂P) = _
  rw [integral_congr_ae (putReward_zero_ae hzero K r q σ S)]
  simp

theorem payoff_le_value (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) : max (K-S) 0 ≤ americanPutValue P 𝓕 W K r q σ S T := by
  rw [← expectedReward_zero (𝓕 := 𝓕) (T := T) hzero]
  exact expectedReward_le_value hW hK hr hS (StoppingRule.zero 𝓕 T)

theorem value_at_expiry (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) : americanPutValue P 𝓕 W K r q σ S 0 = max (K-S) 0 := by
  apply le_antisymm _ (payoff_le_value hW hzero hK hr hS)
  refine stoppingValue_le univ_nonempty fun θ _ ↦ ?_
  have heq : θ.time = (StoppingRule.zero 𝓕 0).time := funext θ.time_eq_zero
  change (∫ ω, putReward W K r q σ S θ.time ω ∂P) ≤ _
  rw [heq,expectedReward_zero hzero]

theorem value_mono_horizon (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (hTU : T ≤ U) :
    americanPutValue P 𝓕 W K r q σ S T ≤ americanPutValue P 𝓕 W K r q σ S U := by
  exact stoppingValue_le univ_nonempty fun θ _ ↦
    expectedReward_le_value hW hK hr hS (θ.extend hTU)

/-- The deterministic maturity rule is admissible, so the American value
dominates the European payoff expectation without any optimal-stopping theorem. -/
theorem european_expectation_le_value (hW : Measurable W.uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    (∫ ω, putReward W K r q σ S (fun _ => T) ω ∂P) ≤ americanPutValue P 𝓕 W K r q σ S T :=
  expectedReward_le_value hW hK hr hS (StoppingRule.constant 𝓕 T T le_rfl)

end MathFin.BlackScholes.AmericanPut.Stopping
