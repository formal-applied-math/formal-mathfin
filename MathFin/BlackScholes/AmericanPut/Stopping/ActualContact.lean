/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.StrictExerciseGeometry
public import MathFin.BlackScholes.AmericanPut.Stopping.ClassicalContact

/-! # A first-contact rule constructed from the actual stopping price

The actual price `canonicalPrice` is a `PutEnvelope`, so the classical first-contact rule
`classicalContactRule` applies to it at strike `1`, rate `k`, dividend `h`, volatility
`Real.sqrt 2` and spot `Real.exp x`: the rule stopping at the first zero of the gap between the
discounted price and the discounted payoff is admissible and exercises at payoff contact. The
lemmas here only restate the classical ones in the normalized conventions
(`x + (k-h-1)*t + Real.sqrt 2 * W t` for the log spot, remaining time `T - t`).
Optimality and the dynamic programming principle are not assumed.

## Result

Public entry points include `classicalLogSpot_canonical`, `normalizedRate_sqrt_two`,
`canonicalContactRule`, `canonicalContactRule_contact`, `canonicalContactRule_price_eq`,
`canonicalContactRule_continuation_before`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

variable {Ω : Type*}

/-- At strike `1`, spot `Real.exp x` and volatility `Real.sqrt 2` the strike-normalized log spot
is `x + (k-h-1)*t + Real.sqrt 2 * W t`. -/
@[simp] theorem classicalLogSpot_canonical (W : ℝ≥0 → Ω → ℝ) (k h x : ℝ) (t : ℝ≥0) (ω : Ω) :
    classicalLogSpot W 1 k h (Real.sqrt 2) (Real.exp x) t ω =
      x+(k-h-1)*(t : ℝ)+Real.sqrt 2*W t ω := by
  simp only [classicalLogSpot,div_one,Real.log_exp,Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

/-- At volatility `Real.sqrt 2` the normalized time `σ^2/2*s` is the physical time `s`. -/
@[simp] theorem sqrt_two_sq_div_two_mul (s : ℝ) : Real.sqrt 2^2/2*s = s := by
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

/-- At volatility `Real.sqrt 2` the normalized rate is the rate itself. -/
@[simp] theorem normalizedRate_sqrt_two (r : ℝ) : normalizedRate r (Real.sqrt 2) = r := by
  rw [normalizedRate,Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

variable [MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {W : ℝ≥0 → Ω → ℝ} {k h : ℝ}

/-- The rule stopping at the first zero of the gap between the discounted price and the
discounted payoff, that is, at first contact of the price with the payoff: the classical
first-contact rule for the actual price. -/
noncomputable abbrev canonicalContactRule (hk : 0 ≤ k) (hW : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (x : ℝ) (T : ℝ≥0) : StoppingRule 𝓕 T :=
  classicalContactRule k h (Real.sqrt 2)
    (canonicalPrice_putEnvelope (h := h) hk) hW hpaths one_pos (Real.exp_pos x) T

theorem canonicalContactRule_price_eq (hk : 0 ≤ k) (hW : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (x : ℝ) (T : ℝ≥0) (ω : Ω) :
    let s := (canonicalContactRule (h := h) hk hW hpaths x T).time ω
    canonicalPrice k h (x+(k-h-1)*(s : ℝ)+Real.sqrt 2*W s ω) ((T : ℝ)-(s : ℝ)) =
      putPayoff (x+(k-h-1)*(s : ℝ)+Real.sqrt 2*W s ω) := by
  have he := classicalContactRule_price_eq (K := 1) (r := k) (q := h) (σ := Real.sqrt 2)
    (canonicalPrice_putEnvelope (h := h) hk) hW hpaths one_pos (Real.exp_pos x) T ω
  simpa using he

theorem canonicalContactRule_continuation_before (hk : 0 ≤ k) (hW : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (x : ℝ) (T : ℝ≥0) (ω : Ω)
    {t : ℝ≥0} (ht : t < (canonicalContactRule (h := h) hk hW hpaths x T).time ω) :
    (x+(k-h-1)*(t : ℝ)+Real.sqrt 2*W t ω, (T : ℝ)-(t : ℝ)) ∈ canonicalContinuationRegion k h := by
  obtain ⟨htT,hlt⟩ := classicalContactRule_payoff_lt (K := 1) (r := k) (q := h)
    (σ := Real.sqrt 2) (canonicalPrice_putEnvelope (h := h) hk) hW hpaths one_pos
    (Real.exp_pos x) ω ht
  refine ⟨sub_pos.mpr (by exact_mod_cast htT),?_⟩
  simpa using hlt

theorem canonicalContactRule_exercise_before_expiry (hk : 0 ≤ k) (hW : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (x : ℝ) (T : ℝ≥0) (ω : Ω)
    (ht : (canonicalContactRule (h := h) hk hW hpaths x T).time ω < T) :
    let s := (canonicalContactRule (h := h) hk hW hpaths x T).time ω
    Real.exp (x+(k-h-1)*(s : ℝ)+Real.sqrt 2*W s ω) ≤
      canonicalStockBoundary k h ((T : ℝ)-(s : ℝ)) :=
  (canonicalPrice_contact_iff hk _ (sub_pos.mpr (by exact_mod_cast ht))).mp
    (canonicalContactRule_price_eq hk hW hpaths x T ω)

/-- The discounted actual price along the Brownian log-state: the classical candidate of the
actual price `canonicalPrice k h`, at strike `1`, rate `k`, dividend `h`, volatility
`Real.sqrt 2` and spot `Real.exp x`. -/
noncomputable abbrev canonicalDiscountedPrice (k h x : ℝ) (T : ℝ≥0) :=
  classicalCandidate brownian 1 k h (Real.sqrt 2) (Real.exp x) (canonicalPrice k h) T

section Brownian

variable [MeasurableSpace (ℝ≥0 → ℝ)] {𝓖 : Filtration ℝ≥0 ‹MeasurableSpace (ℝ≥0 → ℝ)›}

/-- At first contact the discounted actual price equals the discounted reward. -/
theorem canonicalContactRule_contact (hk : 0 ≤ k) (hW : Adapted 𝓖 brownian)
    (hpaths : ∀ ω, Continuous (fun t => brownian t ω)) (x : ℝ) (T : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    let θ := canonicalContactRule (h := h) hk hW hpaths x T
    canonicalDiscountedPrice k h x T (θ.time ω) ω =
      putReward brownian 1 k h (Real.sqrt 2) (Real.exp x) θ.time ω :=
  classicalContactRule_contact
    (canonicalPrice_putEnvelope (h := h) hk) hW hpaths one_pos (Real.exp_pos x) T ω

/-- Before first contact the discounted actual price strictly exceeds the discounted reward. -/
theorem canonicalContactRule_reward_lt (hk : 0 ≤ k) (hW : Adapted 𝓖 brownian)
    (hpaths : ∀ ω, Continuous (fun t => brownian t ω)) (x : ℝ) (T : ℝ≥0) (ω : ℝ≥0 → ℝ)
    {t : ℝ≥0} (ht : t < (canonicalContactRule (h := h) hk hW hpaths x T).time ω) :
    frozenPutReward brownian 1 k h (Real.sqrt 2) (Real.exp x) T t ω <
      canonicalDiscountedPrice k h x T t ω :=
  classicalContactRule_reward_lt
    (canonicalPrice_putEnvelope (h := h) hk) hW hpaths one_pos (Real.exp_pos x) ω ht

end Brownian

theorem brownianUsual_adapted :
    @Adapted _ _ (completedMeasurableSpace gaussianLimit) _ _ _
        brownianUsualFiltration brownian := by
  intro t
  exact (brownian_adapted t).mono (brownian_completedRaw_le_usual t) le_rfl

/-- Concrete admissible rule on the completed usual Brownian space. -/
noncomputable def brownianUsualActualContactRule {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T : ℝ≥0) :
    @StoppingRule (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit) ℝ≥0 _
      brownianUsualFiltration T :=
  @canonicalContactRule _ (completedMeasurableSpace gaussianLimit) brownianUsualFiltration
    brownian k h hk brownianUsual_adapted continuous_brownian x T

end MathFin.BlackScholes.AmericanPut.Stopping
