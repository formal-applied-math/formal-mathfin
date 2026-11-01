/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FirstContact
public import MathFin.BlackScholes.AmericanPut.Stopping.ClassicalCandidate

/-!
# The first-contact rule of a put envelope

For any `PutEnvelope p` the gap between the discounted price and the discounted payoff is
continuous, adapted, nonnegative, and zero at maturity. Its first zero therefore supplies
an explicit admissible contact rule, at which the price equals the payoff and before which it
strictly exceeds it; no optimal-stopping assertion is assumed and no PDE is used. The
description of the contact set by an exercise boundary (`classicalGap_zero_iff`,
`classicalContactRule_continuation`) additionally needs `ContinuousBoundaryPutSolution`.

## Result

Public entry points include `classicalCandidate_adapted`, `frozenPutReward`,
`frozenPutReward_adapted`, `frozenPutReward_continuous`, `classicalContactRule_price_eq`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open MathFin.BlackScholes.AmericanPut.Boundary
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
  {k h K r q σ S : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem classicalCandidate_adapted (hp : PutEnvelope p)
    (hW : Adapted 𝓕 W) (T : ℝ≥0) : Adapted 𝓕 (classicalCandidate W K r q σ S p T) := by
  intro t
  let s := min t T
  have htime : 0 ≤ σ^2/2*((T : ℝ)-(s : ℝ)) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast min_le_right t T))
  have hc : Continuous (fun w : ℝ => p (Real.log (S/K)+(r-q-σ^2/2)*(s : ℝ)+σ*w)
      (σ^2/2*((T : ℝ)-(s : ℝ)))) := by
    exact hp.price_continuous.comp_continuous
      (show Continuous (fun w : ℝ => (Real.log (S/K)+(r-q-σ^2/2)*(s : ℝ)+σ*w,
        σ^2/2*((T : ℝ)-(s : ℝ)))) by fun_prop) (fun _ => htime)
  have hm := hc.measurable.comp ((hW s).mono (𝓕.mono (min_le_left t T)) le_rfl)
  exact measurable_const.mul (measurable_const.mul hm)

/-- The put reward for exercise at the deterministic time `min t T`, so it is frozen once `t`
passes maturity. -/
noncomputable def frozenPutReward (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ) (T t : ℝ≥0) : Ω → ℝ :=
  putReward W K r q σ S (fun _ => min t T)

theorem frozenPutReward_adapted (hW : Adapted 𝓕 W) (T : ℝ≥0) :
    Adapted 𝓕 (frozenPutReward W K r q σ S T) := by
  intro t
  have hw : @Measurable Ω ℝ (𝓕 t) _ (W (min t T)) :=
    (hW _).mono (𝓕.mono (min_le_left t T)) le_rfl
  unfold frozenPutReward putReward MathFin.gbmValue
  dsimp only
  fun_prop

omit [MeasurableSpace Ω] in
theorem frozenPutReward_continuous (hW : ∀ ω, Continuous (fun t => W t ω)) (T : ℝ≥0) (ω : Ω) :
    Continuous (fun t => frozenPutReward W K r q σ S T t ω) := by
  unfold frozenPutReward putReward MathFin.gbmValue
  fun_prop

omit [MeasurableSpace Ω] in
theorem frozenPutReward_norm_le (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) (T t : ℝ≥0) (ω : Ω) :
    ‖frozenPutReward W K r q σ S T t ω‖ ≤ K := by
  rw [frozenPutReward,Real.norm_eq_abs,abs_of_nonneg (putReward_nonneg _ _ _ _ _ _ _ _)]
  exact putReward_le_strike W hK hr hS _ ω

/-- The gap `classicalCandidate - frozenPutReward` between the discounted classical price and
the discounted payoff. -/
noncomputable def classicalGap (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ)
    (p : ℝ → ℝ → ℝ) (T t : ℝ≥0) (ω : Ω) : ℝ :=
  classicalCandidate W K r q σ S p T t ω - frozenPutReward W K r q σ S T t ω

theorem classicalGap_adapted (hp : PutEnvelope p)
    (hW : Adapted 𝓕 W) (T : ℝ≥0) : Adapted 𝓕 (classicalGap W K r q σ S p T) :=
  fun t => (classicalCandidate_adapted hp hW T t).sub (frozenPutReward_adapted hW T t)

omit [MeasurableSpace Ω] in
theorem classicalGap_continuous (hp : PutEnvelope p)
    (hW : ∀ ω, Continuous (fun t => W t ω)) (T : ℝ≥0) (ω : Ω) :
    Continuous (fun t => classicalGap W K r q σ S p T t ω) :=
  (classicalCandidate_continuous hp hW T ω).sub (frozenPutReward_continuous hW T ω)

omit [MeasurableSpace Ω] in
theorem classicalGap_nonneg (hp : PutEnvelope p)
    (hK : 0 < K) (hS : 0 < S) (T t : ℝ≥0) (ω : Ω) :
    0 ≤ classicalGap W K r q σ S p T t ω := by
  have hh := classicalCandidate_dominates (r := r) (q := q) (σ := σ) hp W hK hS (min_le_right t T) ω
  simpa [classicalGap,frozenPutReward,classicalCandidate,min_assoc] using sub_nonneg.mpr hh

omit [MeasurableSpace Ω] in
theorem classicalGap_terminal (hp : PutEnvelope p)
    (hK : 0 < K) (hS : 0 < S) (T : ℝ≥0) (ω : Ω) :
    classicalGap W K r q σ S p T T ω = 0 := by
  simp only [classicalGap,classicalCandidate_maturity hp W hK hS,frozenPutReward,min_self,sub_self]

/-- The rule that exercises at the first zero of `classicalGap`, admissible by
`firstContactRule`. -/
noncomputable def classicalContactRule (hp : PutEnvelope p)
    (hadapt : Adapted 𝓕 W) (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 < K) (hS : 0 < S) (T : ℝ≥0) : StoppingRule 𝓕 T :=
  firstContactRule (Z := classicalGap W K r q σ S p T)
    (classicalGap_adapted hp hadapt T) (classicalGap_continuous hp hpaths T)
    (classicalGap_nonneg hp hK hS T) T (classicalGap_terminal hp hK hS T)

theorem classicalContactRule_gap (hp : PutEnvelope p)
    (hadapt : Adapted 𝓕 W) (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 < K) (hS : 0 < S) (T : ℝ≥0) (ω : Ω) :
    classicalGap W K r q σ S p T
      ((classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T).time ω) ω = 0 :=
  (firstContactTime_mem (classicalGap_continuous (r := r) (q := q) (σ := σ) hp hpaths T)
    (classicalGap_terminal hp hK hS T) ω).2

theorem classicalContactRule_contact (hp : PutEnvelope p)
    (hadapt : Adapted 𝓕 W) (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 < K) (hS : 0 < S) (T : ℝ≥0) (ω : Ω) :
    let θ := classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T
    classicalCandidate W K r q σ S p T (θ.time ω) ω = putReward W K r q σ S θ.time ω := by
  let θ := classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T
  have hh := classicalContactRule_gap (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T ω
  change classicalGap W K r q σ S p T (θ.time ω) ω = 0 at hh
  have ht := θ.le_horizon ω
  simp only [classicalGap,frozenPutReward,min_eq_left ht,sub_eq_zero] at hh
  exact hh

omit [MeasurableSpace Ω] in
/-- The gap is the discounted `K * (p - payoff)` along the log spot, before maturity. -/
theorem classicalGap_eq (hK : 0 < K) (hS : 0 < S) {T t : ℝ≥0} (ht : t ≤ T) (ω : Ω) :
    classicalGap W K r q σ S p T t ω =
      Real.exp (-r*(t : ℝ))*(K*(p (classicalLogSpot W K r q σ S t ω) (σ^2/2*((T : ℝ)-(t : ℝ))) -
        putPayoff (classicalLogSpot W K r q σ S t ω))) := by
  simp only [classicalGap,classicalCandidate,frozenPutReward,putReward,min_eq_left ht]
  rw [← scaled_classical_payoff W hK hS t ω]
  ring

omit [MeasurableSpace Ω] in
theorem classicalGap_zero_iff (hp : ContinuousBoundaryPutSolution k h p b)
    (hK : 0 < K) (hS : 0 < S) (hσ : 0 < σ) {T t : ℝ≥0} (ht : t < T) (ω : Ω) :
    classicalGap W K r q σ S p T t ω = 0 ↔
      classicalLogSpot W K r q σ S t ω ≤ b (σ^2/2*((T : ℝ)-(t : ℝ))) := by
  have htime : 0 < σ^2/2*((T : ℝ)-(t : ℝ)) :=
    mul_pos (by positivity) (sub_pos.mpr (by exact_mod_cast ht))
  rw [classicalGap_eq hK hS ht.le,← hp.contact_iff htime]
  simp only [mul_eq_zero,(Real.exp_pos _).ne',hK.ne',false_or,sub_eq_zero]

theorem classicalContactRule_gap_pos (hp : PutEnvelope p)
    (hadapt : Adapted 𝓕 W) (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 < K) (hS : 0 < S) {T t : ℝ≥0} (ω : Ω)
    (ht : t < (classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T).time ω) :
    0 < classicalGap W K r q σ S p T t ω :=
  firstContactTime_pos_before (classicalGap_continuous (r := r) (q := q) (σ := σ) hp hpaths T)
    (classicalGap_nonneg hp hK hS T) (classicalGap_terminal hp hK hS T) ω ht

/-- Before first contact the discounted price strictly exceeds the discounted payoff. -/
theorem classicalContactRule_reward_lt (hp : PutEnvelope p)
    (hadapt : Adapted 𝓕 W) (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 < K) (hS : 0 < S) {T t : ℝ≥0} (ω : Ω)
    (ht : t < (classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T).time ω) :
    frozenPutReward W K r q σ S T t ω < classicalCandidate W K r q σ S p T t ω :=
  sub_pos.mp (classicalContactRule_gap_pos hp hadapt hpaths hK hS ω ht)

/-- At first contact the price equals the payoff. -/
theorem classicalContactRule_price_eq (hp : PutEnvelope p)
    (hadapt : Adapted 𝓕 W) (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 < K) (hS : 0 < S) (T : ℝ≥0) (ω : Ω) :
    let θ := classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T
    p (classicalLogSpot W K r q σ S (θ.time ω) ω) (σ^2/2*((T : ℝ)-(θ.time ω : ℝ))) =
      putPayoff (classicalLogSpot W K r q σ S (θ.time ω) ω) := by
  intro θ
  have hz := classicalContactRule_gap (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T ω
  change classicalGap W K r q σ S p T (θ.time ω) ω = 0 at hz
  rw [classicalGap_eq hK hS (θ.le_horizon ω)] at hz
  simpa only [mul_eq_zero,(Real.exp_pos _).ne',hK.ne',false_or,sub_eq_zero] using hz

/-- Before first contact the price strictly exceeds the payoff. -/
theorem classicalContactRule_payoff_lt (hp : PutEnvelope p)
    (hadapt : Adapted 𝓕 W) (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 < K) (hS : 0 < S) {T t : ℝ≥0} (ω : Ω)
    (ht : t < (classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T).time ω) :
    t < T ∧ putPayoff (classicalLogSpot W K r q σ S t ω) <
      p (classicalLogSpot W K r q σ S t ω) (σ^2/2*((T : ℝ)-(t : ℝ))) := by
  have htT : t < T := ht.trans_le
    ((classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T).le_horizon ω)
  have hpos := classicalContactRule_gap_pos hp hadapt hpaths hK hS ω ht
  rw [classicalGap_eq hK hS htT.le] at hpos
  exact ⟨htT,sub_pos.mp ((mul_pos_iff_of_pos_left hK).mp
    ((mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hpos))⟩

theorem classicalContactRule_continuation (hp : ContinuousBoundaryPutSolution k h p b)
    (hadapt : Adapted 𝓕 W) (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 < K) (hS : 0 < S) (hσ : 0 < σ) {T t : ℝ≥0} (ω : Ω)
    (ht : t < (classicalContactRule (r := r) (q := q) (σ := σ) hp.toPutEnvelope hadapt hpaths
      hK hS T).time ω) :
    t < T ∧ b (σ^2/2*((T : ℝ)-(t : ℝ))) < classicalLogSpot W K r q σ S t ω := by
  obtain ⟨htT,hlt⟩ := classicalContactRule_payoff_lt hp.toPutEnvelope hadapt hpaths hK hS ω ht
  refine ⟨htT,lt_of_not_ge fun hx => hlt.ne' ?_⟩
  exact (hp.contact_iff (mul_pos (by positivity) (sub_pos.mpr (by exact_mod_cast htT)))).mpr hx

/-- The explicit first-contact rule discharges the admissibility and contact
premises of verification. Only the candidate's two stochastic properties are
left here, and neither is silently inferred from the classical PDE. -/
theorem classical_price_eq_value_of_contact_verification
    {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ≥0}
    (hp : PutEnvelope p) (hW : Measurable W.uncurry) (hadapt : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S)
    (hsuper : Supermartingale (classicalCandidate W K r q σ S p T) 𝓕 P)
    (hmart : Martingale (fun t ω => classicalCandidate W K r q σ S p T
      (min t ((classicalContactRule (r := r) (q := q) (σ := σ) hp hadapt hpaths hK hS T).time ω)) ω)
          𝓕 P) :
    americanPutValue P 𝓕 W K r q σ S T = K*p (Real.log (S/K)) (σ^2/2*(T : ℝ)) :=
  classical_price_eq_value_of_verification hp hW hpaths hzero hK hr hS hsuper
    (classicalContactRule hp hadapt hpaths hK hS T)
    (Filter.Eventually.of_forall (classicalContactRule_contact hp hadapt hpaths hK hS T)) hmart

end MathFin.BlackScholes.AmericanPut.Stopping
