/-
Copyright (c) 2026 Robert Martin, Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin, Adam Kiezun
-/
module

public import MathFin.Models.BlackScholes.American.Stopping.GridSampling
public import MathFin.Pricing.ContinuousMarket
public import MathFin.Probability.Martingales.StoppingRule
public import MathFin.Probability.Discrete.DiscreteStoppingValue

/-!
# Discrete rules sampled at finitely many deterministic times

A continuous-time rule that may stop only on a finite schedule of dates `e 0 < ⋯ < e m` is a
discrete rule for the filtration sampled along the schedule, and conversely. So the continuous
stopping value over such rules is the discrete value of the sampled reward, that is the expected
Snell envelope of the sampled filtration, and it is attained. The uniform capped grid of
`FiniteExerciseGrid.lean` is the case `e i = min (i δ) T`; this module treats any strictly
increasing schedule.

## Main definitions

* `StoppingRule.toSampledRule`: a discrete rule `η` for `ContinuousMarket.sampledFiltration 𝓕 hs`
  read back in continuous time as `ω ↦ s (η.time ω)`, with horizon `s N`.
* `sampleTimes`: a finite schedule `e : Fin (m + 1) → ℝ≥0` run out over `ℕ`, constant at `e m`.
* `sampledRuleEquiv`: the rules for the sampled filtration with horizon `m` are the rules with
  values in the schedule, `e (Fin.last m) = T`.

## Main results

* `stoppingValue_valuedIn_range`: the continuous stopping value over the rules valued in the
  schedule is the discrete value of the sampled reward.
* `stoppingValue_valuedIn_range_eq_integral_snellEnvelope`: it is the expectation at `0` of the
  Snell envelope of the sampled reward.
* `exists_mem_valuedIn_range_integral_eq_stoppingValue`: some rule valued in the schedule attains
  it.

## References

* [G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*][PeskirShiryaev2006],
  ch. I, §2

## Tags

sampled stopping rule, finite exercise schedule, Bermudan option, Snell envelope, deterministic
times, MSC 60G40, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A discrete rule `η` for `ContinuousMarket.sampledFiltration 𝓕 hs` read back in continuous
time as `ω ↦ s (η.time ω)`, with horizon `s N`. -/
def _root_.MathFin.StoppingRule.toSampledRule {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {s : ℕ → ℝ≥0} {hs : Monotone s} {N : ℕ}
    (η : StoppingRule (ContinuousMarket.sampledFiltration 𝓕 hs) N) : StoppingRule 𝓕 (s N) where
  time := fun ω ↦ s (η.time ω)
  stopping := by
    intro t
    have he : {ω | (s (η.time ω) : WithTop ℝ≥0) ≤ t} =
        ⋃ i : ℕ, if s i ≤ t then {ω | (η.time ω : WithTop ℕ) ≤ i} else ∅ := by
      ext ω
      simp only [mem_ofPred_eq,WithTop.coe_le_coe,mem_iUnion]
      constructor
      · intro hω
        refine ⟨η.time ω,?_⟩
        simp [hω]
      · rintro ⟨i,hi⟩
        split_ifs at hi with hit
        · exact (hs (by simpa using hi)).trans hit
        · exact False.elim (notMem_empty ω hi)
    rw [he]
    apply MeasurableSet.iUnion
    intro i
    split_ifs with hit
    · exact 𝓕.mono hit _ (η.stopping i)
    · exact @MeasurableSet.empty Ω (𝓕 t)
  le_horizon := fun ω ↦ hs (η.le_horizon ω)

end MathFin.BlackScholes.AmericanPut.Stopping

namespace MathFin

open MeasureTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

@[ext] theorem StoppingRule.ext {ι : Type*} [LinearOrder ι] {𝓕 : Filtration ι ‹MeasurableSpace Ω›}
    {T : ι} {θ η : StoppingRule 𝓕 T} (h : ∀ ω, θ.time ω = η.time ω) : θ = η := by
  cases θ
  cases η
  simp only [StoppingRule.mk.injEq]
  exact funext h

section Schedule

variable {m : ℕ} (e : Fin (m + 1) → ℝ≥0)

/-- A finite schedule `e 0, …, e m` run out over `ℕ`: `e n` for `n ≤ m`, constant at `e m` after. -/
def sampleTimes (n : ℕ) : ℝ≥0 := e (Fin.clamp n m)

variable {e}

theorem monotone_sampleTimes (he : Monotone e) : Monotone (sampleTimes e) :=
  fun _ _ hab ↦ he (Fin.le_def.2 (min_le_min_right m hab))

theorem sampleTimes_last : sampleTimes e m = e (Fin.last m) :=
  congrArg e (Fin.ext (min_self m))

theorem sampleTimes_val (k : Fin (m + 1)) : sampleTimes e k = e k :=
  congrArg e (Fin.ext (min_eq_left (Nat.le_of_lt_succ k.2)))

/-- On a strictly increasing schedule, `e k ≤ e n` just when the index `k` is at most `n`. -/
theorem le_sampleTimes_iff (he : StrictMono e) (k : Fin (m + 1)) (n : ℕ) :
    e k ≤ sampleTimes e n ↔ k.val ≤ n := by
  rw [sampleTimes, he.le_iff_le, Fin.le_def, Fin.coe_clamp, le_min_iff,
    and_iff_left (Nat.le_of_lt_succ k.2)]

end Schedule

/-- **Rules on a finite schedule are discrete rules.** For a strictly increasing schedule
`e 0 < ⋯ < e m = T`, the stopping rules for the filtration sampled along the schedule, with
horizon `m`, are in bijection with the rules for `𝓕` whose stopping times take values in the
schedule, a rule `η` corresponding to the physical rule `ω ↦ e (η.time ω)`. -/
noncomputable def sampledRuleEquiv (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) {T : ℝ≥0} {m : ℕ}
    {e : Fin (m + 1) → ℝ≥0} (he : StrictMono e) (heT : e (Fin.last m) = T) :
    StoppingRule (ContinuousMarket.sampledFiltration 𝓕 (monotone_sampleTimes he.monotone)) m ≃
      {θ // θ ∈ StoppingRule.valuedIn 𝓕 T (Set.range e)} where
  toFun η := ⟨η.toSampledRule.extend (sampleTimes_last.trans_le heT.le),
    fun ω ↦ ⟨Fin.clamp (η.time ω) m, rfl⟩⟩
  invFun θ :=
    { time := fun ω ↦ (Function.invFun e (θ.1.time ω)).val
      stopping := BlackScholes.AmericanPut.Stopping.isStoppingTime_sampledFiltration
        (monotone_sampleTimes he.monotone) θ.1 fun ω n ↦ by
        obtain ⟨k, hk⟩ := θ.2 ω
        rw [← hk, Function.leftInverse_invFun he.injective, le_sampleTimes_iff he]
      le_horizon := fun ω ↦ Nat.le_of_lt_succ (Function.invFun e _).2 }
  left_inv η := StoppingRule.ext fun ω ↦ by
    change (Function.invFun e (e (Fin.clamp (η.time ω) m))).val = η.time ω
    rw [Function.leftInverse_invFun he.injective, Fin.coe_clamp, min_eq_left (η.le_horizon ω)]
  right_inv θ := Subtype.ext <| StoppingRule.ext fun ω ↦ by
    obtain ⟨k, hk⟩ := θ.2 ω
    change e (Fin.clamp (Function.invFun e (θ.1.time ω)).val m) = θ.1.time ω
    rw [← hk, Function.leftInverse_invFun he.injective]
    exact sampleTimes_val k

/-- The continuous stopping value over the rules that stop only on the schedule `e` is the
discrete stopping value of the reward sampled along it, for the sampled filtration. -/
theorem stoppingValue_valuedIn_range {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}
    {m : ℕ} {e : Fin (m + 1) → ℝ≥0} (he : StrictMono e) (heT : e (Fin.last m) = T)
    (Q : Measure Ω) (Z : ℝ≥0 → Ω → ℝ) :
    stoppingValue Q 𝓕 Z T (StoppingRule.valuedIn 𝓕 T (Set.range e))
      = stoppingValue Q (ContinuousMarket.sampledFiltration 𝓕 (monotone_sampleTimes he.monotone))
          (fun n ω ↦ Z (sampleTimes e n) ω) m := by
  unfold stoppingValue
  rw [Set.image_univ, Set.image_eq_range]
  refine congrArg sSup (Set.ext fun r ↦ ⟨?_, ?_⟩)
  · rintro ⟨θ, rfl⟩
    exact ⟨(sampledRuleEquiv 𝓕 he heT).symm θ, congrArg
      (fun θ' : StoppingRule 𝓕 T ↦ ∫ ω, Z (θ'.time ω) ω ∂Q)
      (congrArg Subtype.val ((sampledRuleEquiv 𝓕 he heT).apply_symm_apply θ))⟩
  · rintro ⟨η, rfl⟩
    exact ⟨sampledRuleEquiv 𝓕 he heT η, rfl⟩

variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0} {m : ℕ} {e : Fin (m + 1) → ℝ≥0}
  {Q : Measure Ω} [IsProbabilityMeasure Q] {Z : ℝ≥0 → Ω → ℝ}

/-- **The value over a finite schedule is the expected Snell envelope.** For a reward adapted to
the filtration sampled along the strictly increasing schedule `e` and integrable at its dates, the
continuous stopping value over the rules that stop only on the schedule is the expectation at `0`
of the Snell envelope of the sampled reward. -/
theorem stoppingValue_valuedIn_range_eq_integral_snellEnvelope (he : StrictMono e)
    (heT : e (Fin.last m) = T)
    (hZa : Adapted (ContinuousMarket.sampledFiltration 𝓕 (monotone_sampleTimes he.monotone))
      fun n ω ↦ Z (sampleTimes e n) ω)
    (hZi : ∀ n, Integrable (fun ω ↦ Z (sampleTimes e n) ω) Q) :
    stoppingValue Q 𝓕 Z T (StoppingRule.valuedIn 𝓕 T (Set.range e))
      = ∫ ω, snellEnvelope Q (ContinuousMarket.sampledFiltration 𝓕
          (monotone_sampleTimes he.monotone)) Set.univ (fun n ω ↦ Z (sampleTimes e n) ω) m 0 ω
          ∂Q :=
  (stoppingValue_valuedIn_range he heT Q Z).trans
    (stoppingValue_eq_integral_snellEnvelope hZa hZi m)

/-- **The value over a finite schedule is attained**: the Snell first-contact rule of the sampled
reward, read back in continuous time, stops on the schedule and earns the value. -/
theorem exists_mem_valuedIn_range_integral_eq_stoppingValue (he : StrictMono e)
    (heT : e (Fin.last m) = T)
    (hZa : Adapted (ContinuousMarket.sampledFiltration 𝓕 (monotone_sampleTimes he.monotone))
      fun n ω ↦ Z (sampleTimes e n) ω)
    (hZi : ∀ n, Integrable (fun ω ↦ Z (sampleTimes e n) ω) Q) :
    ∃ θ ∈ StoppingRule.valuedIn 𝓕 T (Set.range e),
      (∫ ω, Z (θ.time ω) ω ∂Q) = stoppingValue Q 𝓕 Z T (StoppingRule.valuedIn 𝓕 T (Set.range e)) :=
  ⟨_, ((sampledRuleEquiv 𝓕 he heT) (snellRule (P := Q) hZa m)).2,
    (snellRule_attains_value hZa hZi m).trans (stoppingValue_valuedIn_range he heT Q Z).symm⟩

end MathFin
