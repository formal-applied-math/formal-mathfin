/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
import MathFin

/-!
# Sampled stopping values on a two-point space

Two-date optimal-stopping examples over `Bool` with fair weights, exercising
the sampled stopping value leaf (`MathFin.sampledStoppingValue_eq_and_attained`):
the discrete stopping value is the expected all-index Snell envelope, attained
by an explicit rule.

* `value_terminalReward`: with `Z 0 = 0` and `Z 1 = 1` the value is `1`
  (waiting for the mandatory terminal date is optimal).
* `value_earlyReward`: stopping at the first date (payoff `3 / 2`) beats
  waiting for the terminal date (expected payoff `1`); the value is `3 / 2`.
-/

open MeasureTheory MathFin

namespace MathFinTest.FiniteSampledValue

/-- Information arrives at date 1: nothing known at 0, everything after. -/
def infoFiltration : Filtration ℕ (inferInstance : MeasurableSpace Bool) where
  seq := fun n => if n = 0 then ⊥ else inferInstance
  mono' := by
    intro i j hij
    cases i with
    | zero => exact bot_le
    | succ i =>
      cases j with
      | zero => exact absurd hij (by omega)
      | succ j => exact le_rfl
  le' := by
    intro n
    cases n with
    | zero => exact bot_le
    | succ n => exact le_rfl

theorem infoFiltration_zero : infoFiltration 0 = ⊥ := rfl

theorem infoFiltration_succ (n : ℕ) : infoFiltration (Nat.succ n) = ⊤ := rfl

/-- Fair weights on two points. -/
noncomputable def fairWeights : Bool → ℝ := fun _ => 1 / 2

theorem fairWeights_nonneg : ∀ i ∈ Finset.univ, 0 ≤ fairWeights i := by
  intro i _
  change (0 : ℝ) ≤ 1 / 2
  norm_num

theorem fairWeights_sum : ∑ i ∈ Finset.univ, fairWeights i = 1 := by
  simp only [fairWeights, Fintype.univ_bool,
    Finset.sum_pair (by decide : (true : Bool) ≠ false)]
  norm_num

/-- Every real function on `Bool` is integrable for a finite measure. -/
theorem integrableOnBool {P : Measure Bool} [IsFiniteMeasure P] (f : Bool → ℝ) :
    Integrable f P :=
  integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)

/-- Mandatory-terminal reward: nothing at date 0, one at every later date. -/
def terminalReward : ℕ → Bool → ℝ := fun n _ => if n = 0 then 0 else 1

theorem terminalReward_zero (ω : Bool) : terminalReward 0 ω = 0 := rfl

theorem terminalReward_succ (ω : Bool) : terminalReward 1 ω = 1 := rfl

theorem integral_terminalReward_one :
    (∫ ω, terminalReward 1 ω ∂Measure.ofWeights Finset.univ fairWeights) = 1 := by
  rw [Measure.integral_ofWeights Finset.univ fairWeights_nonneg]
  simp only [fairWeights, terminalReward_succ, Fintype.univ_bool,
    Finset.sum_pair (by decide : (true : Bool) ≠ false)]
  norm_num

/-- Early-exercise reward: `3 / 2` at date 0, a fair coin flip later. -/
noncomputable def earlyReward : ℕ → Bool → ℝ :=
  fun n ω => if n = 0 then 3 / 2 else if ω then 2 else 0

theorem earlyReward_zero (ω : Bool) : earlyReward 0 ω = 3 / 2 := rfl

theorem earlyReward_one_true : earlyReward 1 true = 2 := rfl

theorem earlyReward_one_false : earlyReward 1 false = 0 := rfl

theorem integral_earlyReward_zero :
    (∫ ω, earlyReward 0 ω ∂Measure.ofWeights Finset.univ fairWeights) = 3 / 2 := by
  rw [Measure.integral_ofWeights Finset.univ fairWeights_nonneg]
  simp only [fairWeights, earlyReward_zero, Fintype.univ_bool,
    Finset.sum_pair (by decide : (true : Bool) ≠ false)]
  norm_num

theorem integral_earlyReward_one :
    (∫ ω, earlyReward 1 ω ∂Measure.ofWeights Finset.univ fairWeights) = 1 := by
  rw [Measure.integral_ofWeights Finset.univ fairWeights_nonneg]
  simp only [fairWeights, Fintype.univ_bool,
    Finset.sum_pair (by decide : (true : Bool) ≠ false),
    earlyReward_one_true, earlyReward_one_false]
  norm_num

/-- The rule stopping immediately at date 0. -/
def stopNow : StoppingRule infoFiltration 1 :=
  StoppingRule.constant infoFiltration 1 0 (by omega)

/-- The rule waiting until the terminal date 1. -/
def stopTerminal : StoppingRule infoFiltration 1 :=
  StoppingRule.constant infoFiltration 1 1 le_rfl

theorem payoff_terminalReward :
    (∫ ω, terminalReward (stopTerminal.time ω) ω
      ∂Measure.ofWeights Finset.univ fairWeights) = 1 := by
  change (∫ ω, terminalReward 1 ω ∂Measure.ofWeights Finset.univ fairWeights) = 1
  exact integral_terminalReward_one

theorem payoff_earlyReward_now :
    (∫ ω, earlyReward (stopNow.time ω) ω
      ∂Measure.ofWeights Finset.univ fairWeights) = 3 / 2 := by
  change (∫ ω, earlyReward 0 ω ∂Measure.ofWeights Finset.univ fairWeights) = 3 / 2
  exact integral_earlyReward_zero

theorem payoff_earlyReward_terminal :
    (∫ ω, earlyReward (stopTerminal.time ω) ω
      ∂Measure.ofWeights Finset.univ fairWeights) = 1 := by
  change (∫ ω, earlyReward 1 ω ∂Measure.ofWeights Finset.univ fairWeights) = 1
  exact integral_earlyReward_one

/-- Mandatory terminal: with `Z 0 = 0` and `Z 1 = 1` the value is `1`. -/
theorem value_terminalReward :
    stoppingValue (Measure.ofWeights Finset.univ fairWeights) infoFiltration
        terminalReward 1 = 1 := by
  have := Measure.isProbabilityMeasure_ofWeights fairWeights_nonneg
    fairWeights_sum
  have hC : ∀ θ ∈ (Set.univ : Set (StoppingRule infoFiltration 1)),
      (∫ ω, terminalReward (θ.time ω) ω
        ∂Measure.ofWeights Finset.univ fairWeights) ≤ 1 := by
    intro θ _
    have hle := θ.le_horizon
    have hpoint : ∀ ω, terminalReward (θ.time ω) ω ≤ 1 := by
      intro ω
      have h := hle ω
      have h01 : θ.time ω = 0 ∨ θ.time ω = 1 := by omega
      rcases h01 with h0 | h1
      · rw [h0, terminalReward_zero ω]
        norm_num
      · rw [h1, terminalReward_succ ω]
    have hIf : Integrable (fun ω => terminalReward (θ.time ω) ω)
        (Measure.ofWeights Finset.univ fairWeights) := integrableOnBool _
    have hI := integral_mono hIf (integrable_const 1) hpoint
    have h1 : (∫ _ : Bool, (1 : ℝ)
        ∂Measure.ofWeights Finset.univ fairWeights) = 1 := by
      rw [Measure.integral_ofWeights Finset.univ fairWeights_nonneg]
      simp only [fairWeights, Fintype.univ_bool,
        Finset.sum_pair (by decide : (true : Bool) ≠ false)]
      norm_num
    exact hI.trans h1.le
  apply le_antisymm
  · exact stoppingValue_le Set.univ_nonempty hC
  · have h := integral_le_stoppingValue hC (Set.mem_univ stopTerminal)
    rw [payoff_terminalReward] at h
    exact h

/-- The Snell envelope expectation agrees with the mandatory-terminal value. -/
theorem snell_terminalReward :
    (∫ ω, snellEnvelope (Measure.ofWeights Finset.univ fairWeights) infoFiltration
        Set.univ terminalReward 1 0 ω
        ∂Measure.ofWeights Finset.univ fairWeights) = 1 := by
  have := Measure.isProbabilityMeasure_ofWeights fairWeights_nonneg
    fairWeights_sum
  have ha : Adapted infoFiltration terminalReward := by
    intro n
    cases n with
    | zero =>
      change Measurable[infoFiltration 0] (fun _ : Bool => (0 : ℝ))
      exact measurable_const
    | succ n =>
      change Measurable[infoFiltration (Nat.succ n)] (fun _ : Bool => (1 : ℝ))
      exact measurable_const
  have hi : ∀ n, Integrable (terminalReward n)
      (Measure.ofWeights Finset.univ fairWeights) := fun n => integrableOnBool _
  have h := stoppingValue_eq_integral_snellEnvelope ha hi 1
  rw [value_terminalReward] at h
  exact h.symm

/-- The mandatory-terminal value is attained by waiting. -/
theorem attained_terminalReward :
    ∃ θ ∈ (Set.univ : Set (StoppingRule infoFiltration 1)),
      (∫ ω, terminalReward (θ.time ω) ω
        ∂Measure.ofWeights Finset.univ fairWeights)
        = stoppingValue (Measure.ofWeights Finset.univ fairWeights) infoFiltration
          terminalReward 1 := by
  refine ⟨stopTerminal, Set.mem_univ _, ?_⟩
  rw [payoff_terminalReward, value_terminalReward]

/-- Early exercise: stopping at date 0 beats waiting; the value is `3 / 2`. -/
theorem value_earlyReward :
    stoppingValue (Measure.ofWeights Finset.univ fairWeights) infoFiltration
        earlyReward 1 = 3 / 2 := by
  have := Measure.isProbabilityMeasure_ofWeights fairWeights_nonneg
    fairWeights_sum
  have hC : ∀ θ ∈ (Set.univ : Set (StoppingRule infoFiltration 1)),
      (∫ ω, earlyReward (θ.time ω) ω
        ∂Measure.ofWeights Finset.univ fairWeights) ≤ 3 / 2 := by
    intro θ _
    have h0 : MeasurableSet[⊥]
        {ω : Bool | ((θ.time ω : ℕ) : WithTop ℕ) ≤ ((0 : ℕ) : WithTop ℕ)} := by
      have h := θ.stopping 0
      rw [infoFiltration_zero] at h
      exact h
    obtain h | h := MeasurableSpace.measurableSet_bot_iff.mp h0
    · have htime : ∀ ω, θ.time ω = 1 := by
        intro ω
        have hle := θ.le_horizon ω
        have hnot : ¬ θ.time ω ≤ 0 := by
          intro hle0
          have hmem : ω ∈ {ω : Bool | ((θ.time ω : ℕ) : WithTop ℕ)
              ≤ ((0 : ℕ) : WithTop ℕ)} :=
            WithTop.coe_le_coe.mpr hle0
          rw [h] at hmem
          exact absurd hmem (Set.notMem_empty ω)
        omega
      have hInt : (∫ ω, earlyReward (θ.time ω) ω
          ∂Measure.ofWeights Finset.univ fairWeights)
          = ∫ ω, earlyReward 1 ω ∂Measure.ofWeights Finset.univ fairWeights := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω => by simp only [htime ω]
      rw [hInt, integral_earlyReward_one]
      norm_num
    · have htime : ∀ ω, θ.time ω = 0 := by
        intro ω
        have hmem : ω ∈ {ω : Bool | ((θ.time ω : ℕ) : WithTop ℕ)
            ≤ ((0 : ℕ) : WithTop ℕ)} := by
          rw [h]
          exact Set.mem_univ ω
        have hle0 : θ.time ω ≤ 0 := WithTop.coe_le_coe.mp hmem
        omega
      have hInt : (∫ ω, earlyReward (θ.time ω) ω
          ∂Measure.ofWeights Finset.univ fairWeights)
          = ∫ ω, earlyReward 0 ω ∂Measure.ofWeights Finset.univ fairWeights := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω => by simp only [htime ω]
      rw [hInt, integral_earlyReward_zero]
  apply le_antisymm
  · exact stoppingValue_le Set.univ_nonempty hC
  · have h := integral_le_stoppingValue hC (Set.mem_univ stopNow)
    rw [payoff_earlyReward_now] at h
    exact h

/-- Stopping at the first date beats waiting for the terminal date. -/
theorem earlyBeatsWaiting :
    (∫ ω, earlyReward (stopTerminal.time ω) ω
      ∂Measure.ofWeights Finset.univ fairWeights)
      < (∫ ω, earlyReward (stopNow.time ω) ω
        ∂Measure.ofWeights Finset.univ fairWeights) := by
  rw [payoff_earlyReward_terminal, payoff_earlyReward_now]
  norm_num

/-- The Snell envelope expectation agrees with the early-exercise value. -/
theorem snell_earlyReward :
    (∫ ω, snellEnvelope (Measure.ofWeights Finset.univ fairWeights) infoFiltration
        Set.univ earlyReward 1 0 ω
        ∂Measure.ofWeights Finset.univ fairWeights) = 3 / 2 := by
  have := Measure.isProbabilityMeasure_ofWeights fairWeights_nonneg
    fairWeights_sum
  have ha : Adapted infoFiltration earlyReward := by
    intro n
    cases n with
    | zero =>
      change Measurable[infoFiltration 0] (fun _ : Bool => (3 / 2 : ℝ))
      exact measurable_const
    | succ n =>
      rw [infoFiltration_succ]
      exact measurable_from_top
  have hi : ∀ n, Integrable (earlyReward n)
      (Measure.ofWeights Finset.univ fairWeights) := fun n => integrableOnBool _
  have h := stoppingValue_eq_integral_snellEnvelope ha hi 1
  rw [value_earlyReward] at h
  exact h.symm

/-- The early-exercise value is attained by stopping at date 0. -/
theorem attained_earlyReward :
    ∃ θ ∈ (Set.univ : Set (StoppingRule infoFiltration 1)),
      (∫ ω, earlyReward (θ.time ω) ω
        ∂Measure.ofWeights Finset.univ fairWeights)
        = stoppingValue (Measure.ofWeights Finset.univ fairWeights) infoFiltration
          earlyReward 1 := by
  refine ⟨stopNow, Set.mem_univ _, ?_⟩
  rw [payoff_earlyReward_now, value_earlyReward]

end MathFinTest.FiniteSampledValue
