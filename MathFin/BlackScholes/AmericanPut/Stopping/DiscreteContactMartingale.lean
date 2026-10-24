/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FiniteBellman

/-! # Stopping a discrete process when its conditional drift first becomes nonzero 
## Result

Public entry points include `discrete_stopped_martingale_of_before`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {U : ℕ → Ω → ℝ} {τ : Ω → ℕ}

theorem discrete_stopped_martingale_of_before
    (ha : StronglyAdapted 𝓕 U) (hi : ∀ i, Integrable (U i) P)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ)))
    (hbefore : ∀ i ω, i < τ ω → P[U (i + 1) | 𝓕 i] ω = U i ω) :
    Martingale (stoppedProcess U (fun ω => (τ ω : WithTop ℕ))) 𝓕 P := by
  apply martingale_of_condExp_sub_eq_zero_nat (ha.stoppedProcess_of_discrete hτ)
    (fun i => integrable_stoppedValue ℕ ((isStoppingTime_const 𝓕 i).min hτ) hi
      (fun _ => min_le_left _ _))
  intro i
  let A : Set Ω := {ω | i < τ ω}
  have hA : MeasurableSet[𝓕 i] A := by
    convert! (hτ i).compl using 1
    ext ω
    simp [A]
  have he : stoppedProcess U (fun ω => (τ ω : WithTop ℕ)) (i+1)-
      stoppedProcess U (fun ω => (τ ω : WithTop ℕ)) i = A.indicator (U (i+1)-U i) := by
    ext ω
    change U (min (i+1) (τ ω)) ω-U (min i (τ ω)) ω = _
    by_cases ht : i < τ ω
    · simp [A,ht,min_eq_left ht.le]
    · have ht' : τ ω ≤ i := le_of_not_gt ht
      simp [A,ht,min_eq_right ht',min_eq_right (ht'.trans (Nat.le_succ i))]
  rw [he]
  have hc := condExp_indicator (m := 𝓕 i) ((hi (i+1)).sub (hi i)) hA
  have hs := condExp_sub (hi (i+1)) (hi i) (𝓕 i)
  rw [condExp_of_stronglyMeasurable (𝓕.le i) (ha i) (hi i)] at hs
  filter_upwards [hc,hs] with ω hc hs
  rw [hc]
  by_cases hω : ω ∈ A
  · rw [indicator_of_mem hω,hs]
    exact sub_eq_zero.mpr (hbefore i ω hω)
  · exact indicator_of_notMem hω _

end MathFin.BlackScholes.AmericanPut.Stopping
