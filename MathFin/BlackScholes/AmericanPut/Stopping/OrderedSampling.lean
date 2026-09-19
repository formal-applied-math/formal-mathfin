/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.Verification

/-! # Ordered bounded continuous-time optional sampling 
## Result

Public entry points include `BoundedRule.minimum`, `expected_gridValue_tendsto`, `expected_stoppedValue_le_of_le`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The pointwise minimum `fun ω => min (θ.time ω) (η.time ω)` of two rules with horizon `T`. -/
def BoundedRule.minimum {T : ℝ≥0} (θ η : BoundedRule 𝓕 T) : BoundedRule 𝓕 T where
  time := fun ω => min (θ.time ω) (η.time ω)
  stopping := by
    intro t
    convert! (θ.stopping t).union (η.stopping t) using 1
    ext ω
    simp only [mem_ofPred_eq,WithTop.coe_le_coe,min_le_iff,mem_union]
  le_horizon := fun ω => (min_le_left _ _).trans (θ.le_horizon ω)

theorem expected_gridValue_tendsto {P : Measure Ω} [IsFiniteMeasure P] {U : ℝ≥0 → Ω → ℝ}
    (hU : Supermartingale U 𝓕 P) (hc : ∀ ω, Continuous (fun t => U t ω))
    {C : ℝ} (hb : ∀ t ω, ‖U t ω‖ ≤ C) {T : ℝ≥0} (θ : BoundedRule 𝓕 T) :
    Tendsto (fun n => ∫ ω, U ((gridIndex θ (gridStep n) ω : ℝ≥0)*gridStep n) ω ∂P)
      atTop (𝓝 (∫ ω, U (θ.time ω) ω ∂P)) := by
  have hm : Measurable U.uncurry := measurable_uncurry_of_continuous_of_measurable hc
    (fun t => (hU.stronglyAdapted t).measurable.mono (𝓕.le t) le_rfl)
  exact tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (hm.comp ((show Measurable (fun ω =>
      (gridIndex θ (gridStep n) ω : ℝ≥0)*gridStep n) by
        exact ((measurable_from_nat : Measurable (fun i : ℕ => (i : ℝ≥0))).comp
          (gridIndex_measurable θ)).mul_const _).prodMk measurable_id)).aestronglyMeasurable)
    (integrable_const C) (fun _ => Eventually.of_forall (fun ω => hb _ ω))
    (Eventually.of_forall (fun ω => ((hc ω).tendsto (θ.time ω)).comp (gridValue_time_tendsto θ ω)))

theorem expected_stoppedValue_le_of_le {P : Measure Ω} [IsFiniteMeasure P] {U : ℝ≥0 → Ω → ℝ}
    (hU : Supermartingale U 𝓕 P) (hc : ∀ ω, Continuous (fun t => U t ω))
    {C : ℝ} (hb : ∀ t ω, ‖U t ω‖ ≤ C) {T : ℝ≥0}
    (θ η : BoundedRule 𝓕 T) (hθη : ∀ ω, θ.time ω ≤ η.time ω) :
    (∫ ω, U (η.time ω) ω ∂P) ≤ ∫ ω, U (θ.time ω) ω ∂P := by
  apply le_of_tendsto_of_tendsto (expected_gridValue_tendsto hU hc hb η)
    (expected_gridValue_tendsto hU hc hb θ)
  apply Eventually.of_forall
  intro n
  have hh := (supermartingale_grid hU (gridStep n)).neg.expected_stoppedValue_mono
    (gridIndex_stopping θ (gridStep_pos n)) (gridIndex_stopping η (gridStep_pos n))
    (fun ω => show (gridIndex θ (gridStep n) ω : ℕ∞) ≤ (gridIndex η (gridStep n) ω : ℕ∞) by
      exact_mod_cast (Nat.ceil_mono (div_le_div_of_nonneg_right (hθη ω) zero_le)))
    (fun ω => show (gridIndex η (gridStep n) ω : ℕ∞) ≤ (⌈T/gridStep n⌉₊ : ℕ) by
      exact_mod_cast gridIndex_bounded η ω)
  simpa [stoppedValue,integral_neg] using hh

end MathFin.BlackScholes.AmericanPut.Stopping
