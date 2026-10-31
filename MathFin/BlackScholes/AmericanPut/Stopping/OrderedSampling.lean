/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.Verification

/-! # Ordered bounded continuous-time optional sampling 
## Result

Public entry points include `expected_stoppedValue_le_of_le`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem expected_stoppedValue_le_of_le {P : Measure Ω} [IsFiniteMeasure P] {U : ℝ≥0 → Ω → ℝ}
    (hU : Supermartingale U 𝓕 P) (hc : ∀ ω, Continuous (fun t => U t ω))
    {C : ℝ} (hb : ∀ t ω, ‖U t ω‖ ≤ C) {T : ℝ≥0}
    (θ η : StoppingRule 𝓕 T) (hθη : ∀ ω, θ.time ω ≤ η.time ω) :
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
