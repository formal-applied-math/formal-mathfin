/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Mathlib

/-!
# Admissible finite-horizon stopping rules

Rules are nonnegative, finite stopping times for an explicit filtration and
are bounded pointwise by the horizon. Measurability is derived from the
stopping-time condition, not added as a separate restriction.

## Result

Public entry points include `BoundedRule`, `measurable_time`, `constant`, `zero`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A stopping time for `𝓕` with values in `ℝ≥0`, bounded pointwise by the horizon `T`. -/
structure BoundedRule (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0) where
  /-- The time at which the rule stops. -/
  time : Ω → ℝ≥0
  stopping : IsStoppingTime 𝓕 (fun ω => (time ω : WithTop ℝ≥0))
  le_horizon : ∀ ω, time ω ≤ T

namespace BoundedRule

variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T U : ℝ≥0}

theorem measurable_time (θ : BoundedRule 𝓕 T) : Measurable θ.time := by
  apply measurable_of_Iic
  intro t
  apply 𝓕.le t
  simpa only [preimage,mem_Iic,WithTop.coe_le_coe] using θ.stopping t

/-- The deterministic rule that stops at the fixed time `s`, for `s ≤ T`. -/
def constant (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T s : ℝ≥0) (hs : s ≤ T) :
    BoundedRule 𝓕 T where
  time := fun _ => s
  stopping := isStoppingTime_const 𝓕 s
  le_horizon := fun _ => hs

/-- The rule that stops immediately, at time `0`. -/
def zero (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0) : BoundedRule 𝓕 T :=
  constant 𝓕 T 0 zero_le

instance : Nonempty (BoundedRule 𝓕 T) := ⟨zero 𝓕 T⟩

/-- The same stopping time, presented against a larger horizon `U ≥ T`. -/
def extend (θ : BoundedRule 𝓕 T) (hTU : T ≤ U) : BoundedRule 𝓕 U where
  time := θ.time
  stopping := θ.stopping
  le_horizon := fun ω => (θ.le_horizon ω).trans hTU

theorem time_eq_zero (θ : BoundedRule 𝓕 0) (ω : Ω) : θ.time ω = 0 :=
  le_antisymm (θ.le_horizon ω) zero_le

/-- Any ordinary `WithTop`-valued stopping time bounded by the finite horizon
has exactly the finite representation used here. No admissible finite-horizon
stopping rules are lost by using nonnegative real-valued times. -/
noncomputable def ofWithTop (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ)
    (hbound : ∀ ω, τ ω ≤ T) : BoundedRule 𝓕 T where
  time := fun ω => (τ ω).untop (ne_top_of_le_ne_top WithTop.coe_ne_top (hbound ω))
  stopping := by
    have he :
        (fun ω => ((τ ω).untop (ne_top_of_le_ne_top WithTop.coe_ne_top (hbound ω)) : WithTop ℝ≥0)) =
        τ := by
      funext ω
      exact WithTop.coe_untop _ _
    rw [he]
    exact hτ
  le_horizon := by
    intro ω
    exact_mod_cast
        (show ((τ ω).untop (ne_top_of_le_ne_top WithTop.coe_ne_top (hbound ω)) : WithTop ℝ≥0) ≤ T by
      simpa only [WithTop.coe_untop] using hbound ω)

theorem ofWithTop_coe_time (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ)
    (hbound : ∀ ω, τ ω ≤ T) (ω : Ω) : ((ofWithTop τ hτ hbound).time ω : WithTop ℝ≥0) = τ ω :=
  WithTop.coe_untop _ _

end BoundedRule

end MathFin.BlackScholes.AmericanPut.Stopping
