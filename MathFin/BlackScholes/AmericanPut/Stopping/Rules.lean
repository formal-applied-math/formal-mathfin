/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Mathlib

/-!
# Admissible stopping rules and the value of an optimal stopping problem

A stopping rule with horizon `T` over an ordered index `ι` is a finite stopping time for an
explicit filtration, bounded pointwise by `T`. It is the same object whether time is `ℝ≥0`
(continuous-time exercise), `ℕ` (a Bermudan or Bellman tower) or any other index. Measurability
is derived from the stopping-time condition, not added as a separate restriction.

`stoppingValue` is the supremum of the expected stopped payoff `∫ Z (θ ω) ω ∂P` over a class `R`
of rules (all rules by default), so the continuous-time American value, the discrete
stopping value and the value over a finite exercise grid are this one definition at different
payoffs, indices and classes. As a bare `sSup` it is `0` for an empty class or an unbounded set
of expected payoffs; the lemmas carry the nonemptiness, integrability and bound they need.

## Result

Public entry points include `StoppingRule`, `StoppingRule.measurable_time`, `stoppingValue`,
`integral_le_stoppingValue`, `stoppingValue_le`, `exists_lt_of_lt_stoppingValue`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [LinearOrder ι]

/-- A stopping time for `𝓕` with values in the index `ι` (never `⊤`), bounded pointwise by the
horizon `T`. Over `ι = ℝ≥0` these are exactly the `WithTop ℝ≥0`-valued stopping times bounded by
`T` (`StoppingRule.ofWithTop`). -/
structure StoppingRule (𝓕 : Filtration ι ‹MeasurableSpace Ω›) (T : ι) where
  /-- The time at which the rule stops. -/
  time : Ω → ι
  stopping : IsStoppingTime 𝓕 (fun ω => (time ω : WithTop ι))
  le_horizon : ∀ ω, time ω ≤ T

namespace StoppingRule

variable {𝓕 : Filtration ι ‹MeasurableSpace Ω›} {T U : ι}

theorem measurable_time [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    [MeasurableSpace ι] [BorelSpace ι] (θ : StoppingRule 𝓕 T) : Measurable θ.time := by
  apply measurable_of_Iic
  intro t
  apply 𝓕.le t
  simpa only [preimage,mem_Iic,WithTop.coe_le_coe] using θ.stopping t

/-- The deterministic rule that stops at the fixed time `s`, for `s ≤ T`. -/
def constant (𝓕 : Filtration ι ‹MeasurableSpace Ω›) (T s : ι) (hs : s ≤ T) :
    StoppingRule 𝓕 T where
  time := fun _ => s
  stopping := isStoppingTime_const 𝓕 s
  le_horizon := fun _ => hs

section Zero

variable [AddMonoid ι] [CanonicallyOrderedAdd ι]

/-- The rule that stops immediately, at time `0`. -/
def zero (𝓕 : Filtration ι ‹MeasurableSpace Ω›) (T : ι) : StoppingRule 𝓕 T :=
  constant 𝓕 T 0 zero_le

instance : Nonempty (StoppingRule 𝓕 T) := ⟨zero 𝓕 T⟩

theorem time_eq_zero (θ : StoppingRule 𝓕 0) (ω : Ω) : θ.time ω = 0 :=
  le_antisymm (θ.le_horizon ω) zero_le

end Zero

/-- The same stopping time, presented against a larger horizon `U ≥ T`. -/
def extend (θ : StoppingRule 𝓕 T) (hTU : T ≤ U) : StoppingRule 𝓕 U where
  time := θ.time
  stopping := θ.stopping
  le_horizon := fun ω => (θ.le_horizon ω).trans hTU

/-- Any ordinary `WithTop`-valued stopping time bounded by the finite horizon
has exactly the finite representation used here. No admissible finite-horizon
stopping rules are lost by using index-valued times. -/
noncomputable def ofWithTop (τ : Ω → WithTop ι) (hτ : IsStoppingTime 𝓕 τ)
    (hbound : ∀ ω, τ ω ≤ T) : StoppingRule 𝓕 T where
  time := fun ω => (τ ω).untop (ne_top_of_le_ne_top WithTop.coe_ne_top (hbound ω))
  stopping := by simpa only [WithTop.coe_untop] using hτ
  le_horizon ω := WithTop.coe_le_coe.mp ((WithTop.coe_untop _ _).le.trans (hbound ω))

theorem ofWithTop_coe_time (τ : Ω → WithTop ι) (hτ : IsStoppingTime 𝓕 τ)
    (hbound : ∀ ω, τ ω ≤ T) (ω : Ω) : ((ofWithTop τ hτ hbound).time ω : WithTop ι) = τ ω :=
  WithTop.coe_untop _ _

/-- The rules whose stopping times take values in `G`. -/
def valuedIn (𝓕 : Filtration ι ‹MeasurableSpace Ω›) (T : ι) (G : Set ι) :
    Set (StoppingRule 𝓕 T) :=
  {θ | ∀ ω, θ.time ω ∈ G}

end StoppingRule

/-- The value of the stopping problem with payoff `Z`: the supremum of the expected stopped payoff
`∫ Z (θ.time ω) ω ∂P` over a class `R` of rules with horizon `T` (all of them by default). With
`Z` a payoff process, the integrand is Mathlib's `stoppedValue Z θ.time` (definitionally).

This is Mathlib's junk-valued `sSup` and Bochner integral: it is the optimal-stopping value only
when `R` is nonempty and the expected payoffs are integrable and bounded above, which is exactly
what `integral_le_stoppingValue` and `stoppingValue_le` assume. -/
noncomputable def stoppingValue (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (Z : ι → Ω → ℝ) (T : ι) (R : Set (StoppingRule 𝓕 T) := univ) : ℝ :=
  sSup ((fun θ : StoppingRule 𝓕 T => ∫ ω, Z (θ.time ω) ω ∂P) '' R)

variable {P : Measure Ω} {𝓕 : Filtration ι ‹MeasurableSpace Ω›} {Z : ι → Ω → ℝ} {T : ι}
  {R : Set (StoppingRule 𝓕 T)}

theorem integral_le_stoppingValue {C : ℝ} (hC : ∀ η ∈ R, (∫ ω, Z (η.time ω) ω ∂P) ≤ C)
    {θ : StoppingRule 𝓕 T} (hθ : θ ∈ R) :
    (∫ ω, Z (θ.time ω) ω ∂P) ≤ stoppingValue P 𝓕 Z T R :=
  le_csSup ⟨C,by rintro _ ⟨η,hη,rfl⟩; exact hC η hη⟩ ⟨θ,hθ,rfl⟩

theorem stoppingValue_le {C : ℝ} (hR : R.Nonempty)
    (hC : ∀ θ ∈ R, (∫ ω, Z (θ.time ω) ω ∂P) ≤ C) : stoppingValue P 𝓕 Z T R ≤ C :=
  csSup_le (hR.image _) (by rintro _ ⟨θ,hθ,rfl⟩; exact hC θ hθ)

theorem exists_lt_of_lt_stoppingValue {a : ℝ} (h : a < stoppingValue P 𝓕 Z T R)
    (hR : R.Nonempty) : ∃ θ ∈ R, a < ∫ ω, Z (θ.time ω) ω ∂P := by
  obtain ⟨_,⟨θ,hθ,rfl⟩,h⟩ := exists_lt_of_lt_csSup (hR.image _) h
  exact ⟨θ,hθ,h⟩

end MathFin.BlackScholes.AmericanPut.Stopping
