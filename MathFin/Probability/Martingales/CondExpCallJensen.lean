/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Init
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Conditional Jensen for the call payoff

Conditioning on less information lowers the expected call payoff:
`E[(E[X | m] − L)⁺] ≤ E[(X − L)⁺]` for an integrable `X` and a sub-σ-algebra `m`. This is
Mathlib's conditional Jensen inequality for the convex payoff `x ↦ (x − L)⁺`.

Two readings in the library. For a martingale `X` the call value `t ↦ E[(X_t − L)⁺]` is
non-decreasing (`integral_posPart_sub_mono_of_martingale` in
`Models/ModelFree/CalendarArbitrage`, the martingale half of the Gatheral–Jacquier calendar
condition). For overnight caplets it would order the forward-looking caplet below the
backward-looking one, once the rate fixed at the start of the accrual period is modelled as the
conditional expectation of the compounded rate; `Models/Rates/OvernightCompounding` does not
formalise that identification.

## Main results

* `integral_posPart_sub_condExp_le`: `E[(E[X | m] − L)⁺] ≤ E[(X − L)⁺]`.

## References

* [A. Lyashenko and F. Mercurio, *Looking forward to backward-looking rates: A modeling
  framework for term rates replacing LIBOR*][LyashenkoMercurio2019]
* [J. Gatheral and A. Jacquier, *Arbitrage-free SVI volatility surfaces*][GatheralJacquier2014],
  Lemma 2.1

## Tags

conditional Jensen inequality, call payoff, conditional expectation, convex order,
MSC 60G42, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory Set

/-- **Conditional Jensen for the call payoff.** For an integrable `X` on a finite measure space
and a sub-σ-algebra `m`, `E[(E[X | m] − L)⁺] ≤ E[(X − L)⁺]`: the level-`L` call on the
conditional expectation is worth at most the call on `X`. -/
theorem integral_posPart_sub_condExp_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X : Ω → ℝ}
    (hX : Integrable X μ) (L : ℝ) :
    ∫ ω, (μ[X | m] ω - L)⁺ ∂μ ≤ ∫ ω, (X ω - L)⁺ ∂μ := by
  set φ : ℝ → ℝ := fun x ↦ (x - L)⁺
  have hcvx : ConvexOn ℝ univ φ :=
    ((convexOn_id convex_univ).sub (concaveOn_const L convex_univ)).sup
      (convexOn_const 0 convex_univ)
  have hφint : Integrable (φ ∘ X) μ := (hX.sub (integrable_const L)).pos_part
  have hJ := hcvx.map_condExp_le hm
    ((show Continuous φ by fun_prop).lowerSemicontinuous.lowerSemicontinuousOn univ)
    (by simp) isClosed_univ hX hφint
  calc ∫ ω, (μ[X | m] ω - L)⁺ ∂μ ≤ ∫ ω, (μ[φ ∘ X | m]) ω ∂μ :=
        integral_mono_ae (((integrable_condExp (m := m)).sub (integrable_const L)).pos_part)
          integrable_condExp hJ
    _ = ∫ ω, (X ω - L)⁺ ∂μ := integral_condExp hm

end MathFin
