/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Instruments.Options

/-!
# The forward and put–call parity in every risk-neutral model

`Contracts/Instruments/Options.lean` proves that a call pays a put plus a forward on every path,
so in every model the call's value is the put's plus the forward's. This file prices the
forward without choosing a model. Only one fact about the model is used: the discounted
underlying at maturity is integrable with mean `S₀`. Then the forward struck at `K` is worth
`S₀ − K D(T)` (`value_forward_of_integral`), and the call is worth the put plus
`S₀ − K D(T)` (`value_europeanCall_sub_put_of_integral`). The put's integrability comes from
the underlying's.

That fact holds in every model whose discounted price `t ↦ D(t) X(t)` is a `Q`-martingale
starting from the constant `S₀`, with `D(0) = 1` (`integral_discounted_of_martingale`). This is
the risk-neutral condition of `ContinuousMarket.IsEMM`, which asks for the martingale and also
for `Q ≈ P`; only the martingale is needed here. In that case neither the forward nor the
parity takes an integrability hypothesis (`value_forward_of_martingale`,
`value_europeanCall_sub_put_of_martingale`).

The Black–Scholes forward (`BlackScholes.value_forward`) is an instance of the first form.

## Main results

* `value_forward_of_integral`, `value_forward_of_martingale` — the forward is worth `S₀ − K D(T)`.
* `value_europeanCall_sub_put_of_integral`, `value_europeanCall_sub_put_of_martingale` —
  call minus put is `S₀ − K D(T)`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {D : ℝ≥0 → ℝ}
  {X : Unit → ℝ≥0 → Ω → ℝ} {S₀ K : ℝ} {T : ℝ≥0}

/-- The forward's discounted payoff is integrable whenever the discounted underlying is. -/
theorem integrable_forward_pathPV [IsFiniteMeasure Q]
    (hX : Integrable (fun ω ↦ D T * X () T ω) Q) :
    Integrable (fun ω ↦ (forward K T).pathPV D (scenarioAt X ω)) Q := by
  simp only [forward, Contract.pathPV, Contract.cashflows, Payoff.eval, scenarioAt,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_sub]
  exact hX.sub (integrable_const _)

/-- The put's discounted payoff is integrable whenever the discounted underlying is. -/
theorem integrable_europeanPut_pathPV [IsFiniteMeasure Q]
    (hX : Integrable (fun ω ↦ D T * X () T ω) Q) :
    Integrable (fun ω ↦ (europeanPut K T).pathPV D (scenarioAt X ω)) Q := by
  simp only [europeanPut, Contract.pathPV, Contract.cashflows, Payoff.eval, scenarioAt,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rcases eq_or_ne (D T) 0 with hD | hD
  · simp [hD]
  · have hXT : Integrable (X () T) Q := by
      simpa [← mul_assoc, inv_mul_cancel₀ hD] using hX.const_mul (D T)⁻¹
    exact ((integrable_const K).sub hXT).pos_part.const_mul _

/-- **The forward's value in any model** in which the discounted underlying at `T` is integrable
with mean `S₀`: the forward struck at `K` is worth `S₀ − K D(T)`. -/
theorem value_forward_of_integral [IsProbabilityMeasure Q]
    (hX : Integrable (fun ω ↦ D T * X () T ω) Q) (hS₀ : ∫ ω, D T * X () T ω ∂Q = S₀) :
    (forward K T).value Q D X = S₀ - K * D T := by
  rw [forward, Contract.value_pay]
  simp only [Payoff.eval, scenarioAt, mul_sub]
  rw [integral_sub hX (integrable_const _), hS₀, integral_const, probReal_univ, one_smul]
  ring

/-- **Put–call parity in closed form, in any model** in which the discounted underlying at `T`
is integrable with mean `S₀`: `C − P = S₀ − K D(T)`. No integrability of either option is
assumed; the put's follows from the underlying's. -/
theorem value_europeanCall_sub_put_of_integral [IsProbabilityMeasure Q]
    (hX : Integrable (fun ω ↦ D T * X () T ω) Q) (hS₀ : ∫ ω, D T * X () T ω ∂Q = S₀) :
    (europeanCall K T).value Q D X - (europeanPut K T).value Q D X = S₀ - K * D T := by
  rw [value_europeanCall_eq_put_add_forward Q D X (integrable_europeanPut_pathPV hX)
    (integrable_forward_pathPV hX), value_forward_of_integral hX hS₀]
  ring

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- **A martingale keeps its starting mean.** If the discounted price `t ↦ D(t) X(t)` is a
`Q`-martingale, `D(0) = 1` and the price starts at the constant `S₀`, then the discounted price
at every `T` has mean `S₀`. -/
theorem integral_discounted_of_martingale [IsProbabilityMeasure Q]
    (hM : Martingale (fun t ω ↦ D t * X () t ω) 𝓕 Q) (hD₀ : D 0 = 1)
    (hX₀ : ∀ ω, X () 0 ω = S₀) (T : ℝ≥0) :
    ∫ ω, D T * X () T ω ∂Q = S₀ := by
  rw [← integral_condExp (𝓕.le 0), integral_congr_ae (hM.condExp_ae_eq (zero_le (a := T)))]
  simp [hD₀, hX₀]

/-- **The forward's value in any risk-neutral model.** If the discounted price is a
`Q`-martingale starting from `S₀`, with `D(0) = 1`, the forward struck at `K` is worth
`S₀ − K D(T)`. -/
theorem value_forward_of_martingale [IsProbabilityMeasure Q]
    (hM : Martingale (fun t ω ↦ D t * X () t ω) 𝓕 Q) (hD₀ : D 0 = 1)
    (hX₀ : ∀ ω, X () 0 ω = S₀) :
    (forward K T).value Q D X = S₀ - K * D T :=
  value_forward_of_integral (hM.integrable T) (integral_discounted_of_martingale hM hD₀ hX₀ T)

/-- **Put–call parity in every risk-neutral model**, with no integrability hypotheses. If the
discounted price is a `Q`-martingale starting from `S₀`, with `D(0) = 1`, then
`C − P = S₀ − K D(T)`. -/
theorem value_europeanCall_sub_put_of_martingale [IsProbabilityMeasure Q]
    (hM : Martingale (fun t ω ↦ D t * X () t ω) 𝓕 Q) (hD₀ : D 0 = 1)
    (hX₀ : ∀ ω, X () 0 ω = S₀) :
    (europeanCall K T).value Q D X - (europeanPut K T).value Q D X = S₀ - K * D T :=
  value_europeanCall_sub_put_of_integral (hM.integrable T)
    (integral_discounted_of_martingale hM hD₀ hX₀ T)

end MathFin.Contracts
