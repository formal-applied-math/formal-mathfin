/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Core
public import MathFin.Markets.DeFi.UniswapMechanics
public import MathFin.Pricing.Market

/-!
# Liquidity positions as payoffs

A fee-free automated-market-maker position is a function of the price `P` of token X in token Y at
the date it is read, so it is a `Contracts.Payoff` on the single underlying `()`, and paying it at
`T` is a `Contract`. Both positions are functions of `√P`, which is the `rpow` of the payoff
language with exponent `1/2`:

* the constant-product position with invariant `k = x₀ y₀` is worth `2 √k √P` in token Y
  (`lpPortfolioValue_eq`: `2 y₀ √r` at the price ratio `r = P x₀ / y₀`);
* the concentrated-liquidity position with liquidity `L` on the square-root range `[a, b]` is worth
  `v3PositionValue L a b (√P)`, which is `L (2u − a − u²/b) + L (1/a − 1/b) (m² − a²)` for
  `u = max a (min √P b)` and `m = min √P a`: concave inside the range, the quadratic
  `L (1/a − 1/b) P` below it, constant above.

## Main definitions

* `constantProductPayoff`: the constant-product position as a payoff.
* `lpPayoff`: the concentrated-liquidity position as a payoff.

## Main results

* `eval_lpPayoff`: the payoff is `v3PositionValue L a b` of `√P`.
* `eval_constantProductPayoff`: the payoff is the reserves `impermanentLossReservesX/Y` of
  `UniswapMechanics` valued at `P`.
* `price_lpPayoff`: in any market, paying either position at `T` is worth the discounted
  expectation of that position's value.

## Scope

The price is a `Market.price` under an arbitrary measure `Q`; it is a price in the sense of
`IsPricingMeasure` only when `Q` is one, and its closed form under Black–Scholes is not stated.

## References

* [H. Adams et al., *Uniswap v3 Core*][AdamsEtAl2021], §6.4.1 (eqs. 6.29-6.30)
* [G. Angeris et al., *An analysis of Uniswap markets*][AngerisKaoChiangNoyesChitra2021]

## Tags

liquidity position, constant-product market maker, Uniswap v3, concentrated liquidity,
payoff language, MSC 91G80, JEL G23
-/

@[expose] public section

open scoped NNReal

namespace MathFin.DeFi

open MathFin.Contracts MeasureTheory

/-- The square root `√P` of the price observed at `T`, as a payoff. -/
noncomputable def sqrtObs (T : ℝ≥0) : Payoff Unit := .rpow (.obs () T) (1 / 2)

/-- **The constant-product position** with invariant `k = x₀ y₀`, as a payoff on the price of X
in Y observed at `T`: `2 √k √P`. -/
noncomputable def constantProductPayoff (k : ℝ) (T : ℝ≥0) : Payoff Unit :=
  .mul (.const (2 * Real.sqrt k)) (sqrtObs T)

/-- **The concentrated-liquidity position** with liquidity `L` on the square-root range `[a, b]`,
as a payoff on the price of X in Y observed at `T`: `L (2u − a − u²/b) + L (1/a − 1/b) (m² − a²)`
with `u = max a (min √P b)` and `m = min √P a`. -/
noncomputable def lpPayoff (L a b : ℝ) (T : ℝ≥0) : Payoff Unit :=
  let u : Payoff Unit := .max (.const a) (.min (sqrtObs T) (.const b))
  let m : Payoff Unit := .min (sqrtObs T) (.const a)
  .add (.mul (.const L) (.sub (.sub (.mul (.const 2) u) (.const a)) (.mul (.const b⁻¹) (.mul u u))))
    (.mul (.const (L * (a⁻¹ - b⁻¹))) (.sub (.mul m m) (.const (a ^ 2))))

theorem eval_sqrtObs (T : ℝ≥0) (s : Scenario Unit) :
    (sqrtObs T).eval s = Real.sqrt (s () T) := by
  simp [sqrtObs, Payoff.eval, Real.sqrt_eq_rpow]

/-- The concentrated-liquidity payoff is the position value `v3PositionValue` of `UniswapMechanics`
at the square root of the observed price. -/
theorem eval_lpPayoff {L a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (T : ℝ≥0) (s : Scenario Unit) :
    (lpPayoff L a b T).eval s = v3PositionValue L a b (Real.sqrt (s () T)) := by
  have hb : 0 < b := ha.trans_le hab
  simp only [lpPayoff, Payoff.eval, eval_sqrtObs]
  generalize Real.sqrt (s () T) = x
  unfold v3PositionValue realReserveX realReserveY
  by_cases h1 : x ≤ a
  · rw [max_eq_left ((min_le_left _ _).trans h1), min_eq_left h1, if_pos h1]
    field_simp
    ring
  · rw [if_neg h1]
    push_neg at h1
    rw [min_eq_right h1.le]
    by_cases h2 : x ≤ b
    · rw [min_eq_left h2, max_eq_right h1.le, if_pos h2]
      have hx : x ≠ 0 := (ha.trans h1).ne'
      field_simp
      ring
    · rw [if_neg h2]
      push_neg at h2
      rw [min_eq_right h2.le, max_eq_right hab]
      field_simp
      ring

/-- The constant-product payoff is the rebalanced reserves `impermanentLossReservesX/Y` of an
invariant `x₀ y₀` valued at the observed price `P > 0`, the reserves being read at the price
ratio `P x₀ / y₀`. -/
theorem eval_constantProductPayoff {x₀ y₀ : ℝ} (hx : 0 < x₀) (hy : 0 < y₀) (T : ℝ≥0)
    (s : Scenario Unit) (hP : 0 < s () T) :
    (constantProductPayoff (x₀ * y₀) T).eval s =
      impermanentLossReservesX x₀ y₀ (s () T * x₀ / y₀) * s () T +
        impermanentLossReservesY x₀ y₀ (s () T * x₀ / y₀) := by
  have hr : s () T * x₀ / y₀ * y₀ / x₀ = s () T := by field_simp
  have h := lpPortfolioValue_eq x₀ y₀ (s () T * x₀ / y₀) hx hy (by positivity)
  rw [hr] at h
  rw [h]
  have key : y₀ * Real.sqrt (s () T * x₀ / y₀) = Real.sqrt (x₀ * y₀) * Real.sqrt (s () T) :=
    calc y₀ * Real.sqrt (s () T * x₀ / y₀)
        = Real.sqrt (y₀ * y₀) * Real.sqrt (s () T * x₀ / y₀) := by
          rw [Real.sqrt_mul_self hy.le]
      _ = Real.sqrt (y₀ * y₀ * (s () T * x₀ / y₀)) := (Real.sqrt_mul (mul_self_nonneg y₀) _).symm
      _ = Real.sqrt (x₀ * y₀ * s () T) := by
          congr 1
          field_simp
      _ = Real.sqrt (x₀ * y₀) * Real.sqrt (s () T) := Real.sqrt_mul (by positivity) _
  simp only [constantProductPayoff, Payoff.eval, eval_sqrtObs]
  linear_combination (-2) * key

/-- **The price of a liquidity position is the discounted expectation of its value.** In a market
with a positive price of X in Y at `T`, under any measure `Q`: the concentrated-liquidity payoff
`lpPayoff L a b T` (for `0 < a ≤ b`) is worth `∫ D_T · v3PositionValue L a b (√P_T)`, and the
constant-product payoff of invariant `x₀ y₀` is worth the discounted expectation of the reserves
`impermanentLossReservesX/Y` valued at the price `P_T`. -/
theorem price_lpPayoff {Ω : Type*} [MeasurableSpace Ω] (M : Market Unit Ω) (Q : Measure Ω)
    (T : ℝ≥0) (hS : ∀ ω, 0 < M.asset () T ω) :
    (∀ L a b : ℝ, 0 < a → a ≤ b →
      M.price Q (.pay T (lpPayoff L a b T)) =
        ∫ ω, M.deflator T ω * v3PositionValue L a b (Real.sqrt (M.asset () T ω)) ∂Q) ∧
    (∀ x₀ y₀ : ℝ, 0 < x₀ → 0 < y₀ →
      M.price Q (.pay T (constantProductPayoff (x₀ * y₀) T)) =
        ∫ ω, M.deflator T ω *
          (impermanentLossReservesX x₀ y₀ (M.asset () T ω * x₀ / y₀) * M.asset () T ω +
            impermanentLossReservesY x₀ y₀ (M.asset () T ω * x₀ / y₀)) ∂Q) := by
  refine ⟨fun L a b ha hab ↦ ?_, fun x₀ y₀ hx hy ↦ ?_⟩
  · rw [Market.price, Contract.value_pay]
    congr 1
    funext ω
    exact congrArg _ (eval_lpPayoff ha hab T _)
  · rw [Market.price, Contract.value_pay]
    congr 1
    funext ω
    exact congrArg _ (eval_constantProductPayoff hx hy T _ (hS ω))

end MathFin.DeFi
