/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import Mathlib
public import MathFin.DeFi.ConstantProductAMM

/-!
# Uniswap v2/v3 AMM mechanics: impermanent loss, TWAP, fee invariant,
v3 real-reserves curve

This file extends the constant-product AMM formalization
(`MathFin/DeFi/ConstantProductAMM.lean`, adapted from Pusceddu-Bartoletti
2024) with further closed-form identities from the Uniswap v2/v3 AMM
designs:

  Hayden Adams, Noah Zinsmeister, Dan Robinson, "Uniswap v2 Core",
  Uniswap whitepaper, 2020. <https://uniswap.org/whitepaper.pdf>

  Hayden Adams et al., "Uniswap v3 Core", Uniswap whitepaper, 2021.
  <https://uniswap.org/whitepaper-v3.pdf>

Curve Finance's StableSwap invariant (Michael Egorov, "StableSwap -
efficient mechanism for Stablecoin liquidity", 2019,
<https://curve.fi/files/stableswap-paper.pdf>) is not formalized in this
file; no StableSwap-specific result appears below.

This file formalises further closed-form results about automated
market makers, building on the constant-product substrate in
`ConstantProductAMM.lean`.

## Results

* `impermanentLossReservesX/Y`, `impermanentLossReserves_invariant`,
  `impermanentLossReserves_price`, `impermanentLoss_eq`: the **impermanent
  loss closed form** `IL(r) = 2√r/(1+r) - 1` for a constant-product LP
  (`x0, y0, r > 0`), derived (not merely asserted) from the post-price-move
  reserve split — the defined reserves satisfy both defining equations
  (`x1*y1 = x0*y0` and `y1/x1 = r*y0/x0`), not just the first.
* `impermanentLoss_eq_neg_sq`, `impermanentLoss_nonpos`, `impermanentLoss_eq_zero_iff`: the
  loss is `−(√r − 1)²/(1 + r)`, so it is never positive and vanishes exactly at `r = 1`
  (AM–GM, `2√r ≤ 1 + r`). Fees are not modelled. The expected LP value under a lognormal price
  is in `MathFin/Bridges/ConstantProductLPLognormal.lean`.
* `twapAccumulator`, `twap`, `twapAccumulator_sub_eq_sum`, `twap_eq_average`:
  the **Uniswap v2 TWAP** over unit time steps, defined as
  `p_{t1,t2} = (a_{t2} - a_{t1})/(t2 - t1)`; the accumulator difference
  telescopes to the window sum, so for `t1 ≤ t2` the TWAP is
  `(∑_{t1 < i ≤ t2} p_i)/(t2 - t1)`.
* `harmonicMean`, `harmonicMean_reciprocal_eq_arithmeticMean`: the
  **reciprocal caveat** — the arithmetic mean of an A-in-B price series is
  the reciprocal of the *harmonic* mean of the B-in-A series. That it
  generally differs from the reciprocal of the B-in-A *arithmetic* mean (the
  AM–HM inequality) is not stated here.
* `swapOutputWithFee`, `fee_invariant_growth`: the Uniswap v2 **fee
  invariant** `x0·y0 ≤ (x0 + Δx)(y0 - Δy)`, where `Δy = swapOutput x0 y0
  (γ·Δx)` is computed from the fee-discounted input (γ the fee retention
  rate; positive reserves and input, `0 < γ ≤ 1`), and `lpFeeShare`, the
  candidate LP value-growth share
  `f = 1 - √(k1/k2)` (only shown nonnegative here, see its docstring).
* `realReserveX/Y`, `realReserves_curve`: the Uniswap v3 **real-reserves
  curve** `(x + L/√p_b)(y + L√p_a) = L²` (v3 whitepaper §2, eq. 2.2): the
  real reserves of an in-range position, shifted by `L/√p_b` and `L√p_a`
  (that is, the virtual reserves `L/√P` and `L√P`), have constant product.
* `v3PositionValue`: the value, in token Y, of a v3 position at any square-root price `s`:
  all token X below the range, the in-range reserves inside, all token Y above (v3 whitepaper
  §6.4.1, eqs. 6.29–6.30). `v3PositionValue_at_lower`, `v3PositionValue_at_upper`: the two
  boundary cases, all X at `s = √p_a` and all Y at `s = √p_b`; `v3PositionValue_nonneg`.
* `v3PositionValue_eq_coveredCall_of_le`, `v3PositionValue_eq_coveredCall_of_lt`,
  `coveredCall_sub_v3PositionValue`, `v3PositionValue_le_coveredCall`: **a v3 position is a
  covered call, less a smoothing term.** With `x_max = realReserveX L √p_a √p_b` the position's
  full X holding, the payoff `x_max · (s² − max (s² − K) 0)` of `x_max` units of X and a short
  call struck at the geometric-mean price `K = √(p_a p_b)` equals the position's value outside
  the range and exceeds it inside by exactly `min (L(s − √p_a)²/√p_a) (L(√p_b − s)²/√p_b)`.
  Fees are not modelled. The resulting Black–Scholes price bound is
  `integral_discounted_v3PositionValue_le` in `MathFin/Bridges/UniswapV3CoveredCallPrice.lean`.
* `tickPrice`, `tickPrice_ratio`: the v3 tick price `p(i) = 1.0001^i` and
  its per-tick ratio.
-/

@[expose] public section

namespace MathFin

namespace DeFi

/-! ## Impermanent loss closed form -/

/-- After the external price moves by factor `r` (new price = `r` times the
price at deposit), a constant-product pool with invariant `k = x0 * y0` and
deposit-time price `y0 / x0` re-balances to the reserves that keep `k`
fixed at the new price `r * y0 / x0`. This is the **new reserve of token
X**: solving `x1 * y1 = x0 * y0` and `y1 / x1 = r * y0 / x0` for positive
reserves gives `x1 = sqrt (x0^2 / r)`. -/
noncomputable def impermanentLossReservesX (x0 _y0 r : ℝ) : ℝ :=
  Real.sqrt (x0 ^ 2 / r)

/-- The new reserve of token Y after the same price move: `y1 = sqrt (y0^2 * r)`. -/
noncomputable def impermanentLossReservesY (_x0 y0 r : ℝ) : ℝ :=
  Real.sqrt (y0 ^ 2 * r)

/-- The rebalanced reserves again satisfy the constant-product invariant. -/
theorem impermanentLossReserves_invariant
    (x0 y0 r : ℝ) (hx0 : 0 < x0) (hy0 : 0 < y0) (hr : 0 < r) :
    impermanentLossReservesX x0 y0 r * impermanentLossReservesY x0 y0 r
      = x0 * y0 := by
  unfold impermanentLossReservesX impermanentLossReservesY
  rw [← Real.sqrt_mul (by positivity)]
  rw [show x0 ^ 2 / r * (y0 ^ 2 * r) = (x0 * y0) ^ 2 by field_simp]
  exact Real.sqrt_sq (by positivity)

/-- The rebalanced reserves sit at the new price `r * y0 / x0`: this is the
second defining equation, so with `impermanentLossReserves_invariant` the
defined pair satisfies both `x1 * y1 = x0 * y0` and `y1 / x1 = r * y0 / x0`,
not merely the invariant. That it is the only positive solution is not
stated. -/
theorem impermanentLossReserves_price
    (x0 y0 r : ℝ) (hx0 : 0 < x0) (hy0 : 0 < y0) (hr : 0 < r) :
    impermanentLossReservesY x0 y0 r / impermanentLossReservesX x0 y0 r
      = r * y0 / x0 := by
  unfold impermanentLossReservesX impermanentLossReservesY
  rw [← Real.sqrt_div' _ (by positivity)]
  rw [show y0 ^ 2 * r / (x0 ^ 2 / r) = (r * y0 / x0) ^ 2 by field_simp]
  exact Real.sqrt_sq (by positivity)

/-- **LP portfolio value** at the new price `p1 = r * y0 / x0`, valued in
token Y: `x1 * p1 + y1`. Derived from the rebalanced reserves above, this
equals `2 * y0 * sqrt r` — the algebraic core of the impermanent-loss
computation. -/
theorem lpPortfolioValue_eq
    (x0 y0 r : ℝ) (hx0 : 0 < x0) (hy0 : 0 < y0) (hr : 0 < r) :
    impermanentLossReservesX x0 y0 r * (r * y0 / x0)
      + impermanentLossReservesY x0 y0 r = 2 * y0 * Real.sqrt r := by
  unfold impermanentLossReservesX impermanentLossReservesY
  set s := Real.sqrt r
  have hs_sq : s ^ 2 = r := Real.sq_sqrt hr.le
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hr
  have hx0' : x0 ≠ 0 := hx0.ne'
  have hs' : s ≠ 0 := hs_pos.ne'
  rw [← hs_sq]
  rw [show x0 ^ 2 / s ^ 2 = (x0 / s) ^ 2 by rw [div_pow]]
  rw [show y0 ^ 2 * s ^ 2 = (y0 * s) ^ 2 by rw [mul_pow]]
  rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
  field_simp
  ring

/-- **HODL portfolio value** at the same new price: `x0 * p1 + y0`, which
simplifies to `y0 * (r + 1)` since `x0 * (y0/x0) = y0`. -/
theorem hodlPortfolioValue_eq (x0 y0 r : ℝ) (hx0 : 0 < x0) :
    x0 * (r * y0 / x0) + y0 = y0 * (r + 1) := by
  have hx0' : x0 ≠ 0 := hx0.ne'
  field_simp

/-- **Impermanent loss closed form**: `IL(r) = 2 * sqrt r / (1 + r) - 1`. -/
noncomputable def impermanentLoss (r : ℝ) : ℝ :=
  2 * Real.sqrt r / (1 + r) - 1

/-- **Impermanent loss theorem**: the LP-vs-HODL value ratio, minus one,
is exactly the closed form `2√r/(1+r) - 1`, independent of the deposit
amounts `x0, y0`. -/
theorem impermanentLoss_eq (x0 y0 r : ℝ) (hx0 : 0 < x0) (hy0 : 0 < y0) (hr : 0 < r) :
    (impermanentLossReservesX x0 y0 r * (r * y0 / x0)
        + impermanentLossReservesY x0 y0 r) / (x0 * (r * y0 / x0) + y0) - 1
      = impermanentLoss r := by
  rw [lpPortfolioValue_eq x0 y0 r hx0 hy0 hr, hodlPortfolioValue_eq x0 y0 r hx0]
  unfold impermanentLoss
  have hy0' : y0 ≠ 0 := hy0.ne'
  have hr1 : (1 : ℝ) + r ≠ 0 := by positivity
  rw [show 2 * y0 * Real.sqrt r / (y0 * (r + 1)) = 2 * Real.sqrt r / (1 + r) by
    field_simp; ring]

/-- **Impermanent loss is a negative square**: for `r ≥ 0`,
`IL(r) = 2√r/(1 + r) − 1 = −(√r − 1)²/(1 + r)`. -/
theorem impermanentLoss_eq_neg_sq {r : ℝ} (hr : 0 ≤ r) :
    impermanentLoss r = -(Real.sqrt r - 1) ^ 2 / (1 + r) := by
  have h1 : (1 : ℝ) + r ≠ 0 := (by linarith : (0 : ℝ) < 1 + r).ne'
  rw [impermanentLoss, eq_div_iff h1, sub_mul, div_mul_cancel₀ _ h1]
  linear_combination Real.sq_sqrt hr

/-- **Impermanent loss is never positive** (AM–GM, `2√r ≤ 1 + r`): a fee-free constant-product
LP never ends a price move ahead of holding the deposit. -/
theorem impermanentLoss_nonpos {r : ℝ} (hr : 0 ≤ r) : impermanentLoss r ≤ 0 := by
  rw [impermanentLoss_eq_neg_sq hr, neg_div]
  exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by linarith))

/-- **Impermanent loss vanishes exactly when the price returns**: for `r ≥ 0`,
`IL(r) = 0 ↔ r = 1`. -/
theorem impermanentLoss_eq_zero_iff {r : ℝ} (hr : 0 ≤ r) : impermanentLoss r = 0 ↔ r = 1 := by
  rw [impermanentLoss_eq_neg_sq hr, neg_div, neg_eq_zero,
    div_eq_zero_iff, or_iff_left (by linarith : (0 : ℝ) < 1 + r).ne', sq_eq_zero_iff, sub_eq_zero,
    Real.sqrt_eq_one]

/-! ## Uniswap v2 TWAP accumulator -/

/-- **TWAP accumulator**: the running sum `a_t = Σ_{i ≤ t} p_i` of a
discrete price series with unit time steps — the special case of the
Uniswap v2 `price*CumulativeLast` storage slots (which accumulate
`p·Δt` over arbitrary block-timestamp gaps) where every step has
`Δt = 1`. -/
noncomputable def twapAccumulator (p : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (t + 1), p i

/-- **Telescoping-sum identity**: the accumulator difference over
`(t1, t2]` equals the sum of prices over that window. -/
theorem twapAccumulator_sub_eq_sum
    (p : ℕ → ℝ) (t1 t2 : ℕ) (h : t1 ≤ t2) :
    twapAccumulator p t2 - twapAccumulator p t1
      = ∑ i ∈ Finset.Ico (t1 + 1) (t2 + 1), p i := by
  unfold twapAccumulator
  rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
  have := Finset.sum_Ico_consecutive p (Nat.zero_le (t1 + 1)) (by omega : t1 + 1 ≤ t2 + 1)
  linarith [this]

/-- **Time-weighted average price** over unit time steps, matching how
Uniswap v2 oracles compute it in the equal-spacing case:
`p_{t1,t2} = (a_{t2} - a_{t1}) / (t2 - t1)`. -/
noncomputable def twap (p : ℕ → ℝ) (t1 t2 : ℕ) : ℝ :=
  (twapAccumulator p t2 - twapAccumulator p t1) / ((t2 : ℝ) - (t1 : ℝ))

/-- The TWAP equals the arithmetic mean of the price series over the
window `(t1, t2]`, i.e. the telescoping accumulator identity really does
compute a time-weighted average — for `t1 < t2`; at `t1 = t2` both sides
reduce to `_ / 0 = 0` by Lean's junk-value convention for division, not a
genuine average over an empty window. -/
theorem twap_eq_average (p : ℕ → ℝ) (t1 t2 : ℕ) (h : t1 ≤ t2) :
    twap p t1 t2 = (∑ i ∈ Finset.Ico (t1 + 1) (t2 + 1), p i) / ((t2 : ℝ) - (t1 : ℝ)) := by
  unfold twap
  rw [twapAccumulator_sub_eq_sum p t1 t2 h]

/-- The harmonic mean `|s| / ∑_{i∈s} 1/q_i` of a finite family of values `q` (meant for a
nonempty family of positive prices; neither hypothesis is built in). -/
noncomputable def harmonicMean (s : Finset ℕ) (q : ℕ → ℝ) : ℝ :=
  (s.card : ℝ) / ∑ i ∈ s, (1 / q i)

/-- If `q` is the reciprocal price series (B-in-A, when `p` is A-in-B),
the **reciprocal of the harmonic mean of `q` equals the arithmetic mean of
`p`**. That this generally differs from the reciprocal of the arithmetic mean
of `q` (the AM–HM inequality, with equality iff `p` is constant) is the caveat
behind the name, and it is not stated here. Intended for strictly positive values
(prices), but stated without that hypothesis: the identity is a `div`/`div`
junk-value tautology that holds unconditionally for *any* finite family
`s`, including the empty one (both sides reduce to `0`). -/
theorem harmonicMean_reciprocal_eq_arithmeticMean
    (s : Finset ℕ) (p : ℕ → ℝ) :
    1 / harmonicMean s (fun i ↦ 1 / p i) = (∑ i ∈ s, p i) / (s.card : ℝ) := by
  unfold harmonicMean
  have hsum : ∑ i ∈ s, (1 / (1 / p i)) = ∑ i ∈ s, p i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [one_div_one_div]
  rw [one_div_div, hsum]

/-! ## Uniswap v2 fee invariant and LP fee share -/

/-- **Fee-adjusted swap output**: Uniswap v2 charges a fee rate `1 - γ`
(e.g. `γ = 0.997` for the standard 0.3% fee), applying the constant-product
formula to only the `γ`-fraction of the input that is actually swapped;
the remaining `(1-γ) * Δx` stays in the pool as fee revenue. -/
noncomputable def swapOutputWithFee (x y Δx γ : ℝ) : ℝ :=
  swapOutput x y (γ * Δx)

/-- **Fee invariant growth**: crediting the *full* input `Δx` to the X
reserve (the fee portion is retained, not refunded) while only the
fee-adjusted output `Δy` leaves the Y reserve makes the invariant grow
(weakly) rather than merely hold:

  `x0 * y0 ≤ (x0 + Δx) * (y0 - Δy)`,

since `(x0 + γΔx) * (y0 - Δy) = x0 * y0` exactly (the no-fee invariant) and
`x0 + Δx ≥ x0 + γΔx` with `y0 - Δy > 0`. -/
theorem fee_invariant_growth
    (x0 y0 Δx γ : ℝ) (hx0 : 0 < x0) (hy0 : 0 < y0) (hΔx : 0 < Δx)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    x0 * y0 ≤ (x0 + Δx) * (y0 - swapOutputWithFee x0 y0 Δx γ) := by
  unfold swapOutputWithFee
  have hγΔx : 0 < γ * Δx := mul_pos hγ0 hΔx
  have hinv := swap_preserves_invariant x0 y0 (γ * Δx) hx0 hγΔx
  have hy_pos : 0 < y0 - swapOutput x0 y0 (γ * Δx) :=
    sub_pos.mpr (swap_output_lt_y x0 y0 (γ * Δx) hx0 hγΔx hy0)
  have hle : x0 + γ * Δx ≤ x0 + Δx := by linarith [mul_le_of_le_one_left hΔx.le hγ1]
  calc x0 * y0 = (x0 + γ * Δx) * (y0 - swapOutput x0 y0 (γ * Δx)) := hinv.symm
    _ ≤ (x0 + Δx) * (y0 - swapOutput x0 y0 (γ * Δx)) :=
        mul_le_mul_of_nonneg_right hle hy_pos.le

/-- **LP fee share candidate**: under the (unproved here) assumption that
LP token value scales with `sqrt k` — the LP's claim on reserves scales
reserves uniformly, so value scales with the geometric mean `sqrt(x*y)` —
`f = 1 - sqrt(k1/k2)` would be the fraction of value growth attributable
to the invariant moving from `k1` to `k2` purely from retained fees. This
file only establishes the sanity property `lpFeeShare_nonneg` below; it
does not prove `f` equals an actual LP value-growth ratio. -/
noncomputable def lpFeeShare (k1 k2 : ℝ) : ℝ :=
  1 - Real.sqrt (k1 / k2)

/-- `lpFeeShare` is nonnegative when the invariant has not shrunk,
matching the fee economics (fees only grow `k`). -/
theorem lpFeeShare_nonneg (k1 k2 : ℝ) (hk2 : 0 < k2) (h : k1 ≤ k2) :
    0 ≤ lpFeeShare k1 k2 := by
  unfold lpFeeShare
  have : Real.sqrt (k1 / k2) ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by rw [div_le_one hk2]; exact h)
  linarith

/-! ## Uniswap v3 real-reserves curve -/

/-- **Real reserve of token X** in a Uniswap v3 concentrated-liquidity
position with liquidity `L`, square-root price `√P`, and range `[√p_a, √p_b]`
(v3 whitepaper §2, the `x` of eq. 2.2): `x = L(1/√P − 1/√p_b)`. Adding `L/√p_b`
gives the virtual reserve `L/√P`. This formula represents the position's
*in-range* reserves only — valid while `√p_a ≤ √P ≤ √p_b`; once the price moves
below the range the position's actual X reserve saturates instead of following
this curve (and above the range it holds no X at all), which `v3PositionValue` below
models (all X below the range, all Y above). -/
noncomputable def realReserveX (L sqrtP sqrtPb : ℝ) : ℝ :=
  L * (1 / sqrtP - 1 / sqrtPb)

/-- **Real reserve of token Y** for the same position (the `y` of eq. 2.2):
`y = L(√P − √p_a)`. Adding `L√p_a` gives the virtual reserve `L√P`. As with
`realReserveX`, this represents the *in-range* reserve only — valid
while `√p_a ≤ √P ≤ √p_b`; outside the range the actual Y reserve
saturates rather than following this curve, as `v3PositionValue` below
models. -/
noncomputable def realReserveY (L sqrtP sqrtPa : ℝ) : ℝ :=
  L * (sqrtP - sqrtPa)

/-- **Uniswap v3 real-reserves curve** (v3 whitepaper §2, eq. 2.2): the
position's real reserves, shifted by `L/√p_b` and `L√p_a` (that is, the
virtual reserves `L/√P` and `L√P`), satisfy the same constant-product form as
a v2 pool with liquidity `L`:

  `(x + L/√p_b) * (y + L√p_a) = L²`. -/
theorem realReserves_curve
    (L sqrtP sqrtPa sqrtPb : ℝ) (hP : 0 < sqrtP) (hPb : 0 < sqrtPb) :
    (realReserveX L sqrtP sqrtPb + L / sqrtPb)
      * (realReserveY L sqrtP sqrtPa + L * sqrtPa) = L ^ 2 := by
  unfold realReserveX realReserveY
  have hP' : sqrtP ≠ 0 := hP.ne'
  have hPb' : sqrtPb ≠ 0 := hPb.ne'
  field_simp
  ring

/-- **Value of a Uniswap v3 position**, in token Y, at square-root price `s`, for liquidity `L` on
the square-root price range `[a, b]` (`a = √p_a`, `b = √p_b`). Below the range the position
holds only token X, its full amount `realReserveX L a b`, worth `s²` each; inside the range it
holds the real reserves `realReserveY L s a` and `realReserveX L s b`; above the range it holds
only token Y, its full amount `realReserveY L b a` (v3 whitepaper §6.4.1, eqs. 6.29–6.30). -/
noncomputable def v3PositionValue (L a b s : ℝ) : ℝ :=
  if s ≤ a then s ^ 2 * realReserveX L a b
  else if s ≤ b then realReserveY L s a + s ^ 2 * realReserveX L s b
  else realReserveY L b a

/-- **All token X at the lower end** of the range: at `s = a` the position is worth its full X
holding `realReserveX L a b` at price `a²`. -/
theorem v3PositionValue_at_lower (L a b : ℝ) :
    v3PositionValue L a b a = a ^ 2 * realReserveX L a b := by
  rw [v3PositionValue, if_pos le_rfl]

/-- **All token Y at the upper end** of the range: at `s = b` the in-range X reserve is zero and
the position is worth its full Y holding `realReserveY L b a`. -/
theorem v3PositionValue_at_upper (L : ℝ) {a b : ℝ} (hab : a < b) :
    v3PositionValue L a b b = realReserveY L b a := by
  rw [v3PositionValue, if_neg (not_le.mpr hab), if_pos le_rfl, realReserveX, sub_self, mul_zero,
    mul_zero, add_zero]

/-- **A v3 position has nonnegative value** for `L ≥ 0` and `0 < a ≤ b`. -/
theorem v3PositionValue_nonneg {L a b s : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ v3PositionValue L a b s := by
  unfold v3PositionValue realReserveX realReserveY
  split_ifs with hsa hsb
  · exact mul_nonneg (sq_nonneg s)
      (mul_nonneg hL (sub_nonneg.mpr (one_div_le_one_div_of_le ha hab)))
  · have hs' : 0 < s := ha.trans (not_le.mp hsa)
    exact add_nonneg (mul_nonneg hL (by linarith [not_le.mp hsa]))
      (mul_nonneg (sq_nonneg s) (mul_nonneg hL (sub_nonneg.mpr (one_div_le_one_div_of_le hs' hsb))))
  · exact mul_nonneg hL (by linarith)

/-- **Below the range the position is the covered call**: for `0 ≤ s ≤ a`,
`v3PositionValue L a b s = x_max · (s² − max (s² − ab) 0)` with `x_max = realReserveX L a b`
(here `s² ≤ ab`, so the call is out of the money). -/
theorem v3PositionValue_eq_coveredCall_of_le {L a b s : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : 0 ≤ s) (hsa : s ≤ a) :
    v3PositionValue L a b s = realReserveX L a b * (s ^ 2 - max (s ^ 2 - a * b) 0) := by
  rw [v3PositionValue, if_pos hsa,
    max_eq_right (by nlinarith [mul_le_mul hsa hsa hs ha.le, mul_le_mul_of_nonneg_left hab ha.le]),
    sub_zero, mul_comm]

/-- **Above the range the position is the covered call**: for `b < s`,
`v3PositionValue L a b s = x_max · (s² − max (s² − ab) 0) = x_max · ab = L (b − a)`, the full Y
holding (here `s² > ab`, so the call is in the money and caps the payoff). -/
theorem v3PositionValue_eq_coveredCall_of_lt {L a b s : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbs : b < s) :
    v3PositionValue L a b s = realReserveX L a b * (s ^ 2 - max (s ^ 2 - a * b) 0) := by
  have hb : 0 < b := ha.trans_le hab
  rw [v3PositionValue, if_neg (not_le.mpr (hab.trans_lt hbs)), if_neg (not_le.mpr hbs),
    max_eq_left (by nlinarith [mul_le_mul hbs.le hbs.le hb.le (hb.trans hbs).le,
      mul_le_mul_of_nonneg_right hab hb.le]),
    sub_sub_cancel, realReserveX, realReserveY]
  field_simp

/-- In-range identity behind `coveredCall_sub_v3PositionValue`: holding all of `x_max` at price
`s²` beats the in-range position by `L (s − a)² / a`. -/
theorem realReserveX_mul_sq_sub_inRange {L a b s : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) :
    realReserveX L a b * s ^ 2 - (realReserveY L s a + s ^ 2 * realReserveX L s b)
      = L * (s - a) ^ 2 / a := by
  unfold realReserveX realReserveY
  field_simp
  ring

/-- In-range identity behind `coveredCall_sub_v3PositionValue`: the capped payoff `x_max · ab`
beats the in-range position by `L (b − s)² / b`. -/
theorem realReserveX_mul_mul_sub_inRange {L a b s : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) :
    realReserveX L a b * (a * b) - (realReserveY L s a + s ^ 2 * realReserveX L s b)
      = L * (b - s) ^ 2 / b := by
  unfold realReserveX realReserveY
  field_simp
  ring

/-- **Inside the range the covered call exceeds the position by the smaller squared gap.** For
`L ≥ 0`, `0 < a < s ≤ b`:
`x_max · (s² − max (s² − ab) 0) − v3PositionValue L a b s = min (L(s − a)²/a) (L(b − s)²/b)`. -/
theorem coveredCall_sub_v3PositionValue {L a b s : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (has : a < s)
    (hsb : s ≤ b) :
    realReserveX L a b * (s ^ 2 - max (s ^ 2 - a * b) 0) - v3PositionValue L a b s
      = min (L * (s - a) ^ 2 / a) (L * (b - s) ^ 2 / b) := by
  have hs : 0 < s := ha.trans has
  have hb : 0 < b := hs.trans_le hsb
  have hX : 0 ≤ realReserveX L a b :=
    mul_nonneg hL (sub_nonneg.mpr (one_div_le_one_div_of_le ha (has.le.trans hsb)))
  have h1 := realReserveX_mul_sq_sub_inRange (L := L) ha.ne' hb.ne' hs.ne'
  have h2 := realReserveX_mul_mul_sub_inRange (L := L) ha.ne' hb.ne' hs.ne'
  rw [v3PositionValue, if_neg (not_le.mpr has), if_pos hsb]
  rcases le_total (s ^ 2) (a * b) with h | h
  · rw [max_eq_right (sub_nonpos.mpr h), sub_zero, h1, min_eq_left]
    nlinarith [mul_nonneg hX (sub_nonneg.mpr h)]
  · rw [max_eq_left (sub_nonneg.mpr h), sub_sub_cancel, h2, min_eq_right]
    nlinarith [mul_nonneg hX (sub_nonneg.mpr h)]

/-- **A v3 position is worth at most the covered call** `x_max · (s² − max (s² − ab) 0)`: long
its full X holding `x_max = realReserveX L a b`, short a call struck at the geometric-mean price
`ab = √(p_a p_b)`. Equality holds outside the range (`v3PositionValue_eq_coveredCall_of_le`,
`v3PositionValue_eq_coveredCall_of_lt`); inside it the gap is `coveredCall_sub_v3PositionValue`. -/
theorem v3PositionValue_le_coveredCall {L a b s : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (hab : a ≤ b)
    (hs : 0 ≤ s) :
    v3PositionValue L a b s ≤ realReserveX L a b * (s ^ 2 - max (s ^ 2 - a * b) 0) := by
  rcases le_or_gt s a with hsa | has
  · exact (v3PositionValue_eq_coveredCall_of_le ha hab hs hsa).le
  rcases le_or_gt s b with hsb | hbs
  · have := coveredCall_sub_v3PositionValue hL ha has hsb
    have : 0 ≤ min (L * (s - a) ^ 2 / a) (L * (b - s) ^ 2 / b) :=
      le_min (div_nonneg (mul_nonneg hL (sq_nonneg _)) ha.le)
        (div_nonneg (mul_nonneg hL (sq_nonneg _)) (ha.trans (has.trans_le hsb)).le)
    linarith
  · exact (v3PositionValue_eq_coveredCall_of_lt ha hab hbs).le

/-- **Tick price**: Uniswap v3 discretizes the price axis into ticks `i`
(integers) with `p(i) = 1.0001^i`, so every tick is `0.01%` apart from its
neighbor. -/
noncomputable def tickPrice (i : ℤ) : ℝ :=
  (1.0001 : ℝ) ^ i

/-- Consecutive ticks have the fixed ratio `1.0001`. -/
theorem tickPrice_ratio (i : ℤ) :
    tickPrice (i + 1) / tickPrice i = 1.0001 := by
  unfold tickPrice
  rw [zpow_add₀ (by norm_num : (1.0001:ℝ) ≠ 0)]
  field_simp

end DeFi

end MathFin
