/-
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

Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.DeFi.ConstantProductAMM

/-!
# Uniswap v2/v3 AMM mechanics: impermanent loss, TWAP, fee invariant,
v3 virtual reserves

This file formalises four further closed-form results about automated
market makers, building on the constant-product substrate in
`ConstantProductAMM.lean`.

## Results

* `impermanentLossReservesX/Y`, `impermanentLossReserves_invariant`,
  `impermanentLossReserves_price`, `impermanentLoss_eq`: the **impermanent
  loss closed form** `IL(r) = 2√r/(1+r) - 1` for a constant-product LP,
  derived (not merely asserted) from the post-price-move reserve split —
  both defining equations (`x1*y1 = x0*y0` and `y1/x1 = r*y0/x0`) are
  proved, not just the first.
* `twapAccumulator`, `twap_eq_average`: the **Uniswap v2 TWAP accumulator**
  telescoping-sum identity `p_{t1,t2} = (a_{t2} - a_{t1})/(t2 - t1)`.
* `harmonicMean`, `harmonicMean_reciprocal_eq_arithmeticMean`: the
  **reciprocal caveat** — the arithmetic mean of an A-in-B price series is
  the reciprocal of the *harmonic* mean of the B-in-A series, not of its
  arithmetic mean.
* `swapOutputWithFee`, `fee_invariant_growth`: the Uniswap v2 **fee
  invariant** `(x0 + Δx)(y0 - Δy) ≥ x0·y0`, where `Δy = swapOutput x0 y0
  (γ·Δx)` is computed from the fee-discounted input (γ the fee retention
  rate), and `lpFeeShare`, the candidate LP value-growth share
  `f = 1 - √(k1/k2)` (only shown nonnegative here, see its docstring).
* `virtualReserveX/Y`, `virtual_reserve_curve`: the Uniswap v3
  **virtual-reserve curve** `(x + L/√p_b)(y + L√p_a) = L²`.
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
X**: solving `x1 * y1 = x0 * y0` and `y1 / x1 = r * y0 / x0` gives
`x1 = sqrt (x0^2 / r)`. -/
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
second defining equation (alongside `impermanentLossReserves_invariant`)
that pins down `x1, y1` as *the* solution of `x1 * y1 = x0 * y0` and
`y1 / x1 = r * y0 / x0`, not merely one pair satisfying the invariant. -/
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
reduce to `_ / 0 = 0` by Lean's junk-value convention for division. -/
theorem twap_eq_average (p : ℕ → ℝ) (t1 t2 : ℕ) (h : t1 ≤ t2) :
    twap p t1 t2 = (∑ i ∈ Finset.Ico (t1 + 1) (t2 + 1), p i) / ((t2 : ℝ) - (t1 : ℝ)) := by
  unfold twap
  rw [twapAccumulator_sub_eq_sum p t1 t2 h]

/-- **Reciprocal caveat**: the harmonic mean of a finite nonempty family of
strictly positive values `q`. -/
noncomputable def harmonicMean (s : Finset ℕ) (q : ℕ → ℝ) : ℝ :=
  (s.card : ℝ) / ∑ i ∈ s, (1 / q i)

/-- If `q` is the reciprocal price series (B-in-A, when `p` is A-in-B),
the **reciprocal of the harmonic mean of `q` equals the arithmetic mean of
`p`** — not the reciprocal of the arithmetic mean of `q`. This is the
caveat: naively averaging the reciprocal series and inverting gives the
wrong (harmonic, not arithmetic) mean. Stated for a nonempty family of
strictly positive values, the intended reading; the identity itself is a
`div`/`div` junk-value tautology that also holds at `s = ∅`. -/
theorem harmonicMean_reciprocal_eq_arithmeticMean
    (s : Finset ℕ) (p : ℕ → ℝ) :
    1 / harmonicMean s (fun i => 1 / p i) = (∑ i ∈ s, p i) / (s.card : ℝ) := by
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

  `(x0 + Δx) * (y0 - Δy) ≥ x0 * y0`,

since `(x0 + γΔx) * (y0 - Δy) = x0 * y0` exactly (the no-fee invariant) and
`x0 + Δx ≥ x0 + γΔx` with `y0 - Δy > 0`. -/
theorem fee_invariant_growth
    (x0 y0 Δx γ : ℝ) (hx0 : 0 < x0) (hy0 : 0 < y0) (hΔx : 0 < Δx)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    (x0 + Δx) * (y0 - swapOutputWithFee x0 y0 Δx γ) ≥ x0 * y0 := by
  unfold swapOutputWithFee
  have hγΔx : 0 < γ * Δx := mul_pos hγ0 hΔx
  have hinv := swap_preserves_invariant x0 y0 (γ * Δx) hx0 hγΔx
  have hy_pos : 0 < y0 - swapOutput x0 y0 (γ * Δx) :=
    sub_pos.mpr (swap_output_lt_y x0 y0 (γ * Δx) hx0 hγΔx hy0)
  have hle : x0 + γ * Δx ≤ x0 + Δx := by nlinarith
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
theorem lpFeeShare_nonneg (k1 k2 : ℝ) (_hk1 : 0 < k1) (hk2 : 0 < k2) (h : k1 ≤ k2) :
    0 ≤ lpFeeShare k1 k2 := by
  unfold lpFeeShare
  have : Real.sqrt (k1 / k2) ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by rw [div_le_one hk2]; exact h)
  linarith

/-! ## Uniswap v3 virtual-reserve curve -/

/-- **Virtual reserve of token X** in a Uniswap v3 concentrated-liquidity
position with liquidity `L`, current price `√P`, and range `[√p_a, √p_b]`. -/
noncomputable def virtualReserveX (L sqrtP sqrtPb : ℝ) : ℝ :=
  L * (1 / sqrtP - 1 / sqrtPb)

/-- **Virtual reserve of token Y** for the same position. -/
noncomputable def virtualReserveY (L sqrtP sqrtPa : ℝ) : ℝ :=
  L * (sqrtP - sqrtPa)

/-- **Uniswap v3 virtual-reserve curve**: the position's reserves, shifted
by the range endpoints, satisfy the same constant-product form as a v2
pool with liquidity `L`:

  `(x + L/√p_b) * (y + L√p_a) = L²`. -/
theorem virtual_reserve_curve
    (L sqrtP sqrtPa sqrtPb : ℝ) (hP : 0 < sqrtP) (hPb : 0 < sqrtPb) :
    (virtualReserveX L sqrtP sqrtPb + L / sqrtPb)
      * (virtualReserveY L sqrtP sqrtPa + L * sqrtPa) = L ^ 2 := by
  unfold virtualReserveX virtualReserveY
  have hP' : sqrtP ≠ 0 := hP.ne'
  have hPb' : sqrtPb ≠ 0 := hPb.ne'
  field_simp
  ring

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
