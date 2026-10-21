/-
This file adapts the mathematical content of the **constant-product AMM**
(Uniswap v2-style) from:

  Daniele Pusceddu and Massimo Bartoletti, "Formalizing Automated Market
  Makers in the Lean 4 Theorem Prover", OASIcs FMBC 2024 (5th
  International Workshop on Formal Methods for Blockchains).
  <https://doi.org/10.4230/OASIcs.FMBC.2024.5>
  Companion code: <https://github.com/dpusceddu/lean4-amm>

and the underlying theory paper they cite:

  Massimo Bartoletti, James Chiang, and Alberto Lluch-Lafuente, "A theory
  of Automated Market Makers in DeFi", LMCS 2022.

Our implementation differs from Pusceddu-Bartoletti's in that we use
**plain real reserves** (`ℝ` with positivity hypotheses) rather than
Lean's `PReal` (strictly-positive-reals subtype) machinery, and we model
**a single AMM pair** rather than their full multi-AMM blockchain state
abstraction. The mathematical content (constant-product invariant + swap
output formula + invariant preservation + arbitrage gain) is adapted
from their work.

Author of this MathFin Lean 4 adaptation: Raphael Coelho.
Original mathematical framework: Bartoletti-Chiang-Lluch-Lafuente (2022),
Pusceddu-Bartoletti Lean formalisation (2024).
Copyright (c) 2026 Raphael Coelho (this adaptation).
Mathematical content © Bartoletti et al. / Pusceddu-Bartoletti, used here
under academic fair use for derivative work with attribution. The
original Pusceddu-Bartoletti GitHub repository has no explicit license at
the time of writing; this adaptation does not copy any Lean source from
that repo and uses only the published paper content.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# Constant-product AMM (after Pusceddu-Bartoletti 2024)

A constant-product Automated Market Maker (CPMM, Uniswap v2-style) holds
reserves `(x, y)` of two tokens. The **constant-product invariant**
`x · y = k` is preserved across swap transactions: a trader who deposits
`Δx` of token X receives

  `Δy = y · Δx / (x + Δx)`

of token Y, after which the new reserves `(x + Δx, y − Δy)` again satisfy
`(x + Δx)·(y − Δy) = x · y`. This algorithmically-determined exchange
rate is what makes CPMMs "automated" — no order book, no oracle.

This file formalises:

* `swapOutput`: the closed-form `Δy` as a function of input `Δx` and
  reserves.
* `swap_preserves_invariant`: `(x + Δx)·(y − Δy) = x · y`, the pricing rule:
  the swap is the trade that keeps the product fixed.
* `swap_round_trip`: swapping `Δx` in and the proceeds straight back returns
  exactly `Δx`. This is the **no-money-printing** property, proved for that
  round trip: it neither gains nor loses.
* `marginal_exchange_rate`: the average rate `Δy / Δx = y / (x + Δx)`;
  `hasDerivAt_swapOutput`, `hasDerivAt_swapOutput_zero`: the marginal rate at
  size `Δx` is `x y / (x + Δx)²`, and at zero size it is the **internal price**
  `y / x`.
* `internalPrice` / `arbitragePresent`: the internal price `y / x` and the
  predicate for it diverging from an external oracle price `P`.
* `exists_profitable_swap_iff`, `exists_profitable_reverse_swap_iff`,
  `arbitragePresent_iff`: **the arbitrage meaning of `arbitragePresent`,
  derived**. Some single swap against the pool earns a riskless profit,
  valued at `P`, if and only if `y / x ≠ P`: selling X to the pool pays
  exactly when `P < y / x`, buying X from it exactly when `y / x < P`. So a
  pool whose internal price equals the oracle price admits no profitable
  swap of any size, the fee-free case of the no-arbitrage band of
  Angeris et al. (2021).

## Why this is quant finance

Pre-existing `Foundations/AlmgrenChriss.lean` covers traditional execution
cost / market impact. CPMM swap output `Δy = y·Δx/(x+Δx)` plays the same
role for an automated market maker: the execution rate `y/(x+Δx)` depends on
the trade size (an analogy only; no formal link to the Almgren-Chriss model is
made here).

## Results

* `swapOutput`: definition `y · Δx / (x + Δx)`.
* `swap_preserves_invariant`: constant-product invariance under swap.
* `swap_output_pos`: `Δy > 0` when input is positive.
* `swap_output_lt_y`: `Δy < y` (cannot drain pool).
* `swap_round_trip`: a round trip through the pool returns exactly the input.
* `marginal_exchange_rate`: the average rate `Δy / Δx = y / (x + Δx)`.
* `hasDerivAt_swapOutput`, `hasDerivAt_swapOutput_zero`: the marginal rate,
  and the internal price as the marginal rate at zero size.
* `internalPrice`, `arbitragePresent`: internal price `y / x` and the
  oracle-divergence predicate (definitions).
* `exists_profitable_swap_iff`, `exists_profitable_reverse_swap_iff`,
  `arbitragePresent_iff`: price divergence is equivalent to the existence of a
  profitable swap at oracle prices.

## References

* G. Angeris, H.-T. Kao, R. Chiang, C. Noyes, T. Chitra, "An analysis of
  Uniswap markets", *Cryptoeconomic Systems* 1(1) (2021), §2.1 (optimal
  arbitrage; the no-arbitrage bound (3), which at zero fee says the pool
  price equals the reference price).
-/

@[expose] public section

namespace MathFin

namespace DeFi

/-- **Constant-product AMM swap output**: given input `Δx` of token X
and reserves `(x, y)` with `x, y > 0`, the output `Δy` of token Y
under the constant-product invariant `x · y = k` is

  `Δy := y · Δx / (x + Δx)`.

This is the algebraic core of the Uniswap v2 model (Adams-Zinsmeister
2020), as formalised by Pusceddu-Bartoletti (2024). -/
noncomputable def swapOutput (x y Δx : ℝ) : ℝ :=
  y * Δx / (x + Δx)

/-- **Constant-product invariant preservation**: after a swap of input
`Δx` (with `x, Δx > 0`), the new reserves `(x + Δx, y − Δy)` satisfy

  `(x + Δx) · (y − Δy) = x · y`,

where `Δy := swapOutput x y Δx`. This is the pricing rule of the CPMM: the swap
is the trade that keeps the product fixed. That a round trip prints no money is
`swap_round_trip`. -/
theorem swap_preserves_invariant
    (x y Δx : ℝ) (hx : 0 < x) (hΔx : 0 < Δx) :
    (x + Δx) * (y - swapOutput x y Δx) = x * y := by
  unfold swapOutput
  have h_sum_pos : 0 < x + Δx := by linarith
  field_simp
  ring

/-- **Swap output is strictly positive** when input is positive (and
reserves are positive). -/
theorem swap_output_pos
    (x y Δx : ℝ) (hx : 0 < x) (hy : 0 < y) (hΔx : 0 < Δx) :
    0 < swapOutput x y Δx := by
  unfold swapOutput
  have h_sum_pos : 0 < x + Δx := by linarith
  exact div_pos (mul_pos hy hΔx) h_sum_pos

/-- **Swap output bounded by reserve**: `Δy < y` — the AMM cannot be
drained by any single (finite) trade. The deficit is exactly the positive
remainder `y·x / (x + Δx)`. -/
theorem swap_output_lt_y
    (x y Δx : ℝ) (hx : 0 < x) (hΔx : 0 < Δx) (hy : 0 < y) :
    swapOutput x y Δx < y := by
  unfold swapOutput
  have h_sum_pos : 0 < x + Δx := by linarith
  rw [div_lt_iff₀ h_sum_pos]
  -- y · Δx < y · x + y · Δx, the gap being the positive y · x
  nlinarith [mul_pos hy hx]

/-- **Average execution rate**: for any input `Δx > 0`, the rate `Δy / Δx`
received is `y / (x + Δx)`. The marginal rate at zero size, the internal price
`y / x`, is `hasDerivAt_swapOutput_zero`. -/
lemma marginal_exchange_rate
    (x y Δx : ℝ) (hx : 0 < x) (hΔx : 0 < Δx) :
    swapOutput x y Δx / Δx = y / (x + Δx) := by
  unfold swapOutput
  have h_sum_pos : 0 < x + Δx := by linarith
  have hΔx_ne : Δx ≠ 0 := hΔx.ne'
  field_simp

/-- **Internal price = reserve ratio** at zero input: the spot price of
token X (denominated in Y) implied by the AMM's curve at the current
reserve point is `y / x`. -/
noncomputable def internalPrice (x y : ℝ) : ℝ := y / x

/-- **Arbitrage trigger condition**: the AMM's internal price `y/x` differs
from an external oracle's price `p_oracle`. That this is exactly the existence
of a profitable swap at the oracle price is `arbitragePresent_iff`; the optimal
arbitrage size is not formalized here (see Pusceddu-Bartoletti 2024 §3 and
Bartoletti-Chiang-Lluch-Lafuente 2022, Theorem 4). -/
def arbitragePresent (x y p_oracle : ℝ) : Prop :=
  internalPrice x y ≠ p_oracle

/-- **A round trip prints no money.** Swap `Δx` of X into the pool for
`Δy = swapOutput x y Δx` of Y, then swap that `Δy` straight back into the new
reserves `(x + Δx, y − Δy)`: the pool returns exactly `Δx`, so this round
trip neither gains nor loses. -/
theorem swap_round_trip (x y Δx : ℝ) (hx : 0 < x) (hy : 0 < y) (hΔx : 0 < Δx) :
    swapOutput (y - swapOutput x y Δx) (x + Δx) (swapOutput x y Δx) = Δx := by
  have hxΔ : x + Δx ≠ 0 := by positivity
  simp only [swapOutput, sub_add_cancel]
  rw [mul_div_assoc', mul_div_cancel_left₀ _ hxΔ, mul_div_cancel_left₀ _ hy.ne']

/-- **The marginal execution rate**: the derivative of the swap output in the
input size is `x y / (x + Δx)²`. -/
theorem hasDerivAt_swapOutput (y : ℝ) {x Δx : ℝ} (h : x + Δx ≠ 0) :
    HasDerivAt (swapOutput x y) (x * y / (x + Δx) ^ 2) Δx := by
  rw [show x * y / (x + Δx) ^ 2 = (y * 1 * (x + Δx) - y * Δx * 1) / (x + Δx) ^ 2 by ring]
  exact ((hasDerivAt_id' Δx).const_mul y).div ((hasDerivAt_id' Δx).const_add x) h

/-- **The internal price is the marginal price.** At zero size the swap pays
`y / x` per unit of input: `d(swapOutput x y)/dΔx (0) = internalPrice x y`. -/
theorem hasDerivAt_swapOutput_zero (y : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (swapOutput x y) (internalPrice x y) 0 := by
  have h := hasDerivAt_swapOutput y (x := x) (Δx := 0) (by simpa using hx.ne')
  rw [add_zero, sq, mul_comm x y, mul_div_mul_right y x hx.ne'] at h
  exact h

/-- **Selling X to the pool pays exactly when the pool overprices X.** Buy
`Δx` of X at the oracle price `P` and sell it to the pool: for some size
`Δx > 0` the proceeds `swapOutput x y Δx` exceed the cost `P · Δx` if and only
if `P < y / x`. -/
theorem exists_profitable_swap_iff {x y P : ℝ} (hx : 0 < x) (hP : 0 < P) :
    (∃ Δx > 0, P * Δx < swapOutput x y Δx) ↔ P < internalPrice x y := by
  have key (Δx : ℝ) (hΔx : 0 < Δx) : P * Δx < swapOutput x y Δx ↔ P * (x + Δx) < y := by
    rw [swapOutput, lt_div_iff₀ (by linarith)]
    constructor <;> intro h <;> nlinarith
  rw [internalPrice, lt_div_iff₀ hx]
  constructor
  · rintro ⟨Δx, hΔx, h⟩
    linarith [(key Δx hΔx).mp h, mul_pos hP hΔx]
  · intro h
    have hΔ : 0 < (y - P * x) / (2 * P) := div_pos (by linarith) (by positivity)
    have hPΔ : P * ((y - P * x) / (2 * P)) = (y - P * x) / 2 := by
      rw [mul_div_assoc', mul_comm 2 P, mul_div_mul_left _ _ hP.ne']
    exact ⟨_, hΔ, (key _ hΔ).mpr (by linarith)⟩

/-- **Buying X from the pool pays exactly when the pool underprices X.** Sell
`Δy` of Y to the pool and the X received at the oracle price `P`: for some size
`Δy > 0` the proceeds `P · swapOutput y x Δy` exceed `Δy` if and only if
`y / x < P`. -/
theorem exists_profitable_reverse_swap_iff {x y P : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∃ Δy > 0, Δy < P * swapOutput y x Δy) ↔ internalPrice x y < P := by
  have key (Δy : ℝ) (hΔy : 0 < Δy) : Δy < P * swapOutput y x Δy ↔ y + Δy < P * x := by
    rw [swapOutput, mul_div_assoc', lt_div_iff₀ (by linarith)]
    constructor <;> intro h <;> nlinarith
  rw [internalPrice, div_lt_iff₀ hx]
  constructor
  · rintro ⟨Δy, hΔy, h⟩
    linarith [(key Δy hΔy).mp h]
  · intro h
    have hΔ : 0 < (P * x - y) / 2 := by linarith
    exact ⟨_, hΔ, (key _ hΔ).mpr (by linarith)⟩

/-- **`arbitragePresent` means what it says.** For positive reserves and a
positive oracle price `P`, the pool price differs from `P` if and only if some
single fee-free swap against the pool, valued at `P`, earns a riskless profit:
selling X to the pool when it overprices X, or buying X from it when it
underprices X. Equivalently, a pool at the oracle price admits no profitable
swap of any size. -/
theorem arbitragePresent_iff {x y P : ℝ} (hx : 0 < x) (hy : 0 < y) (hP : 0 < P) :
    arbitragePresent x y P ↔
      (∃ Δx > 0, P * Δx < swapOutput x y Δx) ∨ (∃ Δy > 0, Δy < P * swapOutput y x Δy) := by
  rw [exists_profitable_swap_iff hx hP, exists_profitable_reverse_swap_iff hx hy,
    arbitragePresent, ne_comm, ne_iff_lt_or_gt]

end DeFi

end MathFin
