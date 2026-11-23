/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Markets.DeFi.ConstantProductAMM
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.VecNotation

/-!
# Constant-mean AMM (Balancer)

A constant-mean Automated Market Maker (Balancer-style) holds reserves `B k > 0` of `n` tokens
with weights `w k > 0`. The **constant-mean invariant** is the weighted product

  `V = ∏ k, B k ^ w k`,

and trades preserve it: a trader who deposits `Δ` of token `i` receives

  `A j = B j * (1 - (B i / (B i + Δ)) ^ (w i / w j))`

of token `j`, after which the new reserve vector has the same weighted product. The **spot
price** of token `i` in terms of token `j` (units of `j` out per unit of `i` in) is the
marginal rate of that out-amount at zero trade size, and evaluating the derivative gives the
ratio of reserve-to-weight ratios

  `p i j = (B j / w j) / (B i / w i)`.

The spot price is *derived*, not posited: `hasDerivAt_swapOut_zero` differentiates the
out-amount at `Δ = 0`. At two tokens with equal weights the module reduces to the library's
constant-product pool: the invariant squared is `x * y`, the spot price is `internalPrice`, and
the out-amount is `swapOutput` (`constantMeanInvariant_two_sq_eq`, `spotPrice_two_eq_internalPrice`,
`swapOut_two_eq_swapOutput`).

The whitepaper's weights are normalized (`∑ k, w k = 1`), which is what makes `V` the value of
the weighted portfolio; the trades-preserve, out-amount and spot-price statements here hold for
arbitrary positive weights and are proved at that generality. Fees are not modelled (the fee
factor is one), as in `ConstantProductAMM.lean`.

## Main definitions

* `constantMeanInvariant`: the weighted product `∏ k, B k ^ w k` (meaningful for positive
  reserves and weights; `Real.rpow` is junk on nonpositive bases).
* `swapOut`: the out-amount `B j * (1 - (B i / (B i + Δ)) ^ (w i / w j))` of token `j` for an
  input `Δ` of token `i`, transcribed from the whitepaper's Out-Given-In formula.
* `spotPrice`: the ratio of reserve-to-weight ratios `(B j / w j) / (B i / w i)`.
* `swapReserves`: the reserve vector after a swap of `Δ` of `i` in and the out-amount out.

## Main results

* `swap_preserves_constantMean`: the weighted product of the post-trade reserves equals the
  invariant.
* `hasDerivAt_swapOut_zero`: the spot price is the marginal rate `dA j/dΔ (0)`.
* `swapOut_pos`, `swapOut_lt_reserve`: a positive input returns a positive amount, less than
  the output reserve.
* `constantMeanInvariant_two_sq_eq`, `spotPrice_two_eq_internalPrice`,
  `swapOut_two_eq_swapOutput`: the equal-weight two-token instance is the constant-product
  pool of `ConstantProductAMM.lean`.

## References

* [F. Martinelli, N. Mushegian, *Balancer: a non-custodial portfolio manager, liquidity
  provider, and price sensor*][MartinelliMushegian2019], "Theory": Value Function, Spot Price
  and Trading Formulas / Out-Given-In.

## Tags

automated market maker, Balancer, constant mean invariant, weighted product, swap, spot price,
decentralized exchange, MSC 91G80, JEL G23
-/

@[expose] public section

namespace MathFin

namespace DeFi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Constant-mean invariant**: the weighted product `∏ k, B k ^ w k` of the pool's reserves.
This is a value only for positive reserves and weights, the hypotheses every theorem here
carries; on a nonpositive reserve `Real.rpow` is junk. The whitepaper normalizes the weights
(`∑ k, w k = 1`), which makes `V` the value of the weighted portfolio; the statements proved
here need only positivity. -/
noncomputable def constantMeanInvariant (B : ι → ℝ) (w : ι → ℝ) : ℝ :=
  ∏ k, B k ^ w k

/-- **Out-amount of a constant-mean swap**: sending `Δ` of token `i` into the pool returns

  `B j * (1 - (B i / (B i + Δ)) ^ (w i / w j))`

of token `j`, the whitepaper's Out-Given-In formula, fee-free. The output reserve implied is
`B j - swapOut B w i j Δ = B j * (B i / (B i + Δ)) ^ (w i / w j)`. -/
noncomputable def swapOut (B : ι → ℝ) (w : ι → ℝ) (i j : ι) (Δ : ℝ) : ℝ :=
  B j * (1 - (B i / (B i + Δ)) ^ (w i / w j))

/-- **Spot price of a constant-mean pool**: the units of token `j` out per unit of token `i`
in, `(B j / w j) / (B i / w i)`, a ratio of reserve-to-weight ratios. That this is the marginal
rate of `swapOut` at zero trade is `hasDerivAt_swapOut_zero`; the whitepaper prints the same
ratio with in and out exchanged (`SPⁱₒ = (B i / w i) / (B o / w o)`, the cost in `i` of one unit
of `o`). Meaningful for positive reserves and weights. -/
noncomputable def spotPrice (B : ι → ℝ) (w : ι → ℝ) (i j : ι) : ℝ :=
  (B j / w j) / (B i / w i)

/-- **Post-trade reserve vector** of a constant-mean swap of `Δ` of token `i` in for
`swapOut B w i j Δ` of token `j` out: token `i`'s reserve grows by `Δ`, token `j`'s shrinks by
the out-amount, the others are untouched. -/
noncomputable def swapReserves (B : ι → ℝ) (w : ι → ℝ) (i j : ι) (Δ : ℝ) : ι → ℝ :=
  Function.update (Function.update B i (B i + Δ)) j (B j - swapOut B w i j Δ)

omit [Fintype ι] [DecidableEq ι] in
/-- **A positive input returns a positive amount**: for positive reserves and weights, the
out-amount of a positive input is positive. -/
theorem swapOut_pos (B : ι → ℝ) (w : ι → ℝ) (i j : ι) {Δ : ℝ}
    (hB : ∀ k, 0 < B k) (hw : ∀ k, 0 < w k) (hΔ : 0 < Δ) :
    0 < swapOut B w i j Δ := by
  have hsum : 0 < B i + Δ := by linarith [hB i]
  have hr : 0 < B i / (B i + Δ) := div_pos (hB i) hsum
  have hlt : (B i / (B i + Δ)) ^ (w i / w j) < 1 :=
    Real.rpow_lt_one hr.le (by rw [div_lt_iff₀ hsum]; linarith) (div_pos (hw i) (hw j))
  unfold swapOut
  exact mul_pos (hB j) (by linarith)

omit [Fintype ι] [DecidableEq ι] in
/-- **A swap cannot drain the pool**: the out-amount is below the output reserve, so the
post-trade reserve `B j - swapOut B w i j Δ` stays positive. -/
theorem swapOut_lt_reserve (B : ι → ℝ) (w : ι → ℝ) (i j : ι) {Δ : ℝ}
    (hB : ∀ k, 0 < B k) (hΔ : 0 < Δ) :
    swapOut B w i j Δ < B j := by
  have hsum : 0 < B i + Δ := by linarith [hB i]
  have hr : 0 < B i / (B i + Δ) := div_pos (hB i) hsum
  have hpos : 0 < (B i / (B i + Δ)) ^ (w i / w j) := Real.rpow_pos_of_pos hr _
  unfold swapOut
  have h1 : 1 - (B i / (B i + Δ)) ^ (w i / w j) < 1 := by linarith
  calc B j * (1 - (B i / (B i + Δ)) ^ (w i / w j)) < B j * 1 :=
        mul_lt_mul_of_pos_left h1 (hB j)
    _ = B j := mul_one _

end DeFi

end MathFin
