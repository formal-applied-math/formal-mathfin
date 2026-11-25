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

The whitepaper's weights are normalized (`∑ k, w k = 1`), which makes `V` the invariant of
a constant-value-share (weighted) portfolio; the trades-preserve, out-amount and spot-price
statements here hold for arbitrary positive weights and are proved at that generality. Fees
are not modelled (the fee factor is one), as in `ConstantProductAMM.lean`.

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
* `constantMeanInvariant_pair`, `spotPrice_pair`: the invariant and the spot price of a
  two-token pool with arbitrary weights.
* `prod_update_pow`: splitting a product of powers over an updated reserve vector (a
  `Finset.prod_update` companion for power summands).

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
This is a value only for positive reserves and weights, the hypotheses the theorems here
carry at the minimum their proofs need (the derivative theorem needs only the input
reserve's positivity); on a nonpositive reserve `Real.rpow` is junk. The whitepaper
normalizes the weights
(`∑ k, w k = 1`), which makes `V` the invariant of a constant-value-share (weighted)
portfolio; the statements proved here need only positivity. -/
noncomputable def constantMeanInvariant (B : ι → ℝ) (w : ι → ℝ) : ℝ :=
  ∏ k, B k ^ w k

/-- **Out-amount of a constant-mean swap**: sending `Δ` of token `i` into the pool returns

  `B j * (1 - (B i / (B i + Δ)) ^ (w i / w j))`

of token `j`, the whitepaper's Out-Given-In formula, fee-free. The output reserve implied is
`B j - swapOut B w i j Δ = B j * (B i / (B i + Δ)) ^ (w i / w j)`. The value means a trade
only where `B i + Δ > 0`: at `B i + Δ = 0` it is the whole reserve `B j`, and on a negative
denominator `Real.rpow` is junk (the theorems carry `0 < B i` and `0 < Δ`). -/
noncomputable def swapOut (B : ι → ℝ) (w : ι → ℝ) (i j : ι) (Δ : ℝ) : ℝ :=
  B j * (1 - (B i / (B i + Δ)) ^ (w i / w j))

/-- **Spot price of a constant-mean pool**: the units of token `j` out per unit of token `i`
in, `(B j / w j) / (B i / w i)`, a ratio of reserve-to-weight ratios. That this is the marginal
rate of `swapOut` at zero trade is `hasDerivAt_swapOut_zero`; the whitepaper prints the same
ratio with in and out exchanged (`SP^o_i = (B i / w i) / (B o / w o)`, the price of `o` in
units of `i`, the paper's superscript naming the priced asset). Meaningful for positive
reserves and weights. -/
noncomputable def spotPrice (B : ι → ℝ) (w : ι → ℝ) (i j : ι) : ℝ :=
  (B j / w j) / (B i / w i)

/-- **Post-trade reserve vector** of a constant-mean swap of `Δ` of token `i` in for
`swapOut B w i j Δ` of token `j` out: token `i`'s reserve grows by `Δ`, token `j`'s shrinks by
the out-amount, the others are untouched. At `i = j` the second write wins and the value is
not a post-trade reserve; every consuming theorem carries `i ≠ j`. -/
noncomputable def swapReserves (B : ι → ℝ) (w : ι → ℝ) (i j : ι) (Δ : ℝ) : ι → ℝ :=
  Function.update (Function.update B i (B i + Δ)) j (B j - swapOut B w i j Δ)

omit [Fintype ι] [DecidableEq ι] in
/-- **A positive input returns a positive amount**: for positive reserves and weights, the
out-amount of a positive input is positive. -/
theorem swapOut_pos (B : ι → ℝ) (w : ι → ℝ) (i j : ι) {Δ : ℝ}
    (hBi : 0 < B i) (hBj : 0 < B j) (hwi : 0 < w i) (hwj : 0 < w j) (hΔ : 0 < Δ) :
    0 < swapOut B w i j Δ := by
  have hsum : 0 < B i + Δ := by linarith [hBi]
  have hr : 0 < B i / (B i + Δ) := div_pos hBi hsum
  have hlt : (B i / (B i + Δ)) ^ (w i / w j) < 1 :=
    Real.rpow_lt_one hr.le (by rw [div_lt_iff₀ hsum]; linarith) (div_pos hwi hwj)
  unfold swapOut
  exact mul_pos hBj (by linarith)

omit [Fintype ι] [DecidableEq ι] in
/-- **A swap cannot drain the pool**: the out-amount is below the output reserve, so the
post-trade reserve `B j - swapOut B w i j Δ` stays positive. -/
theorem swapOut_lt_reserve (B : ι → ℝ) (w : ι → ℝ) (i j : ι) {Δ : ℝ}
    (hBi : 0 < B i) (hBj : 0 < B j) (hΔ : 0 < Δ) :
    swapOut B w i j Δ < B j := by
  have hsum : 0 < B i + Δ := by linarith [hBi]
  have hr : 0 < B i / (B i + Δ) := div_pos hBi hsum
  have hpos : 0 < (B i / (B i + Δ)) ^ (w i / w j) := Real.rpow_pos_of_pos hr _
  unfold swapOut
  have h1 : 1 - (B i / (B i + Δ)) ^ (w i / w j) < 1 := by linarith
  calc B j * (1 - (B i / (B i + Δ)) ^ (w i / w j)) < B j * 1 :=
        mul_lt_mul_of_pos_left h1 hBj
    _ = B j := mul_one _

omit [Fintype ι] [DecidableEq ι] in
/-- The two factors the trade touches: the input token's power at the grown reserve times the
output token's power at the shrunk reserve is the pair's product of powers before the trade,
the constant-mean content of the whitepaper's Out-Given-In derivation. -/
private theorem out_pair_pow_eq (B : ι → ℝ) (w : ι → ℝ) (i j : ι) {Δ : ℝ}
    (hBi : 0 < B i) (hBj : 0 < B j) (hwj : 0 < w j) (hΔ : 0 < Δ) :
    (B i + Δ) ^ w i * (B j - swapOut B w i j Δ) ^ w j = B i ^ w i * B j ^ w j := by
  have hsum : 0 < B i + Δ := by linarith [hBi]
  have hr : 0 < B i / (B i + Δ) := div_pos hBi hsum
  have hrw : B j - swapOut B w i j Δ = B j * (B i / (B i + Δ)) ^ (w i / w j) := by
    unfold swapOut; ring
  have hwi : w i / w j * w j = w i := div_mul_cancel₀ (w i) hwj.ne'
  have hbi : (B i + Δ) ^ w i * (B i / (B i + Δ)) ^ w i = B i ^ w i := by
    rw [← Real.mul_rpow hsum.le hr.le, mul_comm, div_mul_cancel₀ _ hsum.ne']
  rw [hrw, Real.mul_rpow hBj.le (Real.rpow_pos_of_pos hr _).le, ← Real.rpow_mul hr.le, hwi,
    show (B i + Δ) ^ w i * (B j ^ w j * (B i / (B i + Δ)) ^ w i)
      = B j ^ w j * ((B i + Δ) ^ w i * (B i / (B i + Δ)) ^ w i) from by ring, hbi]
  ring

omit [Fintype ι] in
/-- Splitting a product of powers over an updated reserve vector: the updated token
contributes its new power, the rest are unchanged. -/
theorem prod_update_pow (w : ι → ℝ) (f : ι → ℝ) (a : ι) (c : ℝ) (s : Finset ι)
    (h : a ∈ s) :
    ∏ k ∈ s, Function.update f a c k ^ w k = c ^ w a * ∏ k ∈ s.erase a, f k ^ w k := by
  have hfun : (fun k ↦ Function.update f a c k ^ w k)
      = Function.update (fun k ↦ f k ^ w k) a (c ^ w a) := by
    funext k
    by_cases hka : k = a
    · subst hka
      simp
    · simp [hka]
  rw [hfun, Finset.prod_update_of_mem h, Finset.sdiff_singleton_eq_erase]

/-- **Trades preserve the constant-mean invariant**: after a swap of `Δ` of token `i` in for
`swapOut B w i j Δ` of token `j` out, the weighted product of the new reserves equals the
weighted product of the old. This is the pricing rule of the constant-mean pool: the swap is
the trade that keeps the weighted product fixed. -/
theorem swap_preserves_constantMean (B : ι → ℝ) (w : ι → ℝ) (i j : ι) {Δ : ℝ}
    (hBi : 0 < B i) (hBj : 0 < B j) (hwj : 0 < w j) (hij : i ≠ j) (hΔ : 0 < Δ) :
    ∏ k, swapReserves B w i j Δ k ^ w k = constantMeanInvariant B w := by
  have hE : (Finset.univ.erase j).erase i = (Finset.univ.erase i).erase j :=
    Finset.ext fun k ↦ by simp [Finset.mem_erase, and_comm]
  have hL : ∏ k, swapReserves B w i j Δ k ^ w k
      = (B j - swapOut B w i j Δ) ^ w j * ((B i + Δ) ^ w i
          * ∏ k ∈ (Finset.univ.erase i).erase j, B k ^ w k) := by
    unfold swapReserves
    rw [prod_update_pow w _ j _ Finset.univ (Finset.mem_univ j),
      prod_update_pow w _ i (B i + Δ) (Finset.univ.erase j)
        (Finset.mem_erase.2 ⟨hij, Finset.mem_univ _⟩), hE]
  have hR : constantMeanInvariant B w
      = B i ^ w i * (B j ^ w j * ∏ k ∈ (Finset.univ.erase i).erase j, B k ^ w k) := by
    unfold constantMeanInvariant
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) _
        (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ _⟩)]
  have hpair := out_pair_pow_eq B w i j hBi hBj hwj hΔ
  rw [hL, hR, ← mul_assoc, ← mul_assoc, ← hpair]
  rw [mul_comm ((B j - swapOut B w i j Δ) ^ w j) ((B i + Δ) ^ w i)]

omit [Fintype ι] [DecidableEq ι] in
/-- **The spot price is the marginal rate.** At zero trade size the out-amount pays
`(B j / w j) / (B i / w i)` units of token `j` per unit of token `i`: the derivative of the
out-amount in the input at `Δ = 0` is `spotPrice B w i j`. This derives the reserve-to-weight
ratio formula from the constant-mean surface; the whitepaper prints the same ratio with in
and out exchanged. Meaningful where the spot price is — positive reserves and weights; the
`0 < B i` hypothesis keeps the statement out of the junk region. -/
theorem hasDerivAt_swapOut_zero (B : ι → ℝ) (w : ι → ℝ) (i j : ι)
    (hBi : 0 < B i) :
    HasDerivAt (swapOut B w i j) (spotPrice B w i j) 0 := by
  have hunit : B i / (B i + (0 : ℝ)) = 1 := by
    rw [add_zero, div_self hBi.ne']
  have hz : B i + (0 : ℝ) ≠ 0 := by simpa using hBi.ne'
  have hadd : HasDerivAt (fun t ↦ B i + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add (B i)
  have hu : HasDerivAt (fun t ↦ B i / (B i + t)) (-(B i) / (B i) ^ 2) 0 := by
    have h := HasDerivAt.fun_div (hasDerivAt_const (0 : ℝ) (B i)) hadd hz
    convert h using 1
    ring
  have hrpow0 := hu.rpow_const (p := w i / w j) (Or.inl (by rw [hunit]; exact one_ne_zero))
  rw [hunit, Real.one_rpow, mul_one] at hrpow0
  have hrpow : HasDerivAt (fun t ↦ (B i / (B i + t)) ^ (w i / w j))
      (-(B i) / (B i) ^ 2 * (w i / w j)) 0 := hrpow0
  have hfin := (HasDerivAt.fun_sub (hasDerivAt_const (0 : ℝ) (1 : ℝ)) hrpow).const_mul (B j)
  unfold spotPrice swapOut
  convert hfin using 1
  field_simp
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The invariant of a two-token pool with weights `w₁` on X and `w₂` on Y. -/
theorem constantMeanInvariant_pair (x y w₁ w₂ : ℝ) :
    constantMeanInvariant ![x, y] ![w₁, w₂] = x ^ w₁ * y ^ w₂ := by
  simp only [constantMeanInvariant, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]

omit [Fintype ι] [DecidableEq ι] in
/-- The spot price of a two-token pool with weights `w₁` on X and `w₂` on Y: the units of
token Y per unit of token X. -/
theorem spotPrice_pair (x y w₁ w₂ : ℝ) :
    spotPrice ![x, y] ![w₁, w₂] 0 1 = (y / w₂) / (x / w₁) := by
  simp only [spotPrice, Matrix.cons_val_zero, Matrix.cons_val_one]

omit [Fintype ι] [DecidableEq ι] in
/-- **The equal-weight two-token invariant is the constant-product invariant**: at `n = 2` with
`w = ![1/2, 1/2]`, the squared constant-mean invariant is the product of the two reserves,
so the surface `V = √(x·y)` is the Uniswap curve `x·y = k` written in squared form. -/
theorem constantMeanInvariant_two_sq_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (constantMeanInvariant (![x, y] : Fin 2 → ℝ) ![1/2, 1/2]) ^ 2 = x * y := by
  have hx2 : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hx.le]
    norm_num
  have hy2 : (y ^ ((1 : ℝ) / 2)) ^ 2 = y := by
    rw [← Real.rpow_natCast (y ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hy.le]
    norm_num
  unfold constantMeanInvariant
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_pow, hx2, hy2]

omit [Fintype ι] [DecidableEq ι] in
/-- **The equal-weight two-token spot price is the constant-product internal price**: the
marginal rate of the two-token equal-weight pool is `internalPrice x y = y / x`. -/
theorem spotPrice_two_eq_internalPrice (x y : ℝ) :
    spotPrice (![x, y] : Fin 2 → ℝ) ![1/2, 1/2] 0 1 = internalPrice x y := by
  unfold spotPrice internalPrice
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

omit [Fintype ι] [DecidableEq ι] in
/-- **The equal-weight two-token out-amount is the constant-product swap output**: the
whitepaper's Out-Given-In at `w i = w j = 1/2` is `swapOutput x y Δ = y * Δ / (x + Δ)`. -/
theorem swapOut_two_eq_swapOutput (x y Δ : ℝ) (hx : 0 < x) (hΔ : 0 < Δ) :
    swapOut (![x, y] : Fin 2 → ℝ) ![1/2, 1/2] 0 1 Δ = swapOutput x y Δ := by
  have hhalf : ((1 : ℝ) / 2) / ((1 : ℝ) / 2) = 1 :=
    div_self (by norm_num : ((1 : ℝ) / 2) ≠ 0)
  have hsum : 0 < x + Δ := by linarith
  unfold swapOut swapOutput
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hhalf]
  field_simp
  ring

end DeFi

end MathFin
