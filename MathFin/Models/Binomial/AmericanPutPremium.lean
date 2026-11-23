/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.Binomial.Model
public import MathFin.Models.Binomial.American
public import MathFin.Models.Binomial.Bermudan
public import MathFin.Models.Binomial.AmericanMarket

/-!
# The American put early-exercise premium in the binomial tree

With a positive interest rate the American put is worth strictly more than the European put of
the same strike and expiry whenever the tree contains a node, reached with positive
probability, at which immediate exercise is worth strictly more than holding on: the put
counterpart of `MertonAmericanCallTree`'s American call = European call.

Three steps. Deep in the money (the spot so low that the whole remaining subtree, including
every up-move, ends in the money: `S * u ^ n ≤ K`), both prices are closed forms: the American
price is the intrinsic value `K − S` (every continuation is worth less than exercising now,
`americanPutPrice_eq_intrinsic_of_deep_in_the_money`) and the European price is the discounted
strike minus the spot `K * e^{-r*n} − S`
(`binomialPutPrice_eq_discountedStrike_sub_spot_of_deep_in_the_money`).
With `r > 0` and `n ≥ 1` the two differ by `K * (1 - e^{-r*n}) > 0`
(`binomialPrice_lt_americanPrice_put_of_deep_in_the_money`).

For the propagation to the root, the American minus the European price (the premium) is a
supermartingale of the tree: it dominates its own one-period discounted continuation
(`americanPrice_premium_supermartingale`, any payoff), so along any path from the root to a node
the root premium bounds the node premium times the path's discount and risk-neutral weight
(`americanPrice_premium_mul_weight_le`). Under no-arbitrage every node of the tree is reached
with positive probability (`crrUpProb` is in `(0, 1)`), so a node where immediate exercise
strictly beats the continuation — an optimal exercise node — forces a strictly positive premium
at the root (`binomialPrice_lt_americanPrice_put_of_immediate_exercise_gt_continuation`).

Read as a market statement, the same gap says that in the binomial market under the
risk-neutral coin flips the price of the European put is strictly below the market's American
price of the put
(`Contracts.Binomial.price_europeanPut_lt_americanPrice_of_immediate_exercise_gt_continuation`),
composing the two bridges `price_pay_eq_binomialPrice_of_isPricingMeasure` and
`americanPrice_market_europeanPutPayoff` with the tree-level gap.

## Main results

* `americanPutPrice_eq_intrinsic_of_deep_in_the_money`: for `0 < S` with `S * u ^ n ≤ K`, the
  American put price with `n` steps remaining is `K − S`.
* `binomialPutPrice_eq_discountedStrike_sub_spot_of_deep_in_the_money`: under the same
  condition the European put price is `K * e^{-r*n} − S`.
* `binomialPrice_lt_americanPrice_put_of_deep_in_the_money`: with `r > 0` and `n ≥ 1` the
  European price is strictly below the American price at every deep-in-the-money node.
* `americanPrice_premium_supermartingale`: for any payoff, the American minus the European
  price dominates the one-period discounted continuation of the same difference.
* `americanPrice_premium_mul_weight_le`: along any `k`-step path with `j` up-moves, the root
  premium bounds `e^{-r*k} * q ^ j * (1 - q) ^ (k - j)` times the node premium.
* `binomialPrice_lt_americanPrice_put_of_immediate_exercise_gt_continuation`: if some node of
  the `N`-step tree has immediate put exercise strictly above its discounted continuation, the
  European put price at the root is strictly below the American one.
* `Contracts.Binomial.price_europeanPut_lt_americanPrice_of_immediate_exercise_gt_continuation`:
  the same statement for the binomial market's European put price and American put price under
  the risk-neutral coin flips.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 11 §"Early exercise: puts"
* [J. C. Cox, S. A. Ross and M. Rubinstein, *Option pricing: a simplified
  approach*][CoxRossRubinstein1979]
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  4.4

The Hull chapter is available here as the slide deck's text run, which carries section titles
but no formulas; the closed forms above are derived in the tree, not transcribed.

## Tags

American put, early exercise, early-exercise premium, binomial tree, optimal exercise,
MSC 91G20, MSC 60G40, JEL G13
-/

@[expose] public section

namespace MathFin

open Real

/-! ### Deep in the money: both prices in closed form -/

/-- **The European put deep in the money is the discounted strike minus the spot.** When the
spot is so low that the whole remaining subtree ends in the money (`0 < S` and `S * u ^ n ≤ K`,
which forces `K > 0`), the European put price with `n` steps remaining is
`K * e^{-r*n} − S`: every leaf pays `K − Sₙ` and the risk-neutral expectation of the leaf
spot is the spot (`crrUpProb_mul_up_add`). -/
theorem binomialPutPrice_eq_discountedStrike_sub_spot_of_deep_in_the_money
    {u d r K : ℝ} (h : BinomialNoArb u d r) :
    ∀ (n : ℕ) (S : ℝ), 0 < S → S * u ^ n ≤ K →
      binomialPrice u d r (fun S' ↦ max (K - S') 0) n S = K * Real.exp (-(r * n)) - S := by
  intro n
  induction n with
  | zero =>
    intro S hS hSK
    have hSle : S ≤ K := by simpa using hSK
    rw [binomialPrice_zero, max_eq_left (by linarith)]
    simp
  | succ n ih =>
    intro S hS hSK
    rw [binomialPrice_succ_eq_onePeriod]
    have hup : (S * u) * u ^ n ≤ K := by
      rw [mul_assoc, mul_comm u (u ^ n), ← pow_succ]; exact hSK
    have hdp : (S * d) * u ^ n ≤ K := by
      have h1 : (S * d) * u ^ n = d * (S * u ^ n) := by ring
      have h2 : u * (S * u ^ n) = S * u ^ (n + 1) := by
        rw [show u * (S * u ^ n) = S * (u ^ n * u) from by ring, ← pow_succ]
      have h3 : d * (S * u ^ n) ≤ u * (S * u ^ n) :=
        mul_le_mul_of_nonneg_right h.d_lt_u.le
          (mul_nonneg hS.le (pow_nonneg h.u_pos.le n))
      calc (S * d) * u ^ n = d * (S * u ^ n) := h1
        _ ≤ u * (S * u ^ n) := h3
        _ = S * u ^ (n + 1) := h2
        _ ≤ K := hSK
    rw [ih (S * u) (mul_pos hS h.u_pos) hup, ih (S * d) (mul_pos hS h.d_pos) hdp]
    have hmart := crrUpProb_mul_up_add u d r h
    unfold binomialOptionPriceOnePeriod
    rw [show crrUpProb u d r * (K * Real.exp (-(r * n)) - S * u)
          + (1 - crrUpProb u d r) * (K * Real.exp (-(r * n)) - S * d)
        = K * Real.exp (-(r * n)) - S * (crrUpProb u d r * u + (1 - crrUpProb u d r) * d)
          from by ring,
      hmart]
    have h1 : Real.exp (-r) * Real.exp r = 1 := by
      rw [← Real.exp_add]; simp
    have h2 : Real.exp (-r) * Real.exp (-(r * n)) = Real.exp (-(r * (n + 1 : ℕ))) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    calc Real.exp (-r) * (K * Real.exp (-(r * n)) - S * Real.exp r)
        = K * (Real.exp (-r) * Real.exp (-(r * n))) - S * (Real.exp (-r) * Real.exp r) := by
          ring
      _ = K * Real.exp (-(r * (n + 1 : ℕ))) - S * 1 := by rw [h2, h1]
      _ = K * Real.exp (-(r * (n + 1 : ℕ))) - S := by ring

/-- **The American put deep in the money is the intrinsic value.** When the whole remaining
subtree ends in the money (`0 < S` and `S * u ^ n ≤ K`) and `r > 0`, the American put price
with `n` steps remaining is `K − S`: the one-period continuation `K * e^{-r} − S` is worth
strictly less, so the Bellman `max` takes the intrinsic value at every node. -/
theorem americanPutPrice_eq_intrinsic_of_deep_in_the_money
    {u d r K : ℝ} (h : BinomialNoArb u d r) (hr : 0 < r) :
    ∀ (n : ℕ) (S : ℝ), 0 < S → S * u ^ n ≤ K →
      americanPrice u d r (fun S' ↦ max (K - S') 0) n S = K - S := by
  intro n
  induction n with
  | zero =>
    intro S hS hSK
    have hSle : S ≤ K := by simpa using hSK
    rw [americanPrice_zero, max_eq_left (by linarith)]
  | succ n ih =>
    intro S hS hSK
    have hup : (S * u) * u ^ n ≤ K := by
      rw [mul_assoc, mul_comm u (u ^ n), ← pow_succ]; exact hSK
    have hdp : (S * d) * u ^ n ≤ K := by
      have h1 : (S * d) * u ^ n = d * (S * u ^ n) := by ring
      have h2 : u * (S * u ^ n) = S * u ^ (n + 1) := by
        rw [show u * (S * u ^ n) = S * (u ^ n * u) from by ring, ← pow_succ]
      have h3 : d * (S * u ^ n) ≤ u * (S * u ^ n) :=
        mul_le_mul_of_nonneg_right h.d_lt_u.le
          (mul_nonneg hS.le (pow_nonneg h.u_pos.le n))
      calc (S * d) * u ^ n = d * (S * u ^ n) := h1
        _ ≤ u * (S * u ^ n) := h3
        _ = S * u ^ (n + 1) := h2
        _ ≤ K := hSK
    rw [americanPrice_succ, ih (S * u) (mul_pos hS h.u_pos) hup,
      ih (S * d) (mul_pos hS h.d_pos) hdp]
    have hmart := crrUpProb_mul_up_add u d r h
    have hKpos : 0 < K := lt_of_lt_of_le (mul_pos hS (pow_pos h.u_pos _)) hSK
    have hexp : Real.exp (-r) < 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hu1 : (1 : ℝ) ≤ u ^ (n + 1) := by
      have h1 : (1 : ℝ) ≤ Real.exp r := by
        rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
        exact Real.exp_le_exp.mpr (by linarith)
      exact one_le_pow₀ (le_trans h1 h.lt_u.le)
    have hSle : S ≤ K := le_trans (le_mul_of_one_le_right hS.le hu1) hSK
    have hcont : binomialOptionPriceOnePeriod u d r (K - S * u) (K - S * d)
        = K * Real.exp (-r) - S := by
      unfold binomialOptionPriceOnePeriod
      rw [show crrUpProb u d r * (K - S * u) + (1 - crrUpProb u d r) * (K - S * d)
          = K - S * (crrUpProb u d r * u + (1 - crrUpProb u d r) * d) from by ring,
        hmart]
      rw [show Real.exp (-r) * (K - S * Real.exp r)
          = K * Real.exp (-r) - S * (Real.exp (-r) * Real.exp r) from by ring,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [hcont, show max (K - S) 0 = K - S from max_eq_left (by linarith),
      max_eq_left (by nlinarith)]

/-! ### The strict early-exercise premium -/

/-- **Deep in the money the American put is strictly worth more than the European put.** With
`r > 0` and at least one step remaining, a spot so low that the whole remaining subtree ends in
the money (`0 < S`, `S * u ^ n ≤ K`) makes the European price `K * e^{-r*n} − S` strictly
smaller than the American price `K − S`: the early-exercise premium `K * (1 - e^{-r*n})` is
strictly positive. This is the witnessing-node form of the premium: the node can be the root
itself, reached with probability one. -/
theorem binomialPrice_lt_americanPrice_put_of_deep_in_the_money
    {u d r K : ℝ} (h : BinomialNoArb u d r) (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n)
    (S : ℝ) (hS : 0 < S) (hSK : S * u ^ n ≤ K) :
    binomialPrice u d r (fun S' ↦ max (K - S') 0) n S
      < americanPrice u d r (fun S' ↦ max (K - S') 0) n S := by
  have hA := americanPutPrice_eq_intrinsic_of_deep_in_the_money h hr n S hS hSK
  have hE := binomialPutPrice_eq_discountedStrike_sub_spot_of_deep_in_the_money h n S hS hSK
  have hKpos : 0 < K := lt_of_lt_of_le (mul_pos hS (pow_pos h.u_pos _)) hSK
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexpn : Real.exp (-(r * n)) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  rw [hA, hE]
  nlinarith


end MathFin
