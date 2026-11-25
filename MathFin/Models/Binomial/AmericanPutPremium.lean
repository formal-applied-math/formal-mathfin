/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.Binomial.Model
public import MathFin.Models.Binomial.American
public import MathFin.Models.Binomial.Bermudan
public import MathFin.Models.Binomial.Market
public import MathFin.Models.Binomial.AmericanMarket

/-!
# The American put early-exercise premium in the binomial tree

With a positive interest rate the American put is worth strictly more than the European put of
the same strike and expiry whenever the tree contains a node, reached with positive
probability, at which immediate exercise is worth strictly more than holding on: the put
counterpart of `MertonAmericanCallTree`'s American call = European call.

Three steps. Deep in the money (the spot so low that the whole remaining subtree, including
every up-move, ends in the money: `S * u ^ n ≤ K`), both prices are closed forms: the American
price is the intrinsic value `K − S` (every continuation is worth at most exercising now —
strictly less for `r > 0`; `americanPutPrice_eq_intrinsic_of_deep_in_the_money`) and the
European price is the discounted
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

* `americanPutPrice_eq_intrinsic_of_deep_in_the_money`: for `0 < S` with `S * u ^ n ≤ K` and
  `0 ≤ r`, the American put price with `n` steps remaining is `K − S`.
* `binomialPutPrice_eq_discountedStrike_sub_spot_of_deep_in_the_money`: under the same
  condition the European put price is `K * e^{-r*n} − S`.
* `immediate_exercise_gt_continuation_of_deep_in_the_money`: for `r > 0` and `n ≥ 1`, a
  whole-subtree-in-the-money spot satisfies the witnessing condition of the frontier theorem
  with the witness at the root.
* `binomialPrice_lt_americanPrice_put_of_deep_in_the_money`: with `r > 0` and `n ≥ 1` the
  European price is strictly below the American price at every deep-in-the-money node —
  derived from the frontier statement through the witness above.
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
subtree ends in the money (`0 < S` and `S * u ^ n ≤ K`) and `0 ≤ r`, the American put price
with `n` steps remaining is `K − S`: the one-period continuation `K * e^{-r} − S` is worth at
most the intrinsic value (strictly less when `r > 0`), so the Bellman `max` takes the
intrinsic value at every node. -/
theorem americanPutPrice_eq_intrinsic_of_deep_in_the_money
    {u d r K : ℝ} (h : BinomialNoArb u d r) (hr : 0 ≤ r) :
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
    have hexp : Real.exp (-r) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.mpr (by linarith)
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

/-! ### Propagation of the premium to the root -/

/-- **The premium dominates its own discounted continuation.** For any payoff, the difference
between the American and the European price satisfies the supermartingale inequality of the
tree: its one-period discounted continuation at the two successors is at most its value one
step earlier. The American recursion takes a `max` the European one does not, and the one-period
price is affine in the successor values. -/
theorem americanPrice_premium_supermartingale (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    binomialOptionPriceOnePeriod u d r
      (americanPrice u d r g n (S * u) - binomialPrice u d r g n (S * u))
      (americanPrice u d r g n (S * d) - binomialPrice u d r g n (S * d))
    ≤ americanPrice u d r g (n + 1) S - binomialPrice u d r g (n + 1) S := by
  rw [americanPrice_succ, binomialPrice_succ_eq_onePeriod]
  have haff : binomialOptionPriceOnePeriod u d r
      (americanPrice u d r g n (S * u) - binomialPrice u d r g n (S * u))
      (americanPrice u d r g n (S * d) - binomialPrice u d r g n (S * d))
    = binomialOptionPriceOnePeriod u d r (americanPrice u d r g n (S * u))
        (americanPrice u d r g n (S * d))
      - binomialOptionPriceOnePeriod u d r (binomialPrice u d r g n (S * u))
        (binomialPrice u d r g n (S * d)) := by
    unfold binomialOptionPriceOnePeriod; ring
  rw [haff]
  have hmax := le_max_right (g S)
    (binomialOptionPriceOnePeriod u d r (americanPrice u d r g n (S * u))
      (americanPrice u d r g n (S * d)))
  linarith

/-- **The premium at the root bounds every path-weighted premium below it.** For any payoff,
`j + i` steps down from the root with `j` up-moves and `i` down-moves, the premium at the root
dominates the premium at that node times the discount `e^{-r*(j+i)}` and the risk-neutral path
weight `q ^ j * (1 - q) ^ i`. Iterating `americanPrice_premium_supermartingale` along a single
path: the up-step uses the risk-neutral weight of an up-move, the down-step that of a
down-move, and the sibling term is dropped, being nonnegative by
`bermudanPrice_mono`. Under no-arbitrage the weight is strictly positive (`q ∈ (0, 1)`), and
every node of the tree is of this form, so a strictly positive premium at any node propagates
to the root. -/
theorem americanPrice_premium_mul_weight_le {u d r : ℝ} (h : BinomialNoArb u d r)
    (g : ℝ → ℝ) :
    ∀ (j i N : ℕ) (_hN : j + i ≤ N) (S : ℝ),
    Real.exp (-(r * (j + i : ℕ))) * crrUpProb u d r ^ j * (1 - crrUpProb u d r) ^ i *
      (americanPrice u d r g (N - j - i) (S * u ^ j * d ^ i)
        - binomialPrice u d r g (N - j - i) (S * u ^ j * d ^ i))
    ≤ americanPrice u d r g N S - binomialPrice u d r g N S := by
  have hq := crrUpProb_mem_Ioo h
  have hq0 : 0 < crrUpProb u d r := hq.1
  have hq1 : crrUpProb u d r < 1 := hq.2
  have hExpPos : 0 < Real.exp (-r) := Real.exp_pos _
  have hDnn : ∀ (m : ℕ) (x : ℝ),
      0 ≤ americanPrice u d r g m x - binomialPrice u d r g m x := by
    intro m x
    unfold americanPrice binomialPrice
    exact sub_nonneg_of_le (bermudanPrice_mono h g (Set.empty_subset Set.univ) m x)
  intro j
  induction j with
  | zero =>
    intro i
    induction i with
    | zero =>
      intro N _hN S
      simp only [Nat.sub_zero, pow_zero, mul_one, add_zero, Real.exp_zero,
        Nat.cast_zero, mul_zero, neg_zero]
      simp
    | succ i ih =>
      intro N hN S
      obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      subst hm
      have hstep := americanPrice_premium_supermartingale u d r g m S
      have hle := ih m (by omega) (S * d)
      have hsib : 0 ≤ crrUpProb u d r *
          (americanPrice u d r g m (S * u) - binomialPrice u d r g m (S * u)) :=
        mul_nonneg hq0.le (hDnn m (S * u))
      have hexp : Real.exp (-(r * (0 + (i + 1) : ℕ)))
          = Real.exp (-r) * Real.exp (-(r * (0 + i : ℕ))) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have hidx : m + 1 - 0 - (i + 1) = m - 0 - i := by omega
      have hspot : S * u ^ 0 * d ^ (i + 1) = (S * d) * u ^ 0 * d ^ i := by
        rw [pow_succ]; ring
      have hpow : (1 - crrUpProb u d r) ^ (i + 1)
          = (1 - crrUpProb u d r) ^ i * (1 - crrUpProb u d r) := pow_succ _ _
      calc Real.exp (-(r * (0 + (i + 1) : ℕ))) * crrUpProb u d r ^ (0 : ℕ)
            * (1 - crrUpProb u d r) ^ (i + 1)
            * (americanPrice u d r g (m + 1 - 0 - (i + 1)) (S * u ^ 0 * d ^ (i + 1))
              - binomialPrice u d r g (m + 1 - 0 - (i + 1)) (S * u ^ 0 * d ^ (i + 1)))
          = Real.exp (-r) * ((1 - crrUpProb u d r)
              * (Real.exp (-(r * (0 + i : ℕ))) * crrUpProb u d r ^ (0 : ℕ)
                * (1 - crrUpProb u d r) ^ i
                * (americanPrice u d r g (m - 0 - i) ((S * d) * u ^ 0 * d ^ i)
                  - binomialPrice u d r g (m - 0 - i) ((S * d) * u ^ 0 * d ^ i)))) := by
            rw [hidx, hspot, hexp, hpow]
            simp only [pow_zero, mul_one]
            push_cast
            ring
        _ ≤ Real.exp (-r) * ((1 - crrUpProb u d r)
            * (americanPrice u d r g m (S * d) - binomialPrice u d r g m (S * d))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hle (by linarith)
        _ ≤ Real.exp (-r) * (crrUpProb u d r
            * (americanPrice u d r g m (S * u) - binomialPrice u d r g m (S * u))
            + (1 - crrUpProb u d r)
            * (americanPrice u d r g m (S * d) - binomialPrice u d r g m (S * d))) := by
            apply mul_le_mul_of_nonneg_left _ hExpPos.le
            linarith
        _ = binomialOptionPriceOnePeriod u d r
            (americanPrice u d r g m (S * u) - binomialPrice u d r g m (S * u))
            (americanPrice u d r g m (S * d) - binomialPrice u d r g m (S * d)) := rfl
        _ ≤ americanPrice u d r g (m + 1) S - binomialPrice u d r g (m + 1) S := hstep
  | succ j ih =>
    intro i N hN S
    obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    subst hm
    have hstep := americanPrice_premium_supermartingale u d r g m S
    have hle := ih i m (by omega) (S * u)
    have hsib : 0 ≤ (1 - crrUpProb u d r) *
        (americanPrice u d r g m (S * d) - binomialPrice u d r g m (S * d)) :=
      mul_nonneg (by linarith) (hDnn m (S * d))
    have hexp : Real.exp (-(r * (j + 1 + i : ℕ)))
        = Real.exp (-r) * Real.exp (-(r * (j + i))) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have hidx : m + 1 - (j + 1) - i = m - j - i := by omega
    have hspot : S * u ^ (j + 1) * d ^ i = (S * u) * u ^ j * d ^ i := by
      rw [pow_succ]; ring
    have hqp : crrUpProb u d r ^ (j + 1)
        = crrUpProb u d r ^ j * crrUpProb u d r := pow_succ _ _
    calc Real.exp (-(r * (j + 1 + i : ℕ))) * crrUpProb u d r ^ (j + 1)
          * (1 - crrUpProb u d r) ^ i
          * (americanPrice u d r g (m + 1 - (j + 1) - i) (S * u ^ (j + 1) * d ^ i)
            - binomialPrice u d r g (m + 1 - (j + 1) - i) (S * u ^ (j + 1) * d ^ i))
        = Real.exp (-r) * (crrUpProb u d r
            * (Real.exp (-(r * (j + i : ℕ))) * crrUpProb u d r ^ j
              * (1 - crrUpProb u d r) ^ i
              * (americanPrice u d r g (m - j - i) ((S * u) * u ^ j * d ^ i)
                - binomialPrice u d r g (m - j - i) ((S * u) * u ^ j * d ^ i)))) := by
          rw [hidx, hspot, hexp, hqp]
          push_cast
          ring
      _ ≤ Real.exp (-r) * (crrUpProb u d r
          * (americanPrice u d r g m (S * u) - binomialPrice u d r g m (S * u))) := by
          apply mul_le_mul_of_nonneg_left _ hExpPos.le
          exact mul_le_mul_of_nonneg_left hle hq0.le
      _ ≤ Real.exp (-r) * (crrUpProb u d r
          * (americanPrice u d r g m (S * u) - binomialPrice u d r g m (S * u))
          + (1 - crrUpProb u d r)
          * (americanPrice u d r g m (S * d) - binomialPrice u d r g m (S * d))) := by
          apply mul_le_mul_of_nonneg_left _ hExpPos.le
          linarith
      _ = binomialOptionPriceOnePeriod u d r
          (americanPrice u d r g m (S * u) - binomialPrice u d r g m (S * u))
          (americanPrice u d r g m (S * d) - binomialPrice u d r g m (S * d)) := rfl
      _ ≤ americanPrice u d r g (m + 1) S - binomialPrice u d r g (m + 1) S := hstep

/-- **A node where immediate exercise strictly beats continuation makes the premium at the root
strictly positive.** For the put payoff `max (K − S) 0` with `N` steps remaining, if some node
of the tree — `j` up-moves and `i` down-moves below the root, at least one step remaining — has
immediate exercise strictly above the one-period discounted continuation of the American price,
then the European put price at the root is strictly below the American one. Every node of the
tree is reached with positive probability under the risk-neutral law (`crrUpProb ∈ (0, 1)`),
so the hypothesis is exactly a strictly-optimal exercise node of positive probability. -/
theorem binomialPrice_lt_americanPrice_put_of_immediate_exercise_gt_continuation
    {u d r K S : ℝ} (h : BinomialNoArb u d r) (N : ℕ)
    (hw : ∃ j i : ℕ, j + i + 1 ≤ N ∧
      binomialOptionPriceOnePeriod u d r
        (americanPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i - 1) (S * u ^ j * d ^ i * u))
        (americanPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i - 1) (S * u ^ j * d ^ i * d))
      < max (K - S * u ^ j * d ^ i) 0) :
    binomialPrice u d r (fun S' ↦ max (K - S') 0) N S
      < americanPrice u d r (fun S' ↦ max (K - S') 0) N S := by
  obtain ⟨j, i, hN, hcont⟩ := hw
  have hq := crrUpProb_mem_Ioo h
  have hq0 : 0 < crrUpProb u d r := hq.1
  have hq1 : crrUpProb u d r < 1 := hq.2
  have hm : N - j - i = (N - j - i - 1) + 1 := by omega
  have hDnode : 0 < americanPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i)
        (S * u ^ j * d ^ i)
      - binomialPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i) (S * u ^ j * d ^ i) := by
    have hA : americanPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i)
        (S * u ^ j * d ^ i) = max (K - S * u ^ j * d ^ i) 0 := by
      rw [hm, americanPrice_succ, max_eq_left hcont.le]
    have hE : binomialPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i)
        (S * u ^ j * d ^ i)
        = binomialOptionPriceOnePeriod u d r
          (binomialPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i - 1)
            (S * u ^ j * d ^ i * u))
          (binomialPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i - 1)
            (S * u ^ j * d ^ i * d)) := by
      conv_lhs => rw [hm]
      exact binomialPrice_succ_eq_onePeriod u d r _ _ _
    have hmono : binomialOptionPriceOnePeriod u d r
        (binomialPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i - 1)
          (S * u ^ j * d ^ i * u))
        (binomialPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i - 1)
          (S * u ^ j * d ^ i * d))
      ≤ binomialOptionPriceOnePeriod u d r
          (americanPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i - 1)
            (S * u ^ j * d ^ i * u))
          (americanPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i - 1)
            (S * u ^ j * d ^ i * d)) :=
      binomialOptionPriceOnePeriod_mono h
        (bermudanPrice_mono h _ (Set.empty_subset Set.univ) _ _)
        (bermudanPrice_mono h _ (Set.empty_subset Set.univ) _ _)
    rw [hA, hE]
    linarith
  have hW : 0 < Real.exp (-(r * (j + i : ℕ))) * crrUpProb u d r ^ j
      * (1 - crrUpProb u d r) ^ i :=
    mul_pos (mul_pos (Real.exp_pos _) (pow_pos hq0 j)) (pow_pos (by linarith) i)
  have hle := americanPrice_premium_mul_weight_le h
    (fun S' ↦ max (K - S') 0) j i N (by omega) S
  have hpos : 0 < Real.exp (-(r * (j + i : ℕ))) * crrUpProb u d r ^ j
      * (1 - crrUpProb u d r) ^ i
      * (americanPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i) (S * u ^ j * d ^ i)
        - binomialPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i) (S * u ^ j * d ^ i)) :=
    mul_pos hW hDnode
  linarith

/-! ### The strict early-exercise premium -/

/-- **Deep in the money, immediate exercise strictly beats continuation.** For `r > 0` and at
least one step remaining, a spot so low that the whole remaining subtree ends in the money
(`0 < S`, `S * u ^ N ≤ K`) satisfies the witnessing condition of
`binomialPrice_lt_americanPrice_put_of_immediate_exercise_gt_continuation` with the witness at
the root (`j = i = 0`): the American one-period continuation is worth `K * e^{-r} − S`,
strictly below the intrinsic `K − S`. -/
theorem immediate_exercise_gt_continuation_of_deep_in_the_money
    {u d r K S : ℝ} (h : BinomialNoArb u d r) (hr : 0 < r) {N : ℕ} (hN : 1 ≤ N)
    (hS : 0 < S) (hSK : S * u ^ N ≤ K) :
    ∃ j i : ℕ, j + i + 1 ≤ N ∧
      binomialOptionPriceOnePeriod u d r
        (americanPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i - 1) (S * u ^ j * d ^ i * u))
        (americanPrice u d r (fun S' ↦ max (K - S') 0) (N - j - i - 1) (S * u ^ j * d ^ i * d))
      < max (K - S * u ^ j * d ^ i) 0 := by
  refine ⟨0, 0, by omega, ?_⟩
  simp only [pow_zero, mul_one]
  have hKpos : 0 < K := lt_of_lt_of_le (mul_pos hS (pow_pos h.u_pos N)) hSK
  have hexp : Real.exp (-r) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  have huN : S * u ^ ((N - 1) + 1) ≤ K := by
    rw [show (N - 1) + 1 = N from by omega]; exact hSK
  have hup : (S * u) * u ^ (N - 1) ≤ K := by
    rw [mul_assoc, mul_comm u (u ^ (N - 1)), ← pow_succ]; exact huN
  have hdp : (S * d) * u ^ (N - 1) ≤ K := by
    have h1 : (S * d) * u ^ (N - 1) = d * (S * u ^ (N - 1)) := by ring
    have h2 : u * (S * u ^ (N - 1)) = S * u ^ ((N - 1) + 1) := by
      rw [show u * (S * u ^ (N - 1)) = S * (u ^ (N - 1) * u) from by ring, ← pow_succ]
    have h3 : d * (S * u ^ (N - 1)) ≤ u * (S * u ^ (N - 1)) :=
      mul_le_mul_of_nonneg_right h.d_lt_u.le
        (mul_nonneg hS.le (pow_nonneg h.u_pos.le (N - 1)))
    calc (S * d) * u ^ (N - 1) = d * (S * u ^ (N - 1)) := h1
      _ ≤ u * (S * u ^ (N - 1)) := h3
      _ = S * u ^ ((N - 1) + 1) := h2
      _ ≤ K := huN
  rw [show N - 0 - 0 - 1 = N - 1 from by omega,
    americanPutPrice_eq_intrinsic_of_deep_in_the_money h (le_of_lt hr) (N - 1) (S * u)
      (mul_pos hS h.u_pos) hup,
    americanPutPrice_eq_intrinsic_of_deep_in_the_money h (le_of_lt hr) (N - 1) (S * d)
      (mul_pos hS h.d_pos) hdp]
  have hcont : binomialOptionPriceOnePeriod u d r (K - S * u) (K - S * d)
      = K * Real.exp (-r) - S := by
    unfold binomialOptionPriceOnePeriod
    rw [show crrUpProb u d r * (K - S * u) + (1 - crrUpProb u d r) * (K - S * d)
        = K - S * (crrUpProb u d r * u + (1 - crrUpProb u d r) * d) from by ring,
      crrUpProb_mul_up_add u d r h]
    rw [show Real.exp (-r) * (K - S * Real.exp r)
        = K * Real.exp (-r) - S * (Real.exp (-r) * Real.exp r) from by ring,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hu1 : (1 : ℝ) ≤ u := by
    have h1 : (1 : ℝ) ≤ Real.exp r := by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.mpr (by linarith)
    exact le_trans h1 h.lt_u.le
  have hSle : S ≤ K :=
    le_trans (le_mul_of_one_le_right hS.le (one_le_pow₀ hu1)) hSK
  rw [hcont, max_eq_left (by linarith)]
  nlinarith

/-- **Deep in the money the American put is strictly worth more than the European put.** With
`r > 0` and at least one step remaining, a spot so low that the whole remaining subtree ends in
the money (`0 < S`, `S * u ^ n ≤ K`) makes the European price `K * e^{-r*n} − S` strictly
smaller than the American price `K − S`: the early-exercise premium `K * (1 - e^{-r*n})` is
strictly positive. Derived from the frontier statement
`binomialPrice_lt_americanPrice_put_of_immediate_exercise_gt_continuation` with the witnessing
node at the root (`immediate_exercise_gt_continuation_of_deep_in_the_money`): deep in the
money the node is the root itself, reached with probability one. -/
theorem binomialPrice_lt_americanPrice_put_of_deep_in_the_money
    {u d r K : ℝ} (h : BinomialNoArb u d r) (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n)
    (S : ℝ) (hS : 0 < S) (hSK : S * u ^ n ≤ K) :
    binomialPrice u d r (fun S' ↦ max (K - S') 0) n S
      < americanPrice u d r (fun S' ↦ max (K - S') 0) n S :=
  binomialPrice_lt_americanPrice_put_of_immediate_exercise_gt_continuation h n
    (immediate_exercise_gt_continuation_of_deep_in_the_money h hr hn hS hSK)

end MathFin

/-! ### The premium read in the binomial market -/

namespace MathFin.Contracts.Binomial

open MeasureTheory
open scoped NNReal

/-- **In the binomial market, the European put is strictly worth less than the American put
whenever some node makes immediate exercise strictly optimal.** Under the risk-neutral coin
flips — a pricing measure of the binomial market (`isPricingMeasure_coinFlipMeasure`) — the
price of the European put `europeanPut K` is its tree price
(`price_pay_eq_binomialPrice_of_isPricingMeasure`), the American price of the exercise right
`europeanPutPayoff K` is the tree's `americanPrice`
(`americanPrice_market_europeanPutPayoff`), and the tree-level gap at a strictly-optimal
exercise node (`binomialPrice_lt_americanPrice_put_of_immediate_exercise_gt_continuation`)
makes the market prices differ strictly. The market is taken at unit step with horizon `N`. -/
theorem price_europeanPut_lt_americanPrice_of_immediate_exercise_gt_continuation
    {S₀ u d ρ K : ℝ} {q p : ℝ≥0} (hq : q ≤ 1) (hp0 : 0 < p) (hp : p < 1) (hS₀ : 0 < S₀)
    (hna : MathFin.BinomialNoArb u d ρ) (hqcrr : MathFin.crrUpProb u d ρ = q) (N : ℕ)
    (hw : ∃ j i : ℕ, j + i + 1 ≤ N ∧
      MathFin.binomialOptionPriceOnePeriod u d ρ
        (MathFin.americanPrice u d ρ (fun S' ↦ max (K - S') 0) (N - j - i - 1)
          (S₀ * u ^ j * d ^ i * u))
        (MathFin.americanPrice u d ρ (fun S' ↦ max (K - S') 0) (N - j - i - 1)
          (S₀ * u ^ j * d ^ i * d))
      < max (K - S₀ * u ^ j * d ^ i) 0) :
    (market (coinFlipMeasure p hp.le) S₀ u d ρ zero_le_one).price (coinFlipMeasure q hq)
        (europeanPut K (N : ℝ≥0))
    < (market (coinFlipMeasure p hp.le) S₀ u d ρ zero_le_one).americanPrice
        (coinFlipMeasure q hq) (europeanPutPayoff K) (N : ℝ≥0) := by
  have hQ : (market (coinFlipMeasure p hp.le) S₀ u d ρ zero_le_one).IsPricingMeasure (N : ℝ≥0)
      (coinFlipMeasure q hq) :=
    isPricingMeasure_coinFlipMeasure hq hna hqcrr S₀ zero_le_one hp0 hp N
  have hE := price_pay_eq_binomialPrice_of_isPricingMeasure (h := 1) hS₀ hna hqcrr one_pos
    (T := (N : ℝ≥0)) (N := N) (hTN := by push_cast; simp)
    (a := europeanPutPayoff K (N : ℝ≥0)) (g := fun S' ↦ max (K - S') 0) (hg := fun _ ↦ rfl) hQ
  have hA := americanPrice_market_europeanPutPayoff (h := 1) one_pos hq hqcrr
    (coinFlipMeasure p hp.le) S₀ K (N : ℝ≥0)
  conv at hA => rw [show ⌊((N : ℝ≥0) : ℝ) / 1⌋₊ = N from by push_cast; simp]
  unfold europeanPut
  rw [hE, hA]
  exact MathFin.binomialPrice_lt_americanPrice_put_of_immediate_exercise_gt_continuation
    hna N hw

end MathFin.Contracts.Binomial

