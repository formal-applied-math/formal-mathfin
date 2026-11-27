/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import MathFin.Contracts.Instruments.Options

/-!
# A static-hedge compiler for piecewise-linear payoffs

A European payoff that is a continuous piecewise-linear function of the terminal price is a
*static portfolio*: an amount of zero-coupon bond, an amount of the underlying, and finitely many
calls, one at each kink of the payoff, weighted by the change of slope there. This file compiles the
payoffs of the language of `Contracts/Core.lean` that are such functions, by structural recursion on
the payoff, and proves the compiler correct.

The fragment `Payoff.IsPiecewiseLinear T` is what the language builds from constants, the
observation `obs () T`, `add`, `sub`, `max`, `min` and the product with a constant. The portfolio
`StaticHedge` is data: a bond amount `a`, a forward amount `b` and a list of `(strike, weight)`
pairs, standing for the function `S ↦ a + b S + ∑ⱼ wⱼ (S − Kⱼ)⁺`. `Payoff.staticHedge` sends a
payoff to its portfolio, and `StaticHedge.contract` reads the portfolio back as a `Contract Unit`
built from `pay T (const 1)`, `pay T (obs () T)` and `europeanCall K T`.

The correctness theorem is pathwise and holds for every discount function: along any scenario
with a nonnegative observation at `T`, the compiled contract has the same present value as
`pay T e` (`Payoff.IsPiecewiseLinear.pathPV_staticHedge`). The restriction to nonnegative
observations is the true condition: the identity is one of functions on `S ≥ 0`, and a strike below
zero is folded into the affine part there. The values of the two contracts in every model, and the
prices of the pieces by the call price function of a market, are in `Pricing/StaticHedge.lean` and
`Models/ModelFree/StaticHedgeMarket.lean`.

## Implementation notes

The compiler is explicit. Each connective of the payoff language has an operation on portfolios
that is correct for the function the portfolio stands for:
* `add`, `sub` and `smul` concatenate the call lists and combine the amounts;
* `posPart` computes the positive part `h⁺` of `h = a + b S + ∑ⱼ wⱼ (S − Kⱼ)⁺`. It sorts the kinks
  (`sortKinks`) and scans them from the left, keeping the first kink `K` and the rest `R`. A kink
  below zero is affine on `S ≥ 0` and is folded into `a` and `b`. Otherwise `h⁺` is the positive
  part of the affine function `a + b S` left of `K`, and right of `K` the positive part of the
  portfolio of `R` with `a − w K` and `b + w`, computed recursively. The two are joined at `K`:
  their difference, which vanishes at `K`, is cut off below `K` by `tail`, whose single new call at
  `K` carries the slope the difference has there. The zero crossings of the pieces enter through
  `affinePos`, the positive part of an affine function, which is `b (S − r)⁺` for `b > 0` and
  `(a + b S) + (−b)(S − r)⁺` for `b < 0`, with `r = −a / b`;
* `sup` is `f + (g − f)⁺` and `inf` is `f + g − max f g`.

`Payoff.staticHedge` is the recursion on the syntax: constants and `obs () T` to the affine
portfolios, `add`, `sub`, `max`, `min` to the operations, a product with a constant to `smul`, and
anything else (and `obs` at another date) to the empty portfolio. The list `calls` is not reduced:
it may hold calls of weight zero and calls at one strike twice, which is the same function.
`StaticHedge.normalize` reduces it to the normal form, merged, sorted and without zero weights, with
the same value (`StaticHedge.eval_normalize`); the normal form is what the slope bridge to the
Carr–Madan formula reads (`Models/ModelFree/CarrMadan.lean`, `StaticHedge.jump_eval_of_mem_normalize`),
the finite exact case of `carrMadan_spanning`, which spans a smooth payoff by a continuum of calls.
Outside the fragment the compiler returns a portfolio that no theorem relates to the payoff.

## Main definitions

* `callSum`: the sum `∑ⱼ wⱼ (S − Kⱼ)⁺` of a list of `(Kⱼ, wⱼ)`.
* `StaticHedge`: a bond amount, a forward amount and a list of `(strike, weight)` calls, with its
  `eval` as a function of the terminal price and its `contract` at a date `T`.
* `StaticHedge.add`, `StaticHedge.sub`, `StaticHedge.smul`, `StaticHedge.posPart`,
  `StaticHedge.sup`, `StaticHedge.inf`: the operations the compiler is built from.
* `insertCall`, `StaticHedge.normalize`: the normal form of a portfolio, its calls merged by strike,
  sorted, and without zero weights.
* `Payoff.IsPiecewiseLinear`: the payoffs of one terminal observation built from constants,
  `obs () T`, `add`, `sub`, `max`, `min` and the product with a constant.
* `Payoff.staticHedge`: the compiler.

## Main results

* `StaticHedge.eval_posPart`: on `S ≥ 0`, the portfolio `H.posPart` is worth `max (H.eval S) 0`.
* `Payoff.IsPiecewiseLinear.eval_staticHedge`: on a scenario with nonnegative terminal observation,
  a payoff of the fragment is worth its compiled portfolio at the terminal price.
* `Payoff.IsPiecewiseLinear.exists_hedge`: every payoff of the fragment is a static portfolio.
* `StaticHedge.pathPV_contract`: the present value of the compiled contract along a scenario is
  the discount factor times the portfolio's value at the terminal price.
* `Payoff.IsPiecewiseLinear.pathPV_staticHedge`: the compiled contract and `pay T e` have the same
  present value along every scenario with nonnegative terminal observation, for every discount
  function.
* `staticHedge_europeanCallPayoff`: the compiler maps the call payoff to the one call at its strike.
* `StaticHedge.eval_normalize`: the normal form is worth what the portfolio is worth, at every price.
* `staticHedge_cappedCall_normalize`: the capped call's two calls, compiled and normalised, are the
  portfolio `⟨0, 0, [(K₁, 1), (K₂, -1)]⟩` for `K₁ < K₂`.

## References

* [P. Carr and D. Madan, *Towards a theory of volatility trading*][CarrMadan1998]
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [S. Peyton Jones, J. M. Eber and J. Seward, *Composing contracts*][PeytonJonesEberSeward2000]

## Tags

static hedge, static replication, piecewise linear payoff, spanning by calls, contract compiler,
payoff language, MSC 91G20, JEL G13
-/

@[expose] public section

open scoped NNReal

namespace MathFin.Contracts

/-! ### Call sums -/

/-- The sum `∑ⱼ wⱼ (S − Kⱼ)⁺` over a list of `(Kⱼ, wⱼ)`: the payoff, at the price `S`, of calls
at the strikes `Kⱼ` held in the amounts `wⱼ`. -/
noncomputable def callSum (L : List (ℝ × ℝ)) (S : ℝ) : ℝ :=
  (L.map fun p ↦ p.2 * max (S - p.1) 0).sum

/-- An empty call sum is zero. -/
@[simp] theorem callSum_nil (S : ℝ) : callSum [] S = 0 := by simp [callSum]

/-- A call sum splits off its first call. -/
@[simp] theorem callSum_cons (p : ℝ × ℝ) (L : List (ℝ × ℝ)) (S : ℝ) :
    callSum (p :: L) S = p.2 * max (S - p.1) 0 + callSum L S := by simp [callSum]

/-- A call sum over two lists is the sum of the two call sums. -/
theorem callSum_append (L L' : List (ℝ × ℝ)) (S : ℝ) :
    callSum (L ++ L') S = callSum L S + callSum L' S := by simp [callSum]

/-- Scaling every weight of a call sum scales the sum. -/
theorem callSum_smul (c : ℝ) (L : List (ℝ × ℝ)) (S : ℝ) :
    callSum (L.map fun p ↦ (p.1, c * p.2)) S = c * callSum L S := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, callSum_cons, ih]
    ring

/-- A call sum does not depend on the order of its calls. -/
theorem callSum_perm {L L' : List (ℝ × ℝ)} (h : L.Perm L') (S : ℝ) :
    callSum L S = callSum L' S := by
  unfold callSum
  exact (h.map _).sum_eq

/-- Calls struck at or above `K` pay nothing at any price `S ≤ K`. -/
theorem callSum_eq_zero_of_le {K S : ℝ} (hS : S ≤ K) {R : List (ℝ × ℝ)}
    (h : ∀ q ∈ R, K ≤ q.1) : callSum R S = 0 := by
  induction R with
  | nil => simp
  | cons q R ih =>
    have h1 : max (S - q.1) 0 = 0 := max_eq_right (by linarith [h q List.mem_cons_self])
    rw [callSum_cons, h1, ih fun r hr ↦ h r (List.mem_cons_of_mem _ hr)]
    ring

/-- Splitting a call sum at a level `K`, on `S ≥ K`: the calls struck below `K` are affine in `S`
there, and the calls struck at or above `K` are kept, the others carrying weight zero. -/
theorem callSum_split (K : ℝ) (L : List (ℝ × ℝ)) (S : ℝ) (hS : K ≤ S) :
    callSum L S = (L.map fun p ↦ if p.1 < K then p.2 else 0).sum * S
      - (L.map fun p ↦ if p.1 < K then p.2 * p.1 else 0).sum
      + callSum (L.map fun p ↦ (p.1, if p.1 < K then 0 else p.2)) S := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, callSum_cons, ih]
    by_cases hp : p.1 < K
    · have h1 : max (S - p.1) 0 = S - p.1 := max_eq_left (by linarith)
      simp only [if_pos hp, h1]
      ring
    · simp only [if_neg hp]
      ring

/-- The calls kept by `callSum_split` pay nothing at any price `S ≤ K`. -/
theorem callSum_split_eq_zero (K : ℝ) (L : List (ℝ × ℝ)) (S : ℝ) (hS : S ≤ K) :
    callSum (L.map fun p ↦ (p.1, if p.1 < K then 0 else p.2)) S = 0 := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, callSum_cons, ih]
    by_cases hp : p.1 < K
    · simp [if_pos hp]
    · have h1 : max (S - p.1) 0 = 0 := max_eq_right (by linarith [not_lt.1 hp])
      simp [if_neg hp, h1]

/-- Inserting a call into a list of calls, kept sorted by strictly increasing strike: a call at a
strike already present is merged into it, the weights adding. -/
def insertCall (p : ℝ × ℝ) : List (ℝ × ℝ) → List (ℝ × ℝ)
  | [] => [p]
  | q :: L =>
    if p.1 < q.1 then p :: q :: L
    else if p.1 = q.1 then (q.1, q.2 + p.2) :: L
    else q :: insertCall p L

/-- **Inserting a call adds it to the call sum.** -/
theorem callSum_insertCall (p : ℝ × ℝ) (L : List (ℝ × ℝ)) (S : ℝ) :
    callSum (insertCall p L) S = p.2 * max (S - p.1) 0 + callSum L S := by
  induction L with
  | nil => simp [insertCall]
  | cons q L ih =>
    unfold insertCall
    split_ifs with h1 h2
    · simp only [callSum_cons]
    · simp only [callSum_cons, ← h2]
      ring
    · simp only [callSum_cons, ih]
      ring

/-- The strikes of the list after an insertion are the strikes before, or the inserted one. -/
theorem mem_insertCall {p q : ℝ × ℝ} {L : List (ℝ × ℝ)} (h : q ∈ insertCall p L) :
    q.1 = p.1 ∨ q ∈ L := by
  induction L with
  | nil => simp only [insertCall, List.mem_singleton] at h; exact Or.inl (by rw [h])
  | cons r L ih =>
    unfold insertCall at h
    split_ifs at h with h1 h2
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl h2.symm
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr List.mem_cons_self
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **Inserting a call keeps the strikes strictly increasing.** -/
theorem pairwise_insertCall (p : ℝ × ℝ) :
    ∀ L : List (ℝ × ℝ), L.Pairwise (fun a b ↦ a.1 < b.1) →
      (insertCall p L).Pairwise (fun a b ↦ a.1 < b.1)
  | [], _ => by simp [insertCall]
  | r :: L, hL => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hL
    unfold insertCall
    split_ifs with hlt heq
    · refine List.pairwise_cons.2 ⟨fun q hq ↦ ?_, hL⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hlt
      · exact hlt.trans (h1 q hq)
    · exact List.pairwise_cons.2 ⟨h1, h2⟩
    · refine List.pairwise_cons.2 ⟨fun q hq ↦ ?_, pairwise_insertCall p L h2⟩
      rcases mem_insertCall hq with h | h
      · exact h ▸ lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm heq)
      · exact h1 q h

/-- Dropping the calls of weight zero does not change the call sum. -/
theorem callSum_filter_ne_zero (L : List (ℝ × ℝ)) (S : ℝ) :
    callSum (L.filter fun p ↦ decide (p.2 ≠ 0)) S = callSum L S := by
  induction L with
  | nil => simp
  | cons p L ih =>
    by_cases h : p.2 = 0
    · simp [List.filter_cons, h, ih, callSum_cons]
    · simp [List.filter_cons, h, ih, callSum_cons]

/-! ### Portfolios and their operations -/

/-- **A static hedge**: an amount of the zero-coupon bond paying `1` at the date, an amount of the
underlying delivered at the date, and calls at the date, each a pair `(strike, weight)`. -/
structure StaticHedge where
  /-- The amount of the bond paying `1`. -/
  bondAmount : ℝ
  /-- The amount of the underlying delivered. -/
  forwardAmount : ℝ
  /-- The calls, as `(strike, weight)` pairs. -/
  calls : List (ℝ × ℝ)

namespace StaticHedge

/-- The value of the portfolio at the terminal price `S`: `a + b S + ∑ⱼ wⱼ (S − Kⱼ)⁺`. -/
noncomputable def eval (H : StaticHedge) (S : ℝ) : ℝ :=
  H.bondAmount + H.forwardAmount * S + callSum H.calls S

/-- The sum of two portfolios: the amounts add and the call lists concatenate. -/
noncomputable def add (H H' : StaticHedge) : StaticHedge :=
  ⟨H.bondAmount + H'.bondAmount, H.forwardAmount + H'.forwardAmount, H.calls ++ H'.calls⟩

/-- A portfolio scaled by `c`: the amounts and the weights are multiplied by `c`. -/
noncomputable def smul (c : ℝ) (H : StaticHedge) : StaticHedge :=
  ⟨c * H.bondAmount, c * H.forwardAmount, H.calls.map fun p ↦ (p.1, c * p.2)⟩

/-- The difference of two portfolios. -/
noncomputable def sub (H H' : StaticHedge) : StaticHedge :=
  H.add (H'.smul (-1))

/-- The value of a sum is the sum of the values. -/
theorem eval_add (H H' : StaticHedge) (S : ℝ) : (H.add H').eval S = H.eval S + H'.eval S := by
  simp only [eval, StaticHedge.add, callSum_append]
  ring

/-- The value of a scaled portfolio is the scaled value. -/
theorem eval_smul (c : ℝ) (H : StaticHedge) (S : ℝ) : (H.smul c).eval S = c * H.eval S := by
  simp only [eval, StaticHedge.smul, callSum_smul]
  ring

/-- The value of a difference is the difference of the values. -/
theorem eval_sub (H H' : StaticHedge) (S : ℝ) : (H.sub H').eval S = H.eval S - H'.eval S := by
  simp only [StaticHedge.sub, eval_add, eval_smul]
  ring

/-- **The normal form of a portfolio**: the calls at one strike merged into one (the weights
adding), sorted by strictly increasing strike, and the calls of weight zero dropped. -/
noncomputable def normalize (H : StaticHedge) : StaticHedge :=
  ⟨H.bondAmount, H.forwardAmount,
    (H.calls.foldr insertCall []).filter fun p ↦ decide (p.2 ≠ 0)⟩

/-- Merging the calls of a list into a sorted list adds their call sums. -/
theorem callSum_foldr_insertCall (L : List (ℝ × ℝ)) (S : ℝ) :
    callSum (L.foldr insertCall []) S = callSum L S := by
  induction L with
  | nil => simp
  | cons p L ih => rw [List.foldr_cons, callSum_insertCall, ih, callSum_cons]

/-- **Normalising does not change the value.** -/
theorem eval_normalize (H : StaticHedge) (S : ℝ) : H.normalize.eval S = H.eval S := by
  simp only [eval, normalize, callSum_filter_ne_zero, callSum_foldr_insertCall]

/-- The strikes of a normalised portfolio are strictly increasing, so each appears once. -/
theorem pairwise_normalize_calls (H : StaticHedge) :
    H.normalize.calls.Pairwise (fun a b ↦ a.1 < b.1) := by
  have h : ∀ L : List (ℝ × ℝ), (L.foldr insertCall []).Pairwise (fun a b ↦ a.1 < b.1) := by
    intro L
    induction L with
    | nil => simp
    | cons p L ih => exact pairwise_insertCall p _ ih
  exact (h H.calls).filter _

/-- No call of a normalised portfolio has weight zero. -/
theorem weight_ne_zero_of_mem_normalize {H : StaticHedge} {q : ℝ × ℝ}
    (hq : q ∈ H.normalize.calls) : q.2 ≠ 0 := by
  simpa [normalize] using (List.mem_filter.1 hq).2

/-- The portfolio of the positive part of the affine function `a + b S`. For `b < 0` it is
`(a + b S) + (−b)(S − r)⁺` and for `b > 0` it is `b (S − r)⁺`, where `r = −a / b` is the root; for
`b = 0` it is the constant `max a 0`. -/
noncomputable def affinePos (a b : ℝ) : StaticHedge :=
  if b < 0 then ⟨a, b, [(-a / b, -b)]⟩
  else if 0 < b then ⟨0, 0, [(-a / b, b)]⟩
  else ⟨max a 0, 0, []⟩

/-- **The positive part of an affine function**, for every price. -/
theorem eval_affinePos (a b S : ℝ) : (affinePos a b).eval S = max (a + b * S) 0 := by
  by_cases hb : b < 0
  · have hr : b * (-a / b) = -a := mul_div_cancel₀ _ hb.ne
    rw [affinePos, if_pos hb]
    simp only [eval, callSum_cons, callSum_nil, add_zero]
    generalize -a / b = r at hr ⊢
    have e : a + b * S = b * (S - r) := by linear_combination hr
    rw [e]
    rcases le_total (S - r) 0 with h | h
    · rw [max_eq_right h, max_eq_left (show 0 ≤ b * (S - r) by nlinarith)]
      ring
    · rw [max_eq_left h, max_eq_right (show b * (S - r) ≤ 0 by nlinarith)]
      ring
  · by_cases hb' : 0 < b
    · have hr : b * (-a / b) = -a := mul_div_cancel₀ _ hb'.ne'
      rw [affinePos, if_neg hb, if_pos hb']
      simp only [eval, callSum_cons, callSum_nil, add_zero, zero_add, zero_mul]
      generalize -a / b = r at hr ⊢
      have e : a + b * S = b * (S - r) := by linear_combination hr
      rw [e]
      rcases le_total (S - r) 0 with h | h
      · rw [max_eq_right h, max_eq_right (show b * (S - r) ≤ 0 by nlinarith)]
        ring
      · rw [max_eq_left h, max_eq_left (show 0 ≤ b * (S - r) by nlinarith)]
    · have hb0 : b = 0 := le_antisymm (not_lt.1 hb') (not_lt.1 hb)
      rw [affinePos, if_neg hb, if_neg hb']
      simp [eval, hb0]

/-- **A portfolio cut off below `K`**: the portfolio that is worth `0` below `K` and, from `K` on,
what `H` is worth, provided `H` is worth `0` at `K`. Its calls are those of `H` struck at or above
`K`, the others carrying weight zero, and one more call at `K` whose weight is the slope of `H`
right of `K` (the forward amount of `H` plus the weights of its calls struck below `K`). -/
noncomputable def tail (K : ℝ) (H : StaticHedge) : StaticHedge :=
  ⟨0, 0, (K, H.forwardAmount + (H.calls.map fun p ↦ if p.1 < K then p.2 else 0).sum) ::
    H.calls.map fun p ↦ (p.1, if p.1 < K then 0 else p.2)⟩

/-- **`tail` cuts a portfolio off below `K`.** If `H` is worth `0` at `K`, then `tail K H` is worth
`0` below `K` and what `H` is worth from `K` on. -/
theorem eval_tail (K : ℝ) (H : StaticHedge) (h0 : H.eval K = 0) (S : ℝ) :
    (tail K H).eval S = if S < K then 0 else H.eval S := by
  unfold eval at h0
  rw [callSum_split K H.calls K le_rfl, callSum_split_eq_zero K H.calls K le_rfl] at h0
  by_cases hlt : S < K
  · have h1 : max (S - K) 0 = 0 := max_eq_right (by linarith)
    simp only [eval, tail, if_pos hlt, callSum_cons, h1,
      callSum_split_eq_zero K H.calls S hlt.le]
    ring
  · have hKS : K ≤ S := not_lt.1 hlt
    have h1 : max (S - K) 0 = S - K := max_eq_left (by linarith)
    simp only [eval, tail, if_neg hlt, callSum_cons, h1]
    rw [callSum_split K H.calls S hKS]
    linear_combination (-1 : ℝ) * h0

/-- The order on `(strike, weight)` pairs by strike. -/
def kinkLE (p q : ℝ × ℝ) : Prop := p.1 ≤ q.1

noncomputable instance : DecidableRel kinkLE := fun p q ↦ inferInstanceAs (Decidable (p.1 ≤ q.1))

instance : Std.Total kinkLE := ⟨fun p q ↦ le_total p.1 q.1⟩

instance : IsTrans (ℝ × ℝ) kinkLE := ⟨fun _ _ _ h h' ↦ le_trans h h'⟩

/-- The calls sorted by increasing strike. -/
noncomputable def sortKinks (L : List (ℝ × ℝ)) : List (ℝ × ℝ) :=
  L.mergeSort (kinkLE · ·)

/-- The sorted calls are sorted. -/
theorem pairwise_sortKinks (L : List (ℝ × ℝ)) : (sortKinks L).Pairwise kinkLE :=
  List.pairwise_mergeSort' kinkLE L

/-- Sorting permutes the calls. -/
theorem sortKinks_perm (L : List (ℝ × ℝ)) : (sortKinks L).Perm L :=
  List.mergeSort_perm L _

/-- The positive part of `a + b S + ∑ⱼ wⱼ (S − Kⱼ)⁺` for kinks sorted by increasing strike, by
recursion on the kinks. With the smallest kink `K` of weight `w` and the rest `R`:
* if `K < 0`, the call is affine on `S ≥ 0` and is folded into `a − w K` and `b + w`;
* otherwise the function is `a + b S` left of `K` and the portfolio of `R` with `a − w K` and
  `b + w` right of it. The positive parts `u` and `v` of the two agree at `K`, and the result is
  `u + tail K (v − u)`. -/
noncomputable def posAux : ℝ → ℝ → List (ℝ × ℝ) → StaticHedge
  | a, b, [] => affinePos a b
  | a, b, (K, w) :: R =>
    if K < 0 then posAux (a - w * K) (b + w) R
    else (affinePos a b).add (tail K ((posAux (a - w * K) (b + w) R).sub (affinePos a b)))

/-- **The positive part of a portfolio**: the portfolio, with the kinks sorted, that is worth
`max (H.eval S) 0` at every price `S ≥ 0` (`eval_posPart`). -/
noncomputable def posPart (H : StaticHedge) : StaticHedge :=
  posAux H.bondAmount H.forwardAmount (sortKinks H.calls)

/-- The positive part of a portfolio with sorted kinks, on `S ≥ 0`. -/
theorem eval_posAux (R : List (ℝ × ℝ)) :
    ∀ (a b : ℝ), R.Pairwise kinkLE → ∀ S, 0 ≤ S →
      (posAux a b R).eval S = max (a + b * S + callSum R S) 0 := by
  induction R with
  | nil =>
    intro a b _ S _
    rw [posAux, eval_affinePos]
    simp
  | cons p R ih =>
    obtain ⟨K, w⟩ := p
    intro a b hs S hS
    have hK : ∀ q ∈ R, K ≤ q.1 := (List.pairwise_cons.1 hs).1
    have hR : R.Pairwise kinkLE := (List.pairwise_cons.1 hs).2
    by_cases hK0 : K < 0
    · have h1 : max (S - K) 0 = S - K := max_eq_left (by linarith)
      rw [posAux, if_pos hK0, ih (a - w * K) (b + w) hR S hS]
      simp only [callSum_cons, h1]
      congr 1
      ring
    · have hK0' : 0 ≤ K := not_lt.1 hK0
      have hv (S' : ℝ) (h : 0 ≤ S') : (posAux (a - w * K) (b + w) R).eval S'
          = max (a - w * K + (b + w) * S' + callSum R S') 0 := ih _ _ hR S' h
      have hvK : ((posAux (a - w * K) (b + w) R).sub (affinePos a b)).eval K = 0 := by
        rw [eval_sub, hv K hK0', eval_affinePos, callSum_eq_zero_of_le le_rfl hK,
          show a - w * K + (b + w) * K + 0 = a + b * K by ring, sub_self]
      rw [posAux, if_neg hK0, eval_add, eval_tail K _ hvK, eval_sub, eval_affinePos]
      by_cases hlt : S < K
      · have h1 : max (S - K) 0 = 0 := max_eq_right (by linarith)
        simp only [if_pos hlt, callSum_cons, h1, callSum_eq_zero_of_le hlt.le hK]
        simp
      · have h1 : max (S - K) 0 = S - K := max_eq_left (by linarith [not_lt.1 hlt])
        rw [if_neg hlt, hv S hS]
        simp only [callSum_cons, h1]
        rw [show a + b * S + (w * (S - K) + callSum R S)
          = a - w * K + (b + w) * S + callSum R S by ring]
        ring

/-- **The positive part of a portfolio is worth the positive part of its value**, on `S ≥ 0`. -/
theorem eval_posPart (H : StaticHedge) (S : ℝ) (hS : 0 ≤ S) :
    H.posPart.eval S = max (H.eval S) 0 := by
  have h := eval_posAux (sortKinks H.calls) H.bondAmount H.forwardAmount
    (pairwise_sortKinks _) S hS
  rw [callSum_perm (sortKinks_perm H.calls) S] at h
  exact h

/-- The larger of two portfolios, as `f + (g − f)⁺`. -/
noncomputable def sup (H H' : StaticHedge) : StaticHedge :=
  H.add ((H'.sub H).posPart)

/-- The smaller of two portfolios, as `f + g − max f g`. -/
noncomputable def inf (H H' : StaticHedge) : StaticHedge :=
  (H.add H').sub (H.sup H')

/-- **The larger of two portfolios is worth the larger of the values**, on `S ≥ 0`. -/
theorem eval_sup (H H' : StaticHedge) (S : ℝ) (hS : 0 ≤ S) :
    (H.sup H').eval S = max (H.eval S) (H'.eval S) := by
  rw [sup, eval_add, eval_posPart _ _ hS, eval_sub]
  rcases le_total (H.eval S) (H'.eval S) with h | h
  · rw [max_eq_right h, max_eq_left (sub_nonneg.2 h)]
    ring
  · rw [max_eq_left h, max_eq_right (sub_nonpos.2 h)]
    ring

/-- **The smaller of two portfolios is worth the smaller of the values**, on `S ≥ 0`. -/
theorem eval_inf (H H' : StaticHedge) (S : ℝ) (hS : 0 ≤ S) :
    (H.inf H').eval S = min (H.eval S) (H'.eval S) := by
  rw [inf, eval_sub, eval_add, eval_sup _ _ _ hS]
  rcases le_total (H.eval S) (H'.eval S) with h | h
  · rw [min_eq_left h, max_eq_right h]
    ring
  · rw [min_eq_right h, max_eq_left h]
    ring

end StaticHedge

/-! ### The fragment and its compiler -/

/-- The constant a payoff is, if it is one. -/
def Payoff.constOf {ι : Type*} : Payoff ι → Option ℝ
  | .const c => some c
  | _ => none

/-- A payoff with a constant value is that constant. -/
theorem Payoff.eq_const_of_constOf {ι : Type*} {a : Payoff ι} {d : ℝ} (h : a.constOf = some d) :
    a = .const d := by
  cases a <;> simp [Payoff.constOf] at h <;> simp [h]

/-- **The static-hedge compiler**, by recursion on the payoff: the portfolio of a constant, of
`obs () T`, and of a sum, difference, `max`, `min` or product with a constant, from the portfolios
of the parts. Any other payoff, and `obs` at another date, compiles to the empty portfolio. On the
fragment `Payoff.IsPiecewiseLinear` the portfolio reproduces the payoff on the nonnegative reals
(`Payoff.IsPiecewiseLinear.eval_staticHedge`). -/
noncomputable def Payoff.staticHedge (T : ℝ≥0) : Payoff Unit → StaticHedge
  | .const c => ⟨c, 0, []⟩
  | .obs _ t => if t = T then ⟨0, 1, []⟩ else ⟨0, 0, []⟩
  | .add a b => (Payoff.staticHedge T a).add (Payoff.staticHedge T b)
  | .sub a b => (Payoff.staticHedge T a).sub (Payoff.staticHedge T b)
  | .max a b => (Payoff.staticHedge T a).sup (Payoff.staticHedge T b)
  | .min a b => (Payoff.staticHedge T a).inf (Payoff.staticHedge T b)
  | .mul a b =>
    match a.constOf with
    | some c => (Payoff.staticHedge T b).smul c
    | none =>
      match b.constOf with
      | some c => (Payoff.staticHedge T a).smul c
      | none => ⟨0, 0, []⟩
  | .indicatorLt _ _ => ⟨0, 0, []⟩
  | .rpow _ _ => ⟨0, 0, []⟩

/-- **The piecewise-linear fragment** of the payoff language, at the observation `obs () T`: the
payoffs built from constants, the observation at `T` alone, sums, differences, `max`, `min` and
the product with a constant, on either side. Every one of them is a continuous piecewise-linear
function of `S_T` with finitely many kinks; `mul` of two non-constant payoffs, `indicatorLt` and
`rpow` are not in the fragment. -/
inductive Payoff.IsPiecewiseLinear (T : ℝ≥0) : Payoff Unit → Prop
  | const (c : ℝ) : IsPiecewiseLinear T (.const c)
  | obs : IsPiecewiseLinear T (.obs () T)
  | add {a b : Payoff Unit} :
      IsPiecewiseLinear T a → IsPiecewiseLinear T b → IsPiecewiseLinear T (.add a b)
  | sub {a b : Payoff Unit} :
      IsPiecewiseLinear T a → IsPiecewiseLinear T b → IsPiecewiseLinear T (.sub a b)
  | max {a b : Payoff Unit} :
      IsPiecewiseLinear T a → IsPiecewiseLinear T b → IsPiecewiseLinear T (.max a b)
  | min {a b : Payoff Unit} :
      IsPiecewiseLinear T a → IsPiecewiseLinear T b → IsPiecewiseLinear T (.min a b)
  | constMul (c : ℝ) {a : Payoff Unit} :
      IsPiecewiseLinear T a → IsPiecewiseLinear T (.mul (.const c) a)
  | mulConst {a : Payoff Unit} (c : ℝ) :
      IsPiecewiseLinear T a → IsPiecewiseLinear T (.mul a (.const c))

/-- The contract holding the calls `(Kⱼ, wⱼ)` at the date `T`: the weighted `europeanCall Kⱼ T`
combined with `both`. -/
noncomputable def callPortfolio (T : ℝ≥0) : List (ℝ × ℝ) → Contract Unit
  | [] => .zero
  | p :: L => .both (.scale p.2 (europeanCall p.1 T)) (callPortfolio T L)

/-- **The compiled contract** of a static hedge at the date `T`: the bond amount of
`pay T (const 1)`, the forward amount of `pay T (obs () T)`, and the calls. -/
noncomputable def StaticHedge.contract (H : StaticHedge) (T : ℝ≥0) : Contract Unit :=
  .both (.scale H.bondAmount (.pay T (.const 1)))
    (.both (.scale H.forwardAmount (.pay T (.obs () T))) (callPortfolio T H.calls))

/-- **The compiler is correct on the fragment**: the payoff is the value of its portfolio at the
terminal price, on every scenario with nonnegative terminal observation. -/
theorem Payoff.IsPiecewiseLinear.eval_staticHedge {T : ℝ≥0} {e : Payoff Unit}
    (h : e.IsPiecewiseLinear T) (s : Scenario Unit) (hs : 0 ≤ s () T) :
    e.eval s = (e.staticHedge T).eval (s () T) := by
  induction h with
  | const c => simp [Payoff.staticHedge, Payoff.eval, StaticHedge.eval]
  | obs => simp [Payoff.staticHedge, Payoff.eval, StaticHedge.eval]
  | add _ _ iha ihb =>
    simp only [Payoff.eval, Payoff.staticHedge, StaticHedge.eval_add, ← iha, ← ihb]
  | sub _ _ iha ihb =>
    simp only [Payoff.eval, Payoff.staticHedge, StaticHedge.eval_sub, ← iha, ← ihb]
  | max _ _ iha ihb =>
    simp only [Payoff.eval, Payoff.staticHedge, StaticHedge.eval_sup _ _ _ hs, ← iha, ← ihb]
  | min _ _ iha ihb =>
    simp only [Payoff.eval, Payoff.staticHedge, StaticHedge.eval_inf _ _ _ hs, ← iha, ← ihb]
  | constMul c _ iha =>
    simp only [Payoff.eval, Payoff.staticHedge, Payoff.constOf, StaticHedge.eval_smul, ← iha]
  | @mulConst a c _ iha =>
    rcases hc : a.constOf with _ | d
    · simp only [Payoff.eval, Payoff.staticHedge, hc, Payoff.constOf, StaticHedge.eval_smul,
        ← iha]
      ring
    · have ha : a = .const d := Payoff.eq_const_of_constOf hc
      subst ha
      simp [Payoff.staticHedge, Payoff.constOf, StaticHedge.eval_smul, Payoff.eval,
        StaticHedge.eval]

/-- **A static portfolio exists for every payoff of the fragment**: its value at the terminal price
is the payoff, on every scenario with nonnegative terminal observation. -/
theorem Payoff.IsPiecewiseLinear.exists_hedge {T : ℝ≥0} {e : Payoff Unit}
    (h : e.IsPiecewiseLinear T) :
    ∃ H : StaticHedge, ∀ s : Scenario Unit, 0 ≤ s () T → e.eval s = H.eval (s () T) :=
  ⟨e.staticHedge T, fun s hs ↦ h.eval_staticHedge s hs⟩

/-! ### What the compiled contract pays -/

/-- The present value of a single payment is the discount factor times the payoff. -/
theorem Contract.pathPV_pay {ι : Type*} (D : ℝ≥0 → ℝ) (s : Scenario ι) (t : ℝ≥0)
    (a : Payoff ι) : (Contract.pay t a).pathPV D s = D t * a.eval s := by
  simp [Contract.pathPV, Contract.cashflows]

/-- The present value of the call along a scenario: the discount factor at maturity times the call
payoff of the observation. -/
theorem pathPV_europeanCall (D : ℝ≥0 → ℝ) (s : Scenario Unit) (K : ℝ) (T : ℝ≥0) :
    (europeanCall K T).pathPV D s = D T * max (s () T - K) 0 := by
  simp [europeanCall, europeanCallPayoff, Contract.pathPV_pay, Payoff.eval]

/-- The present value of a portfolio of calls: the discount factor times its call sum at the
terminal observation. -/
theorem pathPV_callPortfolio (D : ℝ≥0 → ℝ) (s : Scenario Unit) (T : ℝ≥0)
    (L : List (ℝ × ℝ)) :
    (callPortfolio T L).pathPV D s = D T * callSum L (s () T) := by
  induction L with
  | nil => simp [callPortfolio, Contract.pathPV, Contract.cashflows]
  | cons p L ih =>
    rw [callPortfolio, Contract.pathPV_both, Contract.pathPV_scale, pathPV_europeanCall, ih,
      callSum_cons]
    ring

/-- **The compiled contract pays the portfolio's value**: along any scenario, for any discount
function, its present value is `D T` times the value of the portfolio at the terminal price. -/
theorem StaticHedge.pathPV_contract (H : StaticHedge) (D : ℝ≥0 → ℝ) (s : Scenario Unit)
    (T : ℝ≥0) : (H.contract T).pathPV D s = D T * H.eval (s () T) := by
  simp only [StaticHedge.contract, Contract.pathPV_both, Contract.pathPV_scale,
    Contract.pathPV_pay, pathPV_callPortfolio, StaticHedge.eval, Payoff.eval]
  ring

/-- **The static hedge of a piecewise-linear payoff replicates it, pathwise.** Along every
scenario with nonnegative terminal observation and for every discount function, the compiled
contract (a bond, a forward and calls) has the present value of `pay T e`. Nothing is assumed of a
model: in any model whose underlying is nonnegative at `T`, the two contracts have equal values
(`Contract.value_pay_eq_value_staticHedge`). -/
theorem Payoff.IsPiecewiseLinear.pathPV_staticHedge {T : ℝ≥0} {e : Payoff Unit}
    (h : e.IsPiecewiseLinear T) (D : ℝ≥0 → ℝ) (s : Scenario Unit) (hs : 0 ≤ s () T) :
    ((e.staticHedge T).contract T).pathPV D s = (Contract.pay T e).pathPV D s := by
  rw [StaticHedge.pathPV_contract, Contract.pathPV_pay, h.eval_staticHedge s hs]

/-! ### A worked example -/

/-- **The compiler on a call**: the payoff `max (S_T − K) 0` compiles to no bond, no forward, and
the one call struck at `K` with weight `1`. -/
theorem staticHedge_europeanCallPayoff (K : ℝ) (T : ℝ≥0) :
    (europeanCallPayoff K T).staticHedge T = ⟨0, 0, [(K, 1)]⟩ := by
  norm_num [europeanCallPayoff, Payoff.staticHedge, StaticHedge.sup, StaticHedge.inf,
    StaticHedge.sub, StaticHedge.add, StaticHedge.smul, StaticHedge.posPart,
    StaticHedge.sortKinks, List.mergeSort_nil, StaticHedge.posAux, StaticHedge.affinePos]

/-- **The capped call, compiled and normalised.** The payoff of the two cash flows of
`cappedCall K₁ K₂ T` (`Contracts/Instruments/Options.lean`), a call at `K₁` less a call at `K₂`,
compiles to the calls `[(K₁, 1), (K₂, -1)]` in the order of the syntax; normalised (sorted by
strike, merged, weights nonzero) it is the portfolio with no bond, no forward and exactly those two
calls, for `K₁ < K₂`. (At `K₁ = K₂` the two calls cancel and the normal form is empty.) -/
theorem staticHedge_cappedCall_normalize {K₁ K₂ : ℝ} (h : K₁ < K₂) (T : ℝ≥0) :
    ((Payoff.sub (europeanCallPayoff K₁ T) (europeanCallPayoff K₂ T)).staticHedge T).normalize
      = ⟨0, 0, [(K₁, 1), (K₂, -1)]⟩ := by
  have e : (Payoff.sub (europeanCallPayoff K₁ T) (europeanCallPayoff K₂ T)).staticHedge T
      = ⟨0, 0, [(K₁, 1), (K₂, -1)]⟩ := by
    simp only [Payoff.staticHedge, staticHedge_europeanCallPayoff]
    simp [StaticHedge.sub, StaticHedge.add, StaticHedge.smul]
  rw [e]
  simp [StaticHedge.normalize, insertCall, h]

end MathFin.Contracts
