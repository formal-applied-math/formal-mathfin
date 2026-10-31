/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Binomial.MartingaleRepresentation
public import MathFin.Binomial.SnellEnvelope

/-!
# A European claim in the binomial tree is replicated, and its price is the hedge's cost

`binomialPrice u d r g N S₀` is the backward-induction price of the claim that pays `g(S_N)`
after `N` steps. This file proves it is also the initial capital of a hedge: under
no-arbitrage there is a predictable strategy `H` such that, along every coin-flip path,

  `e^{−rN} g(S_N) = binomialPrice u d r g N S₀ + (H · S̃)_N`,

the `martingaleTransform` `∑_{k<N} H_{k+1} (S̃_{k+1} − S̃_k)` of `H` against the discounted spot,
where `S̃_k = e^{−rk} S_k` is the discounted spot (`binomialPrice_replication`). The proof
is the discrete martingale representation theorem (`binomial_martingale_representation`)
applied to two one-step martingales: the discounted tree value of the claim, stopped at `N`
(`discountedTreeValue_step`, which is `binomialPrice_succ`), and the discounted spot
(`discountedSpot_step`, which is `crrUpProb_mul_up_add`).

## Main definitions

* `discountedTreeValue` — the discounted tree price of the claim along a path, stopped at `N`.
* `discountedSpot` — the discounted spot `e^{−rk} S_k`.

## Main results

* `discountedTreeValue_step`, `discountedSpot_step` — both are one-step martingales under the
  risk-neutral up-probability.
* `binomialPrice_replication` — the claim's discounted payoff is its tree price plus the gains of a
  predictable strategy in the discounted spot, on every path.
-/

@[expose] public section

namespace MathFin

/-- A function of the first `m` flips is a function of the first `n`, for `m ≤ n`. -/
lemma PathAdaptedAt.mono {m n : ℕ} {X : (ℕ → Bool) → ℝ} (h : PathAdaptedAt m X)
    (hmn : m ≤ n) : PathAdaptedAt n X :=
  fun ω ω' hω ↦ h ω ω' fun i hi ↦ hω i (hi.trans_le hmn)

/-- The spot after `k` flips does not see the `n`-th flip, for `k ≤ n`. -/
lemma spotPath_update_of_le {k n : ℕ} (hkn : k ≤ n) (S₀ u d : ℝ) (ω : ℕ → Bool) (b : Bool) :
    spotPath S₀ u d k (Function.update ω n b) = spotPath S₀ u d k ω :=
  pathAdaptedAt_spotPath S₀ u d k _ _ fun _ hi ↦ Function.update_of_ne (hi.trans_le hkn).ne _ _

@[simp]
lemma spotPath_zero (S₀ u d : ℝ) (ω : ℕ → Bool) : spotPath S₀ u d 0 ω = S₀ := by
  simp [spotPath]

/-- The **discounted tree value** of the claim `g(S_N)` along a path, stopped at `N`: at step `n`
it is `e^{−r(n ∧ N)}` times the tree price with `N − n` steps left, at the spot reached by step
`n ∧ N`. -/
noncomputable def discountedTreeValue (u d r : ℝ) (g : ℝ → ℝ) (N : ℕ) (S₀ : ℝ) (n : ℕ)
    (ω : ℕ → Bool) : ℝ :=
  Real.exp (-(r * (min n N : ℕ))) * binomialPrice u d r g (N - n) (spotPath S₀ u d (min n N) ω)

/-- The **discounted spot** `S̃_n = e^{−rn} S_n`. -/
noncomputable def discountedSpot (S₀ u d r : ℝ) (n : ℕ) (ω : ℕ → Bool) : ℝ :=
  Real.exp (-(r * n)) * spotPath S₀ u d n ω

lemma pathAdaptedAt_discountedTreeValue (u d r : ℝ) (g : ℝ → ℝ) (N : ℕ) (S₀ : ℝ) (n : ℕ) :
    PathAdaptedAt n (discountedTreeValue u d r g N S₀ n) := fun ω ω' hω ↦ by
  rw [discountedTreeValue, discountedTreeValue,
    ((pathAdaptedAt_spotPath S₀ u d _).mono (min_le_left n N)) ω ω' hω]

lemma pathAdaptedAt_discountedSpot (S₀ u d r : ℝ) (n : ℕ) :
    PathAdaptedAt n (discountedSpot S₀ u d r n) := fun ω ω' hω ↦ by
  rw [discountedSpot, discountedSpot, pathAdaptedAt_spotPath S₀ u d n ω ω' hω]

/-- **The discounted tree value is a one-step martingale** under the risk-neutral
up-probability: before `N` this is the backward recursion `binomialPrice_succ`, and from `N` on
the process is frozen. No no-arbitrage hypothesis is needed. -/
theorem discountedTreeValue_step (u d r : ℝ) (g : ℝ → ℝ) (N : ℕ) (S₀ : ℝ) (n : ℕ)
    (ω : ℕ → Bool) :
    crrUpProb u d r * discountedTreeValue u d r g N S₀ (n + 1) (Function.update ω n true)
      + (1 - crrUpProb u d r)
        * discountedTreeValue u d r g N S₀ (n + 1) (Function.update ω n false)
      = discountedTreeValue u d r g N S₀ n ω := by
  rcases lt_or_ge n N with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k, N = n + 1 + k := ⟨N - (n + 1), by omega⟩
    simp only [discountedTreeValue, show min (n + 1) (n + 1 + k) = n + 1 by omega,
      show min n (n + 1 + k) = n by omega, show n + 1 + k - n = k + 1 by omega,
      show n + 1 + k - (n + 1) = k by omega, spotPath_update_succ_true,
      spotPath_update_succ_false, binomialPrice_succ]
    rw [show -(r * ((n + 1 : ℕ) : ℝ)) = -(r * n) + -r by push_cast; ring, Real.exp_add]
    ring
  · simp only [discountedTreeValue, show min (n + 1) N = N by omega, show min n N = N by omega,
      show N - n = 0 by omega, show N - (n + 1) = 0 by omega, spotPath_update_of_le hn]
    ring

/-- **The discounted spot is a one-step martingale** under the risk-neutral up-probability:
`q u + (1 − q) d = eʳ` (`crrUpProb_mul_up_add`). -/
theorem discountedSpot_step {u d r : ℝ} (h : BinomialNoArb u d r) (S₀ : ℝ) (n : ℕ)
    (ω : ℕ → Bool) :
    crrUpProb u d r * discountedSpot S₀ u d r (n + 1) (Function.update ω n true)
      + (1 - crrUpProb u d r) * discountedSpot S₀ u d r (n + 1) (Function.update ω n false)
      = discountedSpot S₀ u d r n ω := by
  simp only [discountedSpot, spotPath_update_succ_true, spotPath_update_succ_false]
  rw [show -(r * ((n + 1 : ℕ) : ℝ)) = -(r * n) + -r by push_cast; ring, Real.exp_add]
  have he : Real.exp (-r) * Real.exp r = 1 := by rw [← Real.exp_add]; simp
  linear_combination Real.exp (-(r * n)) * Real.exp (-r) * spotPath S₀ u d n ω
      * crrUpProb_mul_up_add u d r h + Real.exp (-(r * n)) * spotPath S₀ u d n ω * he

/-- Under no-arbitrage and `S₀ ≠ 0`, the two children of a node have different discounted spots. -/
lemma discountedSpot_update_ne {u d r : ℝ} (h : BinomialNoArb u d r) {S₀ : ℝ} (hS₀ : S₀ ≠ 0)
    (n : ℕ) (ω : ℕ → Bool) :
    discountedSpot S₀ u d r (n + 1) (Function.update ω n true)
      ≠ discountedSpot S₀ u d r (n + 1) (Function.update ω n false) := by
  have hS : spotPath S₀ u d n ω ≠ 0 :=
    mul_ne_zero hS₀ (Finset.prod_ne_zero_iff.2 fun i _ ↦ by
      split_ifs
      exacts [h.u_pos.ne', h.d_pos.ne'])
  simp only [discountedSpot, spotPath_update_succ_true, spotPath_update_succ_false]
  intro heq
  exact h.d_lt_u.ne' (mul_left_cancel₀ hS (mul_left_cancel₀ (Real.exp_pos _).ne' heq))

/-- **The tree price is the cost of a hedge.** Under no-arbitrage and `S₀ ≠ 0`, for every payoff
`g` and horizon `N` there is a predictable strategy `H` (`H_{k+1}` depends only on the first `k`
flips) whose `martingaleTransform` against the discounted spot, added to the tree price, is the
discounted payoff on every path:

  `e^{−rN} g(S_N) = binomialPrice u d r g N S₀ + ∑_{k<N} H_{k+1} (S̃_{k+1} − S̃_k)`. -/
theorem binomialPrice_replication {u d r : ℝ} (h : BinomialNoArb u d r) {S₀ : ℝ} (hS₀ : S₀ ≠ 0)
    (g : ℝ → ℝ) (N : ℕ) :
    ∃ H : ℕ → (ℕ → Bool) → ℝ, (∀ n, PathAdaptedAt n (H (n + 1))) ∧ ∀ ω,
      Real.exp (-(r * N)) * g (spotPath S₀ u d N ω) = binomialPrice u d r g N S₀
        + martingaleTransform H (discountedSpot S₀ u d r) N ω := by
  obtain ⟨H, hH, hrep⟩ := binomial_martingale_representation
    (pathAdaptedAt_discountedTreeValue u d r g N S₀) (pathAdaptedAt_discountedSpot S₀ u d r)
    (discountedTreeValue_step u d r g N S₀) (discountedSpot_step h S₀)
    (discountedSpot_update_ne h hS₀)
  refine ⟨H, hH, fun ω ↦ ?_⟩
  simpa [discountedTreeValue] using hrep N ω

end MathFin
