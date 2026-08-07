/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# von Neumann–Morgenstern lotteries and the expected-utility functional

`RiskMeasures.UtilityDerivation` starts from a concave utility and derives the
coherent-risk acceptance-set properties. It takes the *expected-utility form*
`E[u(W + X)]` as given. This file supplies the layer underneath: the mixture
algebra of lotteries, the affinity of expected utility in that mixture, and the
verification that an expected-utility preference satisfies the von Neumann–
Morgenstern axioms.

## Setup

A **lottery** over a finite outcome index `ι` is a probability vector
`p : ι → ℝ` supported on a `Finset ι` — nonnegative, summing to one. Following
the house convention in `UtilityDerivation`, the two conditions travel as
explicit hypotheses rather than in a bundled subtype: every theorem below states
exactly the conditions its proof consumes, and most of the mixture algebra needs
neither.

* `mix α p q` — the compound lottery `α p + (1 − α) q`.
* `expectedUtility s u p` — `∑ i ∈ s, p i * u i`.
* `prefersEU s u p q` — `p` is weakly preferred to `q`, i.e. `EU q ≤ EU p`.

## The mixture algebra

`mix_one`, `mix_zero`, `mix_self`, `mix_comm` and `mix_compound` are the
"fundamental claims about mixture lotteries" that any vNM development needs
before the axioms can even be stated. `mix_nonneg` and `sum_mix` are the
closure facts: a mixture of lotteries is a lottery.

## The pivot

`expectedUtility_mix` — expected utility is **affine in the mixture**:
`EU(α p + (1−α) q) = α EU(p) + (1−α) EU(q)`.

Everything else in this file is a corollary of that single identity. It is the
formal content of the claim that expected utility "respects compounding", and it
is precisely what fails for the non-linear functionals (rank-dependent utility,
prospect theory) that were invented to explain the Allais paradox.

## The axioms, verified

`prefersEU` is shown to be complete (`prefersEU_total`), transitive, reflexive,
and to satisfy **independence** (`prefersEU_independence`, and the strict form)
and **continuity** (`prefersEU_continuity`, the Archimedean property: given
`p ≻ q ≻ r` there is a mixture of `p` and `r` indifferent to `q`, exhibited
explicitly as `(EU q − EU r)/(EU p − EU r)`).

## Uniqueness

`expectedUtility_affine` and `prefersEU_affine_invariant` give the direction of
the vNM uniqueness theorem that is constructive: a positive affine
transformation `u ↦ a·u + b` (`a > 0`) transforms the expected-utility
functional the same way and leaves the induced preference **exactly**
unchanged. This is why utility is "cardinal up to origin and scale", and why no
economic content may be attached to the units of `u`.

## What is *not* in this file

The **representation theorem itself** — the converse direction, that any
preference satisfying the four axioms *is* `prefersEU s u` for some `u`. That
proof calibrates each outcome against a best/worst pair, and needs a
strict-monotonicity lemma for `mix` along `α` plus the Archimedean axiom to
extract the calibrating scalar. It is a substantially longer development and is
deliberately left for its own module; this file is its prerequisite layer, and
supplies the soundness half (`prefersEU` satisfies the axioms) against which
that construction will be checked.

Likewise the converse of `prefersEU_affine_invariant` — that two utilities
representing the same preference *must* differ by a positive affine map — needs
the same calibration argument and belongs with it.
-/

@[expose] public section

namespace MathFin

variable {ι : Type*}

/-- The **compound lottery** `α p + (1 − α) q`: with probability `α` you face
lottery `p`, otherwise `q`. -/
def mix (α : ℝ) (p q : ι → ℝ) : ι → ℝ := fun i ↦ α * p i + (1 - α) * q i

/-- **Expected utility** of the lottery `p` under the utility `u`, over the
support `s`. -/
def expectedUtility (s : Finset ι) (u : ι → ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i ∈ s, p i * u i

/-- `p` is **weakly preferred** to `q` under expected utility. -/
def prefersEU (s : Finset ι) (u : ι → ℝ) (p q : ι → ℝ) : Prop :=
  expectedUtility s u q ≤ expectedUtility s u p

/-! ### The mixture algebra -/

/-- Mixing with certainty on the first lottery returns it. -/
theorem mix_one (p q : ι → ℝ) : mix 1 p q = p := by
  funext i
  simp [mix]

/-- Mixing with certainty on the second lottery returns it. -/
theorem mix_zero (p q : ι → ℝ) : mix 0 p q = q := by
  funext i
  simp [mix]

/-- Mixing a lottery with itself is a no-op, at any weight. -/
theorem mix_self (α : ℝ) (p : ι → ℝ) : mix α p p = p := by
  funext i
  show α * p i + (1 - α) * p i = p i
  ring

/-- Swapping the two lotteries complements the weight. -/
theorem mix_comm (α : ℝ) (p q : ι → ℝ) : mix α p q = mix (1 - α) q p := by
  funext i
  show α * p i + (1 - α) * q i = (1 - α) * q i + (1 - (1 - α)) * p i
  ring

/-- **Reduction of compound lotteries**: mixing `q` into a mixture of `p` and
`q` just rescales the weight on `p`. The formal content of the "only the
resulting distribution matters" assumption. -/
theorem mix_compound (α β : ℝ) (p q : ι → ℝ) :
    mix α (mix β p q) q = mix (α * β) p q := by
  funext i
  show α * (β * p i + (1 - β) * q i) + (1 - α) * q i
      = α * β * p i + (1 - α * β) * q i
  ring

/-- A mixture of nonnegative vectors at a weight in `[0, 1]` is nonnegative. -/
theorem mix_nonneg {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (i : ι) :
    0 ≤ mix α p q i := by
  show 0 ≤ α * p i + (1 - α) * q i
  exact add_nonneg (mul_nonneg hα (hp i)) (mul_nonneg (by linarith) (hq i))

/-- A mixture of probability vectors is a probability vector. Together with
`mix_nonneg`, this is the closure of lotteries under mixing. -/
theorem sum_mix (s : Finset ι) (α : ℝ) {p q : ι → ℝ}
    (hp : ∑ i ∈ s, p i = 1) (hq : ∑ i ∈ s, q i = 1) :
    ∑ i ∈ s, mix α p q i = 1 := by
  have hsplit : ∑ i ∈ s, mix α p q i
      = α * (∑ i ∈ s, p i) + (1 - α) * ∑ i ∈ s, q i := by
    simp only [mix]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [hsplit, hp, hq]
  ring

/-! ### The pivot: expected utility is affine in the mixture -/

/-- **Expected utility is affine in the mixture**:
`EU(α p + (1 − α) q) = α EU(p) + (1 − α) EU(q)`.

Every axiom verified below is a corollary of this one identity. Note it needs
*no* hypothesis on `p`, `q` or `α` — it is linearity of the sum, not a fact
about probabilities. -/
theorem expectedUtility_mix (s : Finset ι) (u : ι → ℝ) (α : ℝ) (p q : ι → ℝ) :
    expectedUtility s u (mix α p q)
      = α * expectedUtility s u p + (1 - α) * expectedUtility s u q := by
  simp only [expectedUtility, mix]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ ↦ by ring)

/-! ### The von Neumann–Morgenstern axioms, verified for `prefersEU` -/

/-- **Completeness**: any two lotteries are comparable. -/
theorem prefersEU_total (s : Finset ι) (u : ι → ℝ) (p q : ι → ℝ) :
    prefersEU s u p q ∨ prefersEU s u q p :=
  le_total _ _

/-- **Transitivity**. -/
theorem prefersEU_trans (s : Finset ι) (u : ι → ℝ) {p q r : ι → ℝ}
    (hpq : prefersEU s u p q) (hqr : prefersEU s u q r) : prefersEU s u p r :=
  le_trans hqr hpq

/-- **Reflexivity**. -/
theorem prefersEU_refl (s : Finset ι) (u : ι → ℝ) (p : ι → ℝ) :
    prefersEU s u p p :=
  le_refl _

/-- **Independence**: mixing a common lottery `r` into both sides preserves the
preference, at any nonnegative weight.

This is the axiom the Allais paradox violates, and the one that forces the
expected-utility form. It is immediate from `expectedUtility_mix`: the `r`
term enters both sides identically and cancels. -/
theorem prefersEU_independence (s : Finset ι) (u : ι → ℝ) {α : ℝ} (hα : 0 ≤ α)
    {p q r : ι → ℝ} (h : prefersEU s u p q) :
    prefersEU s u (mix α p r) (mix α q r) := by
  unfold prefersEU at h ⊢
  rw [expectedUtility_mix, expectedUtility_mix]
  exact add_le_add (mul_le_mul_of_nonneg_left h hα) le_rfl

/-- **Strict independence**: a strict preference survives mixing with a common
lottery, at any *positive* weight. -/
theorem prefersEU_strict_independence (s : Finset ι) (u : ι → ℝ) {α : ℝ}
    (hα : 0 < α) {p q r : ι → ℝ}
    (h : expectedUtility s u q < expectedUtility s u p) :
    expectedUtility s u (mix α q r) < expectedUtility s u (mix α p r) := by
  rw [expectedUtility_mix, expectedUtility_mix]
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h hα) le_rfl

/-- The scalar behind the Archimedean axiom: for reals `R < Q < P` there is a
strict convex weight placing `Q` between `R` and `P`, namely `Q`'s position on
the interval `[R, P]`. Stated on plain reals because that is all it is — the
lottery content of continuity is entirely in `expectedUtility_mix`. -/
theorem exists_mix_weight {P Q R : ℝ} (hpq : Q < P) (hqr : R < Q) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * P + (1 - α) * R = Q := by
  have hPR : 0 < P - R := by linarith
  have hne : P - R ≠ 0 := ne_of_gt hPR
  refine ⟨(Q - R) / (P - R), div_pos (by linarith) hPR, ?_, ?_⟩
  · rw [div_lt_one hPR]
    linarith
  · have key : (Q - R) / (P - R) * (P - R) = Q - R := by
      field_simp
    linear_combination key

/-- **Continuity (the Archimedean axiom)**: if `p ≻ q ≻ r`, some strict mixture
of the best and worst is exactly indifferent to the middle lottery.

The witness is exhibited rather than obtained from a limit: the indifference
weight is the position of `q` on the utility interval `[EU r, EU p]`, which is
the calibration scalar the full representation theorem will read off. -/
theorem prefersEU_continuity (s : Finset ι) (u : ι → ℝ) {p q r : ι → ℝ}
    (hpq : expectedUtility s u q < expectedUtility s u p)
    (hqr : expectedUtility s u r < expectedUtility s u q) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      expectedUtility s u (mix α p r) = expectedUtility s u q := by
  obtain ⟨α, hα0, hα1, hα⟩ := exists_mix_weight hpq hqr
  refine ⟨α, hα0, hα1, ?_⟩
  rw [expectedUtility_mix]
  exact hα

/-! ### Uniqueness up to a positive affine transformation -/

/-- A positive affine transformation of the utility transforms expected utility
the same way: `EU_{a u + b}(p) = a EU_u(p) + b`.

The `∑ p = 1` hypothesis is exactly what turns the constant `b` into itself
rather than into `b · ∑ p` — this is where the lottery's normalisation, unused
by the mixture algebra above, finally does work. -/
theorem expectedUtility_affine (s : Finset ι) (u : ι → ℝ) (a b : ℝ) {p : ι → ℝ}
    (hp : ∑ i ∈ s, p i = 1) :
    expectedUtility s (fun i ↦ a * u i + b) p
      = a * expectedUtility s u p + b := by
  simp only [expectedUtility]
  have hsplit : ∑ i ∈ s, p i * (a * u i + b)
      = a * (∑ i ∈ s, p i * u i) + b * ∑ i ∈ s, p i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ ↦ by ring)
  rw [hsplit, hp]
  ring

/-- **The preference is invariant under positive affine rescaling of utility**.

The vNM utility is cardinal only up to origin and scale: `u` and `a·u + b` with
`a > 0` induce the *same* preference relation, so no economic meaning attaches
to the units of `u`. (Comparisons of utility *differences* do survive, which is
what distinguishes vNM utility from the ordinal utility of consumer theory.) -/
theorem prefersEU_affine_invariant (s : Finset ι) (u : ι → ℝ) {a b : ℝ}
    (ha : 0 < a) {p q : ι → ℝ}
    (hp : ∑ i ∈ s, p i = 1) (hq : ∑ i ∈ s, q i = 1) :
    prefersEU s (fun i ↦ a * u i + b) p q ↔ prefersEU s u p q := by
  unfold prefersEU
  rw [expectedUtility_affine s u a b hp, expectedUtility_affine s u a b hq,
    add_le_add_iff_right, mul_le_mul_iff_of_pos_left ha]

end MathFin
