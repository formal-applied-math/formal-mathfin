/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import MathFin.Probability.Analysis.StdSimplexMix
public import MathFin.Probability.Laws.FiniteWeights
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring.RingNF

/-!
# von Neumann–Morgenstern lotteries and the expected-utility functional

`Risk.UtilityDerivation` defines the acceptance set of an expected-utility
agent through `expectedUtility` and shows that a concave utility makes it convex and
an increasing one makes it closed under adding cash. Such a set need not be a cone,
so it need not be the acceptance set of a coherent risk measure
(`not_exists_isCoherentRiskMeasure_log_acceptance`). This file supplies the layer
underneath: the affinity of expected utility in the mixture of lotteries and the
verification that an expected-utility preference satisfies the von Neumann–Morgenstern axioms.

## Setup

A **lottery** over a finite outcome type `ι` is a point of Mathlib's standard simplex
`Convexity.StdSimplex ℝ ι`, the library's probability vector on a finite type. Its mixture
`StdSimplex.mix α h₀ h₁ p q = α p + (1 − α) q` at a weight `α ∈ [0, 1]` and the algebra of
mixtures (`mix_one`, `mix_zero`, `mix_self`, `mix_comm`, `mix_compound`) are in
`Probability.Analysis.StdSimplexMix`. A mixture of lotteries is a lottery by construction.

* `expectedUtility s u p` — `∑ i ∈ s, p i * u i`, the weighted sum of the utilities `u` against
  any weight function `p` over the support `s`.
* `prefersEU u p q` — the lottery `p` is weakly preferred to `q`, i.e. `EU q ≤ EU p`.

## The pivot

`expectedUtility_mix` — expected utility is **affine in the mixture**:
`EU(α p + (1−α) q) = α EU(p) + (1−α) EU(q)`.

Everything else in this file is a corollary of that single identity. It is the
formal content of the claim that expected utility "respects compounding", and it
is precisely what fails for the non-linear functionals (rank-dependent utility,
prospect theory) that were invented to explain the Allais paradox.
`expectedUtility_smul_add_smul` is the identity for arbitrary weight functions, which needs no
hypothesis at all: it is linearity of the finite sum.

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

## The representation theorem

The converse direction, that any preference satisfying the four axioms *is* `prefersEU u` for
some `u`, and that `u` is unique up to a positive affine map, is proved in
`Choice.Utility.VonNeumannMorgensternRepresentation` for lotteries over a finite type. That module
calibrates each outcome against a best and a worst lottery and is built on this one.

## Main definitions

* `expectedUtility`: the expected utility `∑ i ∈ s, p i * u i` of the weights `p` over the
  support `s`.
* `prefersEU`: the lottery `p` is weakly preferred to `q` when `EU(q) ≤ EU(p)`.

## Main results

* `expectedUtility_eq_integral`, `expectedUtility_univ_real_eq_integral`: expected utility is the
  integral of the utility against the lottery as a measure (`Measure.ofWeights`).
* `expectedUtility_mix`: expected utility is affine in the mixture,
  `EU(α p + (1 − α) q) = α EU(p) + (1 − α) EU(q)`.
* `prefersEU_total`, `prefersEU_trans`, `prefersEU_refl`: the expected-utility preference is
  complete, transitive and reflexive.
* `prefersEU_independence`, `prefersEU_strict_independence`: mixing a common lottery into both
  sides preserves a weak preference at any weight `α ∈ [0, 1]`, and a strict one at any
  `α ∈ (0, 1]`.
* `prefersEU_continuity`: if `p ≻ q ≻ r` some strict mixture of `p` and `r` has the same
  expected utility as `q`.
* `prefersEU_affine_invariant`: the preference is unchanged by a positive affine rescaling
  `a u + b` of the utility.

## References

* [von Neumann and Morgenstern, *Theory of Games and Economic Behavior*][VonNeumannMorgenstern1944]
* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §1.1

## Tags

von Neumann-Morgenstern, expected utility, lotteries, independence axiom, Archimedean axiom,
utility uniqueness, preference axioms, MSC 91B16, MSC 91B06, JEL D81
-/

@[expose] public section

namespace MathFin

open Convexity

variable {ι : Type*}

/-- **Expected utility** of the weights `p` under the utility `u`, over the support `s`. For a
lottery `p : StdSimplex ℝ ι` it is `expectedUtility Finset.univ u p.weights`. -/
def expectedUtility (s : Finset ι) (u : ι → ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i ∈ s, p i * u i

open MeasureTheory in
/-- **Expected utility is an integral**: for non-negative weights `p`, `expectedUtility s u p` is
`∫ u ∂(∑ i ∈ s, p i • δ_i)`, the integral of the utility against the lottery as a measure. -/
theorem expectedUtility_eq_integral [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (s : Finset ι) {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (u : ι → ℝ) :
    expectedUtility s u p = ∫ i, u i ∂Measure.ofWeights s p :=
  (Measure.integral_ofWeights s hp u).symm

open MeasureTheory in
/-- **The expected utility of a finite measure's point masses is its integral**:
`∑ i, μ {i} * u i = ∫ u ∂μ` on a finite type with measurable singletons. -/
theorem expectedUtility_univ_real_eq_integral [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (μ : Measure ι) [IsFiniteMeasure μ] (u : ι → ℝ) :
    expectedUtility Finset.univ u (fun i ↦ μ.real {i}) = ∫ i, u i ∂μ := by
  rw [expectedUtility_eq_integral _ fun i _ ↦ measureReal_nonneg,
    Measure.ofWeights_univ_real_singleton]

/-! ### The pivot: expected utility is affine in the mixture -/

/-- **Expected utility is affine in the weights**:
`EU(α p + (1 − α) q) = α EU(p) + (1 − α) EU(q)`.

Note it needs *no* hypothesis on `p`, `q` or `α` — it is linearity of the sum, not a fact
about probabilities. -/
theorem expectedUtility_smul_add_smul (s : Finset ι) (u : ι → ℝ) (α : ℝ) (p q : ι → ℝ) :
    expectedUtility s u (α • p + (1 - α) • q)
      = α * expectedUtility s u p + (1 - α) * expectedUtility s u q := by
  simp only [expectedUtility, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ ↦ by ring)

variable [Fintype ι]

/-- `p` is **weakly preferred** to `q` under expected utility. -/
def prefersEU (u : ι → ℝ) (p q : StdSimplex ℝ ι) : Prop :=
  expectedUtility Finset.univ u q.weights ≤ expectedUtility Finset.univ u p.weights

/-- **Expected utility is affine in the mixture**:
`EU(α p + (1 − α) q) = α EU(p) + (1 − α) EU(q)`.

Every axiom verified below is a corollary of this one identity. -/
theorem expectedUtility_mix (u : ι → ℝ) (α : ℝ) (h₀ : 0 ≤ α) (h₁ : α ≤ 1)
    (p q : StdSimplex ℝ ι) :
    expectedUtility Finset.univ u (StdSimplex.mix α h₀ h₁ p q).weights
      = α * expectedUtility Finset.univ u p.weights
        + (1 - α) * expectedUtility Finset.univ u q.weights := by
  rw [StdSimplex.coe_weights_mix, expectedUtility_smul_add_smul]

/-! ### The von Neumann–Morgenstern axioms, verified for `prefersEU` -/

/-- **Completeness**: any two lotteries are comparable. -/
theorem prefersEU_total (u : ι → ℝ) (p q : StdSimplex ℝ ι) :
    prefersEU u p q ∨ prefersEU u q p :=
  le_total _ _

/-- **Transitivity**. -/
theorem prefersEU_trans (u : ι → ℝ) {p q r : StdSimplex ℝ ι}
    (hpq : prefersEU u p q) (hqr : prefersEU u q r) : prefersEU u p r :=
  le_trans hqr hpq

/-- **Reflexivity**. -/
theorem prefersEU_refl (u : ι → ℝ) (p : StdSimplex ℝ ι) : prefersEU u p p :=
  le_refl _

/-- **Independence**: mixing a common lottery `r` into both sides preserves the
preference, at any weight `α ∈ [0, 1]`.

This is the axiom the Allais paradox violates, and the one that forces the
expected-utility form. It is immediate from `expectedUtility_mix`: the `r`
term enters both sides identically and cancels. -/
theorem prefersEU_independence (u : ι → ℝ) {α : ℝ} (h₀ : 0 ≤ α) (h₁ : α ≤ 1)
    {p q r : StdSimplex ℝ ι} (h : prefersEU u p q) :
    prefersEU u (StdSimplex.mix α h₀ h₁ p r) (StdSimplex.mix α h₀ h₁ q r) := by
  unfold prefersEU at h ⊢
  rw [expectedUtility_mix, expectedUtility_mix]
  exact add_le_add (mul_le_mul_of_nonneg_left h h₀) le_rfl

/-- **Strict independence**: a strict preference survives mixing with a common
lottery, at any *positive* weight. -/
theorem prefersEU_strict_independence (u : ι → ℝ) {α : ℝ} (h₀ : 0 < α) (h₁ : α ≤ 1)
    {p q r : StdSimplex ℝ ι}
    (h : expectedUtility Finset.univ u q.weights < expectedUtility Finset.univ u p.weights) :
    expectedUtility Finset.univ u (StdSimplex.mix α h₀.le h₁ q r).weights
      < expectedUtility Finset.univ u (StdSimplex.mix α h₀.le h₁ p r).weights := by
  rw [expectedUtility_mix, expectedUtility_mix]
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h h₀) le_rfl

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
theorem prefersEU_continuity (u : ι → ℝ) {p q r : StdSimplex ℝ ι}
    (hpq : expectedUtility Finset.univ u q.weights < expectedUtility Finset.univ u p.weights)
    (hqr : expectedUtility Finset.univ u r.weights < expectedUtility Finset.univ u q.weights) :
    ∃ (α : ℝ) (h₀ : 0 < α) (h₁ : α < 1),
      expectedUtility Finset.univ u (StdSimplex.mix α h₀.le h₁.le p r).weights
        = expectedUtility Finset.univ u q.weights := by
  obtain ⟨α, hα₀, hα₁, hα⟩ := exists_mix_weight hpq hqr
  exact ⟨α, hα₀, hα₁, by rw [expectedUtility_mix]; exact hα⟩

/-! ### Uniqueness up to a positive affine transformation -/

omit [Fintype ι] in
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
theorem prefersEU_affine_invariant (u : ι → ℝ) {a b : ℝ} (ha : 0 < a)
    (p q : StdSimplex ℝ ι) :
    prefersEU (fun i ↦ a * u i + b) p q ↔ prefersEU u p q := by
  unfold prefersEU
  rw [expectedUtility_affine Finset.univ u a b (p := p.weights) p.total_of_fintype,
    expectedUtility_affine Finset.univ u a b (p := q.weights) q.total_of_fintype,
    add_le_add_iff_right, mul_le_mul_iff_of_pos_left ha]

end MathFin
