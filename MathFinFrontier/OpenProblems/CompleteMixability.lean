/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Open problems MF-OP-016 and MF-OP-017: complete mixability

Catalogue records `MF-OP-016` and `MF-OP-017` (`docs/research-problems/README.md`); frontier
nodes `thm:uniform-convex-complete-mixability` and `thm:bounded-law-complete-mixability`.

A law `F` is **`n`-completely mixable** if there are random variables `X₁, …, Xₙ`, each with law
`F`, whose sum is almost surely constant. This is the extreme negative dependence of risk
aggregation: sharp bounds on the `VaR` of a sum with given marginals are built from completely
mixable pieces. Both questions below are open problems
of Wang's survey (*Current open questions in complete mixability*, Probability Surveys 12, 2015).
Each statement asserts the positive answer. A counterexample settles the problem by proving the
negation.

A coupling is a probability measure `π` on `Fin n → E` whose coordinate marginals are `F`, so
both statements use no definition the reader has to trust.

* MF-OP-016 (Open Problem 5): the uniform law on a bounded convex body of `ℝᵈ` is `n`-completely
  mixable for every `n ≥ d + 1`. Known for `d ≤ 1`.
* MF-OP-017 (Open Problem 7): an absolutely continuous law on a bounded interval is
  `n`-completely mixable for all large `n`. Known when the density is bounded away from zero.
  Two unrefereed claims disagree: Yin–Zhu (arXiv 1706.05499) are reported to give a
  counterexample, and Shmalo (Zenodo 24070253, November 2026) gives a proof that disputes it.
  Neither has been checked here.
  The catalogue records it as `resolution_reported`.
-/

open MeasureTheory ProbabilityTheory Filter

/-- **MF-OP-016: the uniform law on a convex body is completely mixable** (Wang 2015, Open
Problem 5). For a bounded convex set `C ⊆ ℝᵈ` with nonempty interior and `n ≥ d + 1`, there is a
coupling of `n` copies of the uniform law on `C` whose sum is almost surely constant. -/
theorem MathFinFrontier.uniform_convex_completelyMixable {d : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : Convex ℝ C) (hbdd : Bornology.IsBounded C)
    (hint : (interior C).Nonempty) {n : ℕ} (hn : d + 1 ≤ n) :
    ∃ π : Measure (Fin n → EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure π ∧
      (∀ i, π.map (fun x ↦ x i) = volume[|C]) ∧ ∃ c, ∀ᵐ x ∂π, ∑ i, x i = c := by
  sorry

/-- **MF-OP-017: bounded absolutely continuous laws are eventually completely mixable** (Wang
2015, Open Problem 7). If `F` is an absolutely continuous probability law carried by a bounded
interval `[a, b]`, then for all large `n` there is a coupling of `n` copies of `F` whose sum is
almost surely constant. -/
theorem MathFinFrontier.absolutelyContinuous_eventually_completelyMixable {F : Measure ℝ}
    [IsProbabilityMeasure F] (hac : F ≪ volume) {a b : ℝ} (hab : F (Set.Icc a b)ᶜ = 0) :
    ∀ᶠ n in atTop, ∃ π : Measure (Fin n → ℝ), IsProbabilityMeasure π ∧
      (∀ i, π.map (fun x ↦ x i) = F) ∧ ∃ c, ∀ᵐ x ∂π, ∑ i, x i = c := by
  sorry
