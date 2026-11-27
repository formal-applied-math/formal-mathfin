/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Risk.CompleteMixability
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Pairs of copies: the law of `X + X'`

Two facts about `F ∗ F`, the law of the sum of two independent copies of `F`, that reduce
complete mixability of `F` to that of `F ∗ F`.

* If `F` is carried by a bounded interval and has a nonzero absolutely continuous part, `F ∗ F`
  contains a multiple of a uniform law, even when `F` itself does not (a density supported on a
  fat Cantor set): `g ⋆ g` is continuous for `g = min (f, M)` and has a positive integral.
* A joint mix of `a` copies of `F ∗ F` (and one of `F`) splits into a complete mix of `2a`
  copies of `F` (`2a + 1`): draw each pair from the law of `(X, X')` given `X + X'`.

## Main results

* `MathFin.exists_uniform_le_conv_self`: `F ∗ F` dominates `q` times a uniform law.
* `MathFin.completelyMixable_two_mul_of_conv`, `MathFin.completelyMixable_two_mul_add_one_of_conv`.

## References

* [Y. Shmalo, *Absolutely continuous laws on a bounded interval are completely mixable for all
  large n*][Shmalo2026CompleteMixability], Lemmas 4.1 and 4.2

## Tags

complete mixability, convolution, disintegration, MSC 60E05
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- **`F ∗ F` contains a uniform piece** (Shmalo, Lemma 4.1, for absolutely continuous `F`). -/
theorem exists_uniform_le_conv_self {F : Measure ℝ} [IsProbabilityMeasure F] (hac : F ≪ volume)
    {a b : ℝ} (hab : F (Icc a b)ᶜ = 0) :
    ∃ c H q : ℝ, 0 < H ∧ 0 < q ∧ q ≤ 1 ∧ Icc (c - H) (c + H) ⊆ Icc (2 * a) (2 * b) ∧
      ENNReal.ofReal q • volume[|Icc (c - H) (c + H)] ≤ F ∗ F := by
  sorry

/-- **Splitting pairs** (Shmalo, Lemma 4.2, even case). -/
theorem completelyMixable_two_mul_of_conv {F : Measure ℝ} [IsProbabilityMeasure F] {a : ℕ}
    (h : CompletelyMixable a (F ∗ F)) : CompletelyMixable (2 * a) F := by
  sorry

/-- **Splitting pairs** (Shmalo, Lemma 4.2, odd case): `a` copies of `F ∗ F` jointly mixable with
one copy of `F` give `2a + 1` copies of `F`. -/
theorem completelyMixable_two_mul_add_one_of_conv {F : Measure ℝ} [IsProbabilityMeasure F]
    {a : ℕ} (h : JointlyMixable (Fin.snoc (α := fun _ ↦ Measure ℝ) (fun _ : Fin a ↦ F ∗ F) F)) :
    CompletelyMixable (2 * a + 1) F := by
  sorry

end MathFin
