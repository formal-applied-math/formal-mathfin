/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Purged train/test interval disjointness

López de Prado (*Advances in Financial Machine Learning*, ch. 7) purges a
training interval `[t0 i, t1 i]` from a cross-validation fold whenever it
overlaps a test interval `[t0' j, t1' j]`: it starts inside the test interval,
ends inside it, or envelops it. This file states that three-way overlap
predicate literally as given and proves the combinatorial payoff: any
training interval surviving purging against every test interval is genuinely
disjoint from each of them.

## Main results

* `overlapsTest_of_mem_of_mem`: if some point lies in both a training and a test
  interval, the overlap predicate holds between them (the interval-arithmetic
  heart of the result).
* `purged_disjoint`: a training interval `i` purging leaves untouched (no
  test interval triggers the overlap predicate against it) is disjoint from
  every test interval.
-/

@[expose] public section

namespace MathFin

variable {ι κ : Type*}

/-- The purge-trigger predicate: training interval `i` starts inside, ends
inside, or envelops test interval `j`. -/
def overlapsTest (lo hi : ι → ℝ) (lo' hi' : κ → ℝ) (i : ι) (j : κ) : Prop :=
  (lo' j ≤ lo i ∧ lo i ≤ hi' j) ∨ (lo' j ≤ hi i ∧ hi i ≤ hi' j) ∨ (lo i ≤ lo' j ∧ hi' j ≤ hi i)

/-- If a point lies in both intervals, the overlap predicate holds between
them: comparing `lo' j` with `lo i`, and then `hi i` with `hi' j`, picks which
of the three overlap cases applies. -/
theorem overlapsTest_of_mem_of_mem (lo hi : ι → ℝ) (lo' hi' : κ → ℝ) {i : ι} {j : κ} {t : ℝ}
    (ht : t ∈ Set.Icc (lo i) (hi i)) (ht' : t ∈ Set.Icc (lo' j) (hi' j)) :
    overlapsTest lo hi lo' hi' i j := by
  obtain ⟨hlo, hhi⟩ := ht
  obtain ⟨hlo', hhi'⟩ := ht'
  rcases le_total (lo' j) (lo i) with h1 | h1
  · exact Or.inl ⟨h1, hlo.trans hhi'⟩
  · rcases le_total (hi i) (hi' j) with h2 | h2
    · exact Or.inr (Or.inl ⟨hlo'.trans hhi, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- The disjointness invariant: a training interval `i` that no test interval
`j` triggers the purge predicate on is disjoint from every test interval. -/
theorem purged_disjoint (lo hi : ι → ℝ) (lo' hi' : κ → ℝ) {i : ι}
    (hret : ∀ j, ¬ overlapsTest lo hi lo' hi' i j) (j : κ) :
    Disjoint (Set.Icc (lo i) (hi i)) (Set.Icc (lo' j) (hi' j)) := by
  rw [Set.disjoint_left]
  intro t ht ht'
  exact hret j (overlapsTest_of_mem_of_mem lo hi lo' hi' ht ht')

end MathFin
