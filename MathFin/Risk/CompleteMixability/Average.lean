/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Risk.CompleteMixability

/-!
# Symmetrising a coupling

A coupling of `N + 1` laws with a constant sum need not have equal laws in its first `N`
coordinates. Permuting those coordinates by a uniformly random permutation keeps the sum and
replaces each of their laws by the average of all of them. So it is enough to build a coupling
whose first `N` coordinates have the right *average* law.

## Main results

* `MathFin.JointlyMixable.of_average_snoc`: an average law `G` in the first `N` coordinates and
  law `E` in the last give a joint mix of `N` copies of `G` and one of `E`.

## Tags

complete mixability, exchangeability, symmetrisation, MSC 60E05
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

/-- **Symmetrisation.** If a coupling `ρ` of `N + 1` real coordinates has an a.s. constant sum,
law `E` in its last coordinate and average law `G` in the first `N`
(`∑ i, law (x i) = N • G`), then `N` copies of `G` and one of `E` are jointly mixable: permute the
first `N` coordinates uniformly at random. -/
theorem JointlyMixable.of_average_snoc {N : ℕ} (hN : 0 < N) {G E : Measure ℝ}
    {ρ : Measure (Fin (N + 1) → ℝ)} [IsProbabilityMeasure ρ] {s : ℝ}
    (hs : ∀ᵐ x ∂ρ, ∑ i, x i = s) (hE : ρ.map (fun x ↦ x (Fin.last N)) = E)
    (havg : ∑ i : Fin N, ρ.map (fun x ↦ x i.castSucc) = N • G) :
    JointlyMixable (Fin.snoc (α := fun _ ↦ Measure ℝ) (fun _ : Fin N ↦ G) E) := by
  sorry

end MathFin
