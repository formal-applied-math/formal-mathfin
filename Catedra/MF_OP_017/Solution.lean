/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Risk.CompleteMixability.LargeN

/-!
# MF-OP-017, the comparator's solution

The pinned statement of `Catedra/MF_OP_017/Challenge.lean`, repeated verbatim and proved from the
library: `CompletelyMixable n F` unfolds to the coupling the challenge asks for, and
`MathFin.eventually_completelyMixable_of_absolutelyContinuous` proves it for all large `n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

/-- **MF-OP-017: bounded absolutely continuous laws are eventually completely mixable** (Wang
2015, Open Problem 7). -/
theorem MathFinFrontier.absolutelyContinuous_eventually_completelyMixable {F : Measure ℝ}
    [IsProbabilityMeasure F] (hac : F ≪ volume) {a b : ℝ} (hab : F (Set.Icc a b)ᶜ = 0) :
    ∀ᶠ n in atTop, ∃ π : Measure (Fin n → ℝ), IsProbabilityMeasure π ∧
      (∀ i, π.map (fun x ↦ x i) = F) ∧ ∃ c, ∀ᵐ x ∂π, ∑ i, x i = c :=
  MathFin.eventually_completelyMixable_of_absolutelyContinuous hac hab
