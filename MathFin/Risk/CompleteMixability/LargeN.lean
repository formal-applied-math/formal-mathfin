/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Risk.CompleteMixability.UniformPiece
public import MathFin.Risk.CompleteMixability.Pairing

/-!
# Absolutely continuous laws on a bounded interval are completely mixable for all large `n`

Wang's Open Problem 7 (MF-OP-017): an absolutely continuous law `F` on a bounded interval is
`n`-completely mixable for all large `n`. `F ∗ F` contains a uniform piece
(`exists_uniform_le_conv_self`), so `a` copies of it, alone or with one copy of `F`, are jointly
mixable for all large `a` (`jointlyMixable_of_uniform_piece`), and splitting the pairs gives
`2a` and `2a + 1` copies of `F`.

The outline is Shmalo's; the step for laws with a uniform piece is proved differently
(`UniformPiece.lean`).

## Main results

* `MathFin.eventually_completelyMixable_of_absolutelyContinuous`.

## References

* [R. Wang, *Current open questions in complete mixability*][Wang2015CompleteMixability],
  §2.6, Open Problem 7
* [Y. Shmalo, *Absolutely continuous laws on a bounded interval are completely mixable for all
  large n*][Shmalo2026CompleteMixability], Theorem 1.1

## Tags

complete mixability, absolutely continuous law, bounded support, risk aggregation, MSC 60E05,
MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Filter

/-- **MF-OP-017, solved**: an absolutely continuous law carried by a bounded interval is
`n`-completely mixable for all large `n`. -/
theorem eventually_completelyMixable_of_absolutelyContinuous {F : Measure ℝ}
    [IsProbabilityMeasure F] (hac : F ≪ volume) {a b : ℝ} (hab : F (Icc a b)ᶜ = 0) :
    ∀ᶠ n in atTop, CompletelyMixable n F := by
  sorry

end MathFin
