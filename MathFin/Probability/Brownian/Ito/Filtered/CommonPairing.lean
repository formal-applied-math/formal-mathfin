/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.FilteredBrownian

/-!
# Measurability at a filtration time

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted to a specified common filtration, 2026-10-18.

## Main definitions

* `AdaptedAt`

## Main results

* `adaptedAt_eval` gives measurability of an earlier driver value at a later time.

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto.CommonPairing
open MeasureTheory ProbabilityTheory
open MathFin.FilteredIto.CommonNoise
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

/-- Measurability of a real random variable with respect to the filtration at a fixed time. -/
def AdaptedAt (ℱ : Filtration ℝ≥0 mΩ) (s : ℝ≥0) (f : Ω → ℝ) : Prop :=
  Measurable[ℱ s] f

theorem AdaptedAt.measurable (_hBm : ∀ t, Measurable (B t)) {s : ℝ≥0}
    {f : Ω → ℝ} (hf : AdaptedAt ℱ s f) : Measurable f := hf.mono (ℱ.le s) le_rfl

theorem AdaptedAt.mono {s t : ℝ≥0} (hst : s ≤ t) {f : Ω → ℝ}
    (hf : AdaptedAt ℱ s f) : AdaptedAt ℱ t f := Measurable.mono hf (ℱ.mono hst) le_rfl

theorem AdaptedAt.mul {s : ℝ≥0} {f g : Ω → ℝ}
    (hf : AdaptedAt ℱ s f) (hg : AdaptedAt ℱ s g) :
    AdaptedAt ℱ s (fun ω => f ω * g ω) := Measurable.mul hf hg

theorem AdaptedAt.sub {s : ℝ≥0} {f g : Ω → ℝ}
    (hf : AdaptedAt ℱ s f) (hg : AdaptedAt ℱ s g) :
    AdaptedAt ℱ s (fun ω => f ω - g ω) := Measurable.sub hf hg

variable (hB : IsFilteredPreBrownian B ℱ μ)
include hB

theorem adaptedAt_eval {s u : ℝ≥0} (hu : u ≤ s) : AdaptedAt ℱ s (B u) :=
  (hB.stronglyAdapted u).measurable.mono (ℱ.mono hu) le_rfl

end MathFin.FilteredIto.CommonPairing
