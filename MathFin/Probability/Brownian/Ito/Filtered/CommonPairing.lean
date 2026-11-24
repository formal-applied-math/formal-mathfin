/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.FilteredBrownian

/-!
# Common Pairing

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted to a specified common filtration, 2026-10-18.

## Main definitions

* `AdaptedAt`

## Main results

* `memLp_adapted_mul_increment`
* `integral_adapted_sq_mul_increment_sq`
* `adapted_indepFun_forward`

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

variable (hB : BrownianOn ℱ B μ)
include hB

theorem adaptedAt_eval {s u : ℝ≥0} (hu : u ≤ s) : AdaptedAt ℱ s (B u) :=
  (hB.adapted u).measurable.mono (ℱ.mono hu) le_rfl

theorem integral_adapted_mul_increment (_hBm : ∀ t, Measurable (B t))
    {s t : ℝ≥0} (hst : s ≤ t) {f : Ω → ℝ} (hf : AdaptedAt ℱ s f) :
    (∫ ω, f ω * (B t ω - B s ω) ∂μ) = 0 :=
  MathFin.ItoIsometryAdapted.integral_adapted_mul_increment hB.isFilteredPreBrownian hst hf

theorem memLp_adapted_mul_increment (_hBm : ∀ t, Measurable (B t))
    {s t : ℝ≥0} (hst : s ≤ t) {f : Ω → ℝ} (hf : AdaptedAt ℱ s f)
    (hf2 : MemLp f 2 μ) : MemLp (fun ω => f ω * (B t ω - B s ω)) 2 μ :=
  MathFin.ItoIsometryAdapted.memLp_adapted_mul_increment hB.isFilteredPreBrownian hst hf hf2

theorem integral_adapted_sq_mul_increment_sq (_hBm : ∀ t, Measurable (B t))
    {s t : ℝ≥0} (hst : s ≤ t) {f : Ω → ℝ} (hf : AdaptedAt ℱ s f) :
    (∫ ω, f ω ^ 2 * (B t ω - B s ω) ^ 2 ∂μ) =
      (∫ ω, f ω ^ 2 ∂μ) * ((t : ℝ) - s) :=
  MathFin.ItoIsometryAdapted.integral_adapted_mul_increment_sq hB.isFilteredPreBrownian hst
        (Measurable.pow_const hf 2)

theorem adapted_indepFun_forward (_hBm : ∀ t, Measurable (B t)) {s : ℝ≥0}
    {f : Ω → ℝ} (hf : AdaptedAt ℱ s f)
    {H : (ℝ≥0 → ℝ) → ℝ} (hH : Measurable H) :
    IndepFun f (fun ω => H (fun u => B (s+u) ω - B s ω)) μ :=
  (hB.future_independent s hf).comp measurable_id hH

end MathFin.FilteredIto.CommonPairing
