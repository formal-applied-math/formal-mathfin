/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonProcessMartingale
public import BrownianMotion.StochasticIntegral.LocalMartingale

/-!
# Common Process Local Martingale

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Common-filtration extension for Heston, 2026-10-18.

## Main results

* `itoSimpleProcess_pathContinuous`
* `itoSimpleProcess_isLocalMartingale`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise
open scoped NNReal ENNReal
namespace MathFin.FilteredIto
namespace CommonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ} (hB : IsFilteredPreBrownian B ℱ μ)

include hB

omit hB in

theorem itoSimpleProcess_pathContinuous (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (V : SimpleProcess ℝ ℱ) (ω : Ω) :
    Continuous fun t : ℝ≥0 ↦ itoSimpleProcess hBmeas V t ω := by
  simp_rw [fun t ↦ itoSimpleProcess_apply hBmeas V t ω, Finsupp.sum]
  refine continuous_finsetSum _ fun p _ ↦ ?_
  refine continuous_const.mul (Continuous.sub ?_ ?_)
  · exact (hBcont ω).comp (continuous_const.min continuous_id)
  · exact (hBcont ω).comp (continuous_const.min continuous_id)

theorem itoSimpleProcess_isLocalMartingale (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (V : SimpleProcess ℝ ℱ) :
    IsLocalMartingale (fun t ω ↦ itoSimpleProcess hBmeas V t ω)
      ℱ μ :=
  Martingale.IsLocalMartingale (itoSimpleProcess_isMartingale hB hBmeas V)
    (fun ω ↦ (itoSimpleProcess_pathContinuous hBmeas hBcont V ω).isCadlag)

end CommonProcess
end MathFin.FilteredIto
