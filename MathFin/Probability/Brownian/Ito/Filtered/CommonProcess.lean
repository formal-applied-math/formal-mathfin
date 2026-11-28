/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonL2

/-!
# Common Process

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Common-filtration extension for Heston, 2026-10-18.

## Main definitions

* `itoSimpleProcess`
* `itoSimpleProcessLp`

## Main results

* `memLp_value`
* `memLp_truncated_term`
* `memLp_itoSimpleProcess`

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

open MeasureTheory ProbabilityTheory
open MathFin.FilteredIto.CommonNoise
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

/-- Partial Brownian increment sum of a simple process up to the evaluation time. -/
noncomputable def itoSimpleProcess (_hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ)
    (t : ℝ≥0) : Ω → ℝ :=
  SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ) V B t

private lemma stoppedProcess_const_coe (u s : ℝ≥0) (ω : Ω) :
    stoppedProcess B (fun _ : Ω ↦ u) s ω = B (min s u) ω := rfl

lemma itoSimpleProcess_apply (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ)
    (t : ℝ≥0) (ω : Ω) :
    itoSimpleProcess hBmeas V t ω
      = V.value.sum fun p v ↦ v ω * (B (min p.2 t) ω - B (min p.1 t) ω) := by
  simp only [itoSimpleProcess, SimpleProcess.integral, ContinuousLinearMap.mul_apply']
  refine Finsupp.sum_congr fun p _ ↦ ?_
  rw [stoppedProcess_const_coe, stoppedProcess_const_coe]

lemma itoSimpleProcess_add (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ ℱ)
    (t : ℝ≥0) :
    itoSimpleProcess hBmeas (V + W) t = itoSimpleProcess hBmeas V t
      + itoSimpleProcess hBmeas W t := by
  funext ω
  simp only [itoSimpleProcess, SimpleProcess.integral_add_left, Pi.add_apply]

lemma itoSimpleProcess_smul (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    (V : SimpleProcess ℝ ℱ) (t : ℝ≥0) :
    itoSimpleProcess hBmeas (c • V) t = c • itoSimpleProcess hBmeas V t := by
  funext ω
  simp only [itoSimpleProcess, SimpleProcess.integral_smul_left, Pi.smul_apply]

lemma itoSimpleProcess_neg (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) (t : ℝ≥0) :
    itoSimpleProcess hBmeas (-V) t = -itoSimpleProcess hBmeas V t := by
  funext ω
  simp only [itoSimpleProcess, SimpleProcess.integral_neg_left, Pi.neg_apply]

@[simp] lemma itoSimpleProcess_zero_time (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) :
    itoSimpleProcess hBmeas V 0 = 0 := by
  funext ω
  rw [itoSimpleProcess_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  have e1 : min p.1 (0 : ℝ≥0) = 0 := min_eq_right zero_le
  have e2 : min p.2 (0 : ℝ≥0) = 0 := min_eq_right zero_le
  rw [e1, e2, sub_self, mul_zero]

lemma itoSimpleProcess_eq_itoSimple (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ)
    {t : ℝ≥0} (ht : ∀ p ∈ V.value.support, p.2 ≤ t) :
    itoSimpleProcess hBmeas V t = CommonL2.itoSimple hBmeas V := by
  funext ω
  rw [itoSimpleProcess_apply, CommonL2.itoSimple_apply]
  refine Finsupp.sum_congr fun p hp ↦ ?_
  have h2 : min p.2 t = p.2 := min_eq_left (ht p hp)
  have h1 : min p.1 t = p.1 := min_eq_left ((V.le_of_mem_support_value p hp).trans (ht p hp))
  rw [h1, h2]

variable (hB : IsFilteredPreBrownian B ℱ μ)

include hB

theorem memLp_value (_hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ)
    (p : ℝ≥0 × ℝ≥0) : MemLp (V.value p) 2 μ := by
  haveI : IsProbabilityMeasure μ := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  exact MemLp.of_bound
    ((V.measurable_value p).mono (ℱ.le p.1)
      le_rfl).aestronglyMeasurable
    V.valueBound (ae_of_all _ (V.value_le_valueBound p))

theorem memLp_truncated_term (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ)
    (t : ℝ≥0) {p : ℝ≥0 × ℝ≥0} (hp : p ∈ V.value.support) :
    MemLp (fun ω ↦ V.value p ω * (B (min p.2 t) ω - B (min p.1 t) ω)) 2 μ := by
  haveI : IsProbabilityMeasure μ := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  by_cases ht : p.1 ≤ t
  ·
    rw [min_eq_left ht]
    exact MathFin.ItoIsometryAdapted.memLp_adapted_mul_increment hB
      (le_min (V.le_of_mem_support_value p hp) ht)
      (CommonL2.adaptedAt_of_measurable hBmeas (V.measurable_value p))
      (memLp_value hB hBmeas V p)
  ·
    push Not at ht
    have h1 : min p.1 t = t := min_eq_right ht.le
    have h2 : min p.2 t = t := min_eq_right (ht.le.trans (V.le_of_mem_support_value p hp))
    simp only [h1, h2, sub_self, mul_zero]
    exact memLp_const 0

theorem memLp_itoSimpleProcess (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ)
    (t : ℝ≥0) :
    MemLp (itoSimpleProcess hBmeas V t) 2 μ := by
  rw [show itoSimpleProcess hBmeas V t
        = fun ω ↦ ∑ p ∈ V.value.support, V.value p ω * (B (min p.2 t) ω - B (min p.1 t) ω)
      from funext fun ω ↦ by rw [itoSimpleProcess_apply]; rfl]
  exact memLp_finsetSum _ fun p hp ↦ memLp_truncated_term hB hBmeas V t hp

/-- Partial Brownian increment sum as a square-integrable random variable. -/
noncomputable def itoSimpleProcessLp (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ)
    (t : ℝ≥0) : Lp ℝ 2 μ :=
  (memLp_itoSimpleProcess hB hBmeas V t).toLp _

end CommonProcess
end MathFin.FilteredIto
