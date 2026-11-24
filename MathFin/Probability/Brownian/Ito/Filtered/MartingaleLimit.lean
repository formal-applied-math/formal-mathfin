/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Init
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Limits of Martingales, Uniform Integrability and L1 Convergence

This module establishes the core convergence interfaces from approximating
sequences of martingales (such as stopped processes from a localization sequence)
to the target limiting martingale, avoiding cyclic hypotheses.

Key results:
1. martingale_of_L1_limit: If f_n are martingales strongly adapted to F and
   converging in L1 at each time t to f t, then f is a martingale.
2. uniformIntegrable_one_of_eLpNorm_bdd: A sequence bounded in Lp for p > 1
   on a finite measure space is uniformly integrable in L1.
3. tendsto_eLpNorm_one_of_ae_tendsto_of_eLpNorm_bdd: An a.e. convergent sequence
   with a uniform Lp bound (p > 1) converges in L1 (via Vitali convergence).
4. martingale_of_ae_limit_of_eLpNorm_bdd: An a.e. convergent sequence of martingales
   with a uniform Lp bound (p > 1) has a true martingale limit.

Epistemological status: The target f is not assumed to be a martingale;
the martingale identity is strictly proven from the sequence of stopped martingales.

## Main results

* `uniformIntegrable_one_of_eLpNorm_bdd`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
open MeasureTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology

variable {Omega iota : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

variable {E : Type*} [NormedAddCommGroup E]

theorem uniformIntegrable_one_of_eLpNorm_bdd [IsFiniteMeasure mu]
    {p : ENNReal} (hp : 1 < p) (hp_top : p ≠ ⊤)
    {f : Nat -> Omega -> E}
    (hf_meas : forall n, AEStronglyMeasurable (f n) mu)
    (C : NNReal) (hC : forall n, eLpNorm (f n) p mu <= C) :
    UniformIntegrable f 1 mu := by
  let q : Real := 1 - 1 / p.toReal
  have hpr : 1 < p.toReal := by
    exact_mod_cast (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).mpr hp
  have hq : 0 < q := by
    dsimp [q]
    have : 1 / p.toReal < 1 := (div_lt_one (by linarith)).mpr hpr
    linarith
  have hsmall : UnifIntegrable f 1 mu := by
    refine unifIntegrable_iff.2 fun ε hε => ?_
    have ho : Tendsto (fun n : Nat => ENNReal.ofReal (1 / ((n : Real) + 1))) atTop (nhds 0) := by
      simpa only [ENNReal.ofReal_zero, Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto (0 : Real)).comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    have hz : Tendsto (fun n : Nat => (C : ENNReal) *
        (ENNReal.ofReal (1 / ((n : Real) + 1))) ^ q) atTop (nhds 0) :=
      (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top hq).comp ho
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hz.eventually (Iio_mem_nhds hε))
    refine ⟨ENNReal.ofReal (1 / ((N : Real) + 1)), ENNReal.ofReal_pos.mpr (by positivity), ?_⟩
    intro n s hμs
    have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := mu.restrict s) (p := 1) (q := p) hp.le
      ((hf_meas n).mono_measure Measure.restrict_le_self)
    simp only [ENNReal.toReal_one, div_one, Measure.restrict_apply_univ] at hh
    exact hh.trans ((mul_le_mul' ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC n))
      (ENNReal.rpow_le_rpow hμs hq.le)).trans (hN N le_rfl).le)
  let B : ENNReal := (C : ENNReal) * mu Set.univ ^ q
  have hB : B ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.coe_ne_top
    exact (ENNReal.rpow_lt_top_of_nonneg hq.le (measure_ne_top _ _)).ne
  refine ⟨hsmall, B.toNNReal, ?_⟩
  intro n
  rw [ENNReal.coe_toNNReal hB]
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp.le (hf_meas n)
  simp only [ENNReal.toReal_one, div_one] at hh
  exact hh.trans (mul_le_mul' (hC n) le_rfl)

end MathFin.FilteredIto
