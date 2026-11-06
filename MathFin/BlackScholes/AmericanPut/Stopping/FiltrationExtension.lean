/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.LocalizationTimes
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-! # Bounded continuous supermartingales under filtration extension

Right continuation and adjoining ambient-measurable null sets preserve the
supermartingale property. Completing the ambient measure space is separate.

## Main results

* `supermartingale_of_setIntegral_ge`: an adapted integrable process with
  `∫_s U j ≤ ∫_s U i` for `i ≤ j` and `s ∈ 𝓕 i` is a supermartingale.
* `bounded_continuous_supermartingale_rightCont`: a supermartingale with continuous paths and
  a uniform bound is also a supermartingale for the right-continuous filtration `𝓕.rightCont`.

## Tags

right continuation, null augmentation, supermartingale, filtration enlargement, usual conditions,
MSC 60G40, MSC 60G44
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {U : ℝ≥0 → Ω → ℝ}

theorem supermartingale_of_setIntegral_ge
    (hadapt : StronglyAdapted 𝓕 U) (hint : ∀ t, Integrable (U t) P)
    (hge : ∀ i j, i ≤ j → ∀ s, MeasurableSet[𝓕 i] s →
      ∫ ω in s, U j ω ∂P ≤ ∫ ω in s, U i ω ∂P) : Supermartingale U 𝓕 P := by
  have hn : Submartingale (-U) 𝓕 P := submartingale_of_setIntegral_le hadapt.neg
    (fun t => (hint t).neg) (by
      intro i j hij s hs
      simpa only [Pi.neg_apply,integral_neg,neg_le_neg_iff] using hge i j hij s hs)
  simpa only [neg_neg] using hn.neg

theorem bounded_continuous_supermartingale_rightCont (hU : Supermartingale U 𝓕 P)
    (hcont : ∀ ω, Continuous (fun t => U t ω)) {C : ℝ} (hb : ∀ t ω, ‖U t ω‖ ≤ C) :
    Supermartingale U 𝓕.rightCont P := by
  apply supermartingale_of_setIntegral_ge
    (fun t => (hU.stronglyAdapted t).mono (𝓕.le_rightCont t)) hU.integrable
  intro i j hij s hs
  rcases hij.eq_or_lt with heq | hlt
  · subst j
    exact le_rfl
  let u : ℕ → ℝ≥0 := fun n => min j (i+(localizationEps n).toNNReal)
  have hiu (n : ℕ) : i < u n := lt_min hlt
    (lt_add_of_pos_right i (Real.toNNReal_pos.mpr (localizationEps_pos n)))
  have huj (n : ℕ) : u n ≤ j := min_le_left _ _
  have hlim : Tendsto u atTop (𝓝 i) := by
    have heps : Tendsto (fun n => (localizationEps n).toNNReal) atTop (𝓝 0) := by
      have htime : Continuous (fun x : ℝ => x.toNNReal) := by fun_prop
      convert! (htime.tendsto 0).comp localizationEps_tendsto using 1
      simp
    simpa only [u,add_zero,min_eq_right hij] using
      (tendsto_const_nhds (x := j)).min ((tendsto_const_nhds (x := i)).add heps)
  have hsu (n : ℕ) : MeasurableSet[𝓕 (u n)] s := by
    have hle : 𝓕.rightCont i ≤ 𝓕 (u n) := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le (u n) (hiu n)
    exact hle s hs
  have hc : Tendsto (fun n => ∫ ω in s, U (u n) ω ∂P) atTop (𝓝 (∫ ω in s, U i ω ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (hU.integrable (u n)).aestronglyMeasurable.restrict) (integrable_const C)
      (fun n => Eventually.of_forall (hb (u n)))
      (Eventually.of_forall (fun ω => ((hcont ω).tendsto i).comp hlim))
  exact ge_of_tendsto hc (Eventually.of_forall (fun n => hU.setIntegral_le (huj n) (hsu n)))

end MathFin.BlackScholes.AmericanPut.Stopping
