/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Init
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

/-!
# First-contact stability from a vanishing nonnegative gap

## Main results

* `min_time_tendsto_firstContact`: for continuous `g` positive before `τ`, if `g (s n) → 0` then
  `min (s n) τ → τ`.
* `exists_subseq_gap_tendsto_zero`: for integrable nonnegative `G n` whose integrals tend to
  `0`, some strictly increasing subsequence tends to `0` almost surely.

## Tags

first contact stability, vanishing gap, subsequence, nonnegative gap, stopping time convergence,
MSC 60G40, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

theorem min_time_tendsto_firstContact {g : ℝ≥0 → ℝ} (hc : Continuous g)
    {τ : ℝ≥0} (hp : ∀ t, t < τ → 0 < g t) {s : ℕ → ℝ≥0}
    (hs : Tendsto (fun n => g (s n)) atTop (𝓝 0)) :
    Tendsto (fun n => min (s n) τ) atTop (𝓝 τ) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨t,ht,hmin⟩ :=
        isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (show (0 : ℝ≥0) ≤ a from zero_le))
        hc.continuousOn
    have hpos : 0 < g t := hp t (ht.2.trans_lt ha)
    filter_upwards [hs.eventually (gt_mem_nhds hpos)] with n hn
    apply lt_min _ ha
    by_contra hn'
    have hsa : s n ≤ a := le_of_not_gt hn'
    exact (not_lt_of_ge (hmin ⟨zero_le,hsa⟩)) hn
  · intro b hb
    exact Eventually.of_forall (fun _ => (min_le_right _ _).trans_lt hb)

theorem exists_subseq_gap_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {G : ℕ → Ω → ℝ} (hi : ∀ n, Integrable (G n) P) (hpos : ∀ n ω, 0 ≤ G n ω)
    (he : Tendsto (fun n => ∫ ω, G n ω ∂P) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P, Tendsto (fun n => G (ns n) ω) atTop (𝓝 0) := by
  have hnorm (n : ℕ) : eLpNorm (G n) 1 P = ENNReal.ofReal (∫ ω, G n ω ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hi n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => by
      change ‖G n ω‖ = G n ω
      rw [Real.norm_eq_abs,abs_of_nonneg (hpos n ω)])
  have hl : Tendsto (fun n => eLpNorm (G n-(fun _ => (0 : ℝ))) 1 P) atTop (𝓝 0) := by
    have hz (n : ℕ) : G n-(fun _ => (0 : ℝ)) = G n := by funext ω; simp
    simpa only [hz,hnorm,ENNReal.ofReal_zero,Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp he
  exact (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    hl).exists_seq_tendsto_ae

end MathFin.BlackScholes.AmericanPut.Stopping
