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
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf

/-! # First contact for a continuous scalar profile

Selecting the first nonnegative point gives a full interval of strict
negativity before contact. No differentiability or isolated-contact premise
is needed.

## Main results

* `exists_first_nonnegative_contact`: if `f` is continuous on `[a, m]` with `f a < 0 ≤ f m`,
  there is `T ∈ (a, m]` with `f T = 0` and `f < 0` on `[a, T)`.

## Tags

first contact, continuous function, first nonnegative point, contact point, MSC 35R35, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology

theorem exists_first_nonnegative_contact {f : ℝ → ℝ} {a m : ℝ} (ham : a ≤ m)
    (hf : ContinuousOn f (Icc a m)) (ha : f a < 0) (hm : 0 ≤ f m) :
    ∃ T, a < T ∧ T ≤ m ∧ f T = 0 ∧ ∀ t ∈ Ico a T, f t < 0 := by
  let S := Icc a m ∩ f ⁻¹' Ici 0
  have hS : IsCompact S := hf.upperSemicontinuousOn.isCompact_inter_preimage_Ici isCompact_Icc 0
  obtain ⟨T,hT⟩ := hS.exists_isLeast (show S.Nonempty from ⟨m,⟨ham,le_rfl⟩,hm⟩)
  have hTa : a < T := lt_of_le_of_ne hT.1.1.1 (by
    intro he
    have hn : 0 ≤ f T := hT.1.2
    rw [← he] at hn
    linarith)
  have hTm : T ≤ m := hT.1.1.2
  have hzero : f T = 0 := by
    have hn : 0 ≤ f T := hT.1.2
    apply le_antisymm _ hn
    by_contra! hp
    obtain ⟨r,hr,he⟩ := intermediate_value_Icc hTa.le
      (hf.mono (Icc_subset_Icc_right hTm)) ⟨ha.le,hn⟩
    have hrS : r ∈ S := ⟨⟨hr.1,hr.2.trans hTm⟩,by simp only [mem_preimage,mem_Ici,he,le_refl]⟩
    have hTr : T ≤ r := hT.2 hrS
    have hre : r = T := le_antisymm hr.2 hTr
    rw [hre] at he
    linarith
  refine ⟨T,hTa,hTm,hzero,?_⟩
  intro t ht
  by_contra! hn
  have hmem : t ∈ S := ⟨⟨ht.1,ht.2.le.trans hTm⟩,hn⟩
  exact (not_le_of_gt ht.2) (hT.2 hmem)

end MathFin.BlackScholes.AmericanPut.Boundary
