/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Coherent risk measures: the four axioms of Artzner, Delbaen, Eber and Heath

A **coherent risk measure** on the integrable losses of a measure space `(Ω, P)` is a functional
`ρ : (Ω → ℝ) → ℝ` with the four axioms of Artzner, Delbaen, Eber and Heath, *Coherent measures of
risk*, Math. Finance **9** (1999), in the convention of McNeil, Frey and Embrechts (*Quantitative
Risk Management*, Definition 2.18): a **loss** is signed as a loss, so a larger `X` is worse and
`ρ` increases with it.

* `mono`: `X ≤ Y` almost surely gives `ρ X ≤ ρ Y`;
* `add_const`: `ρ (X + m) = ρ X + m`, so `ρ X` is the capital that makes the loss `X` acceptable;
* `const_mul`: `ρ (c X) = c ρ X` for `c ≥ 0`;
* `add_le`: `ρ (X + Y) ≤ ρ X + ρ Y`.

This is the one coherence structure of the library: value-at-risk's cousin expected shortfall, the
spectral risk measures, worst-case loss and the acceptance-set theory
(`RiskMeasures/AcceptanceSet.lean`) all land in it. The older *positions* convention of the ADEH
paper (a position `X` is a gain, its loss is `−X`; `ρ` decreases with `X` and
`ρ (X + m) = ρ X − m`) is the same object at `L ↦ ρ(−L)` on a finite state space with counting
measure; `RiskMeasures/PositionsConvention.lean` proves that.

The axioms only constrain `ρ` on integrable losses, and almost-sure monotonicity is the weakest
order that makes `ρ` a function of the loss's law. On a finite state space with a finite measure
every function is integrable and the order is still implied by the pointwise order, so the
finite-state theory (`IsCoherentRiskMeasure.mono_of_le`, `IsCoherentRiskMeasure.continuous`) needs
no support hypothesis.

## Main results

* `IsCoherentRiskMeasure`: the four axioms.
* `IsCoherentRiskMeasure.rho_zero`: `ρ 0 = 0`.
* `IsCoherentRiskMeasure.convexOn`: `ρ` is convex on the integrable losses.
* `IsCoherentRiskMeasure.mono_of_le`, `IsCoherentRiskMeasure.continuous`: on a finite state space
  `ρ` is pointwise-monotone and continuous.
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A measure that charges every point of a countable space sees all of it: a property holds
almost everywhere exactly when it holds everywhere. Counting measure is the case `P {ω} = 1`. -/
lemma ae_iff_forall_of_singleton_ne_zero {P : Measure Ω} {p : Ω → Prop} [Countable Ω]
    [MeasurableSingletonClass Ω] (hP : ∀ ω, P {ω} ≠ 0) : (∀ᵐ ω ∂P, p ω) ↔ ∀ ω, p ω := by
  rw [ae_iff_of_countable]
  exact forall_congr' fun ω ↦ ⟨fun h ↦ h (hP ω), fun h _ ↦ h⟩

/-- The four axioms of a **coherent risk measure** (Artzner, Delbaen, Eber and Heath 1999;
McNeil–Frey–Embrechts, Definition 2.18) for a functional `ρ` on the integrable losses of
`(Ω, P)`: monotonicity, translation invariance, positive homogeneity and subadditivity. A loss is
signed as a loss, so a larger `X` is worse and `ρ` increases with it. -/
structure IsCoherentRiskMeasure (P : Measure Ω) (ρ : (Ω → ℝ) → ℝ) : Prop where
  mono : ∀ ⦃X Y : Ω → ℝ⦄, Integrable X P → Integrable Y P → X ≤ᵐ[P] Y → ρ X ≤ ρ Y
  add_const : ∀ ⦃X : Ω → ℝ⦄, Integrable X P → ∀ m : ℝ, ρ (fun ω ↦ X ω + m) = ρ X + m
  const_mul : ∀ ⦃X : Ω → ℝ⦄, Integrable X P → ∀ ⦃c : ℝ⦄, 0 ≤ c →
    ρ (fun ω ↦ c * X ω) = c * ρ X
  add_le : ∀ ⦃X Y : Ω → ℝ⦄, Integrable X P → Integrable Y P →
    ρ (fun ω ↦ X ω + Y ω) ≤ ρ X + ρ Y

namespace IsCoherentRiskMeasure

variable {P : Measure Ω} {ρ : (Ω → ℝ) → ℝ}

/-- `ρ 0 = 0` (positive homogeneity at `c = 2`). -/
lemma rho_zero (hρ : IsCoherentRiskMeasure P ρ) : ρ 0 = 0 := by
  have h := hρ.const_mul (integrable_zero Ω ℝ P) (c := 2) (by norm_num)
  rw [show (fun ω ↦ 2 * (0 : Ω → ℝ) ω) = 0 by ext; simp] at h
  linarith

/-- A coherent risk measure is convex on the integrable losses (positive homogeneity and
subadditivity). -/
lemma convexOn (hρ : IsCoherentRiskMeasure P ρ) : ConvexOn ℝ {X | Integrable X P} ρ := by
  refine ⟨fun x hx y hy a b _ _ _ ↦ ?_, fun x hx y hy a b ha hb _ ↦ ?_⟩
  · exact (hx.smul a).add (hy.smul b)
  · have h := hρ.add_le (hx.const_mul a) (hy.const_mul b)
    rw [hρ.const_mul hx ha, hρ.const_mul hy hb] at h
    exact h

section Finite

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {P : Measure ι} [IsFiniteMeasure P] {ρ : (ι → ℝ) → ℝ}

/-- On a finite state space a pointwise smaller loss has the smaller risk: pointwise order implies
almost-sure order, and every function is integrable. -/
lemma mono_of_le (hρ : IsCoherentRiskMeasure P ρ) {X Y : ι → ℝ} (h : X ≤ Y) : ρ X ≤ ρ Y :=
  hρ.mono .of_finite .of_finite (ae_of_all _ h)

/-- A finite-state coherent risk measure is convex on all of `ℝ^ι`. -/
lemma convexOn_univ (hρ : IsCoherentRiskMeasure P ρ) : ConvexOn ℝ Set.univ ρ := by
  simpa [show {X : ι → ℝ | Integrable X P} = Set.univ from
    Set.eq_univ_of_forall fun _ ↦ .of_finite] using hρ.convexOn

/-- A finite-state coherent risk measure is continuous (a finite convex function on `ℝ^ι`). -/
lemma continuous (hρ : IsCoherentRiskMeasure P ρ) : Continuous ρ := by
  rw [← continuousOn_univ]
  exact hρ.convexOn_univ.continuousOn isOpen_univ

end Finite

end IsCoherentRiskMeasure

end MathFin
