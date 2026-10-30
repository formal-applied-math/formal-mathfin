/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.RiskMeasures.Coherent

/-!
# Coherent risk measures of positions are coherent risk measures of losses

Artzner, Delbaen, Eber and Heath state coherence for **positions**: a position `X` is a gain, so
a risk measure `ρ` *decreases* in `X` (`X ≤ Y → ρ Y ≤ ρ X`) and adding cash `m` lowers the capital
requirement (`ρ (X + m) = ρ X − m`). The library's single coherence structure is stated for
**losses** (`IsCoherentRiskMeasure`, McNeil–Frey–Embrechts' convention), where `ρ` increases and
`ρ (L + m) = ρ L + m`. The two are one object seen through the sign flip `L = −X`.

`isCoherentRiskMeasure_count_neg_iff` makes that precise on a finite state space `ι` with counting
measure, where almost-sure order is pointwise order and every function is integrable: `ρ` satisfies
the four ADEH axioms for positions exactly when `L ↦ ρ (−L)` is an `IsCoherentRiskMeasure`.
The axioms of positions are written out rather than bundled in a second structure: bundling them
would be the duplicate that this module exists to remove. `Solution.lean` uses the statement to
discharge the positions-convention declarations of `Challenge.lean`, which may not import the
library.

## Main results

* `isCoherentRiskMeasure_count_neg_iff`: the four ADEH axioms for positions, written out, are
  equivalent to `IsCoherentRiskMeasure Measure.count (fun L ↦ ρ (-L))`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory

/-- **Positions versus losses.** On a finite state space with counting measure, a functional
`ρ : (ι → ℝ) → ℝ` satisfies the four Artzner–Delbaen–Eber–Heath axioms for positions
(monotone decreasing, `ρ (X + m) = ρ X − m`, positively homogeneous, subadditive) if and only if
`L ↦ ρ (−L)` is a coherent risk measure of losses. -/
theorem isCoherentRiskMeasure_count_neg_iff {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {ρ : (ι → ℝ) → ℝ} :
    IsCoherentRiskMeasure (Measure.count : Measure ι) (fun L ↦ ρ (-L)) ↔
      (∀ X Y : ι → ℝ, (∀ i, X i ≤ Y i) → ρ Y ≤ ρ X) ∧
      (∀ (X : ι → ℝ) (m : ℝ), ρ (fun i ↦ X i + m) = ρ X - m) ∧
      (∀ l : ℝ, 0 ≤ l → ∀ X : ι → ℝ, ρ (l • X) = l * ρ X) ∧
      ∀ X Y : ι → ℝ, ρ (X + Y) ≤ ρ X + ρ Y := by
  constructor
  · intro hρ
    refine ⟨fun X Y h ↦ ?_, fun X m ↦ ?_, fun l hl X ↦ ?_, fun X Y ↦ ?_⟩
    · simpa only [neg_neg] using
        hρ.mono_of_le (X := -Y) (Y := -X) fun i ↦ neg_le_neg (h i)
    · have h := hρ.add_const (X := -fun i ↦ X i + m) .of_finite m
      have e : (-fun ω ↦ (-fun i ↦ X i + m) ω + m) = X := by
        ext i; simp only [Pi.neg_apply]; ring
      change ρ (-fun ω ↦ (-fun i ↦ X i + m) ω + m) = ρ (-(-fun i ↦ X i + m)) + m at h
      rw [e, neg_neg] at h
      linarith
    · have h := hρ.const_mul (X := -X) .of_finite hl
      have e : (-fun ω ↦ l * (-X) ω) = l • X := by
        ext i; simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; ring
      change ρ (-fun ω ↦ l * (-X) ω) = l * ρ (-(-X)) at h
      rwa [e, neg_neg] at h
    · have h := hρ.add_le (X := -X) (Y := -Y) .of_finite .of_finite
      have e : (-fun ω ↦ (-X) ω + (-Y) ω) = X + Y := by
        ext i; simp only [Pi.neg_apply, Pi.add_apply]; ring
      change ρ (-fun ω ↦ (-X) ω + (-Y) ω) ≤ ρ (-(-X)) + ρ (-(-Y)) at h
      rwa [e, neg_neg, neg_neg] at h
  · rintro ⟨hm, hc, hh, hs⟩
    refine ⟨fun X Y _ _ h ↦ ?_, fun X _ m ↦ ?_, fun X _ c hc' ↦ ?_, fun X Y _ _ ↦ ?_⟩
    · exact hm (-Y) (-X) fun i ↦ neg_le_neg (ae_count_iff.1 h i)
    · have e : (-fun ω ↦ X ω + m) = fun i ↦ (-X) i + -m := by
        ext i; simp only [Pi.neg_apply]; ring
      change ρ (-fun ω ↦ X ω + m) = ρ (-X) + m
      rw [e, hc (-X) (-m)]
      ring
    · have e : (-fun ω ↦ c * X ω) = c • -X := by
        ext i; simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; ring
      change ρ (-fun ω ↦ c * X ω) = c * ρ (-X)
      rw [e, hh c hc' (-X)]
    · have e : (-fun ω ↦ X ω + Y ω) = -X + -Y := by
        ext i; simp only [Pi.neg_apply, Pi.add_apply]; ring
      change ρ (-fun ω ↦ X ω + Y ω) ≤ ρ (-X) + ρ (-Y)
      rw [e]
      exact hs (-X) (-Y)

end MathFin
