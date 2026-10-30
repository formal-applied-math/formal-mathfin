import MathFin.RiskMeasures.AcceptanceSet
import MathFin.RiskMeasures.PositionsConvention
import MathFin.RiskMeasures.WorstCaseRisk

/-!
# Proofs of the advertised statements

The two declarations of `Challenge.lean` are repeated here verbatim and proved
by discharging them against the proof development in `MathFin/RiskMeasures/`.
The Challenge states coherence for **positions** (a position is a gain, so `ρ`
decreases and `ρ (X + m) = ρ X - m`); the library has one coherence structure,
`MathFin.IsCoherentRiskMeasure`, stated for **losses**. The bridge is
`MathFin.isCoherentRiskMeasure_count_neg_iff`
(`MathFin/RiskMeasures/PositionsConvention.lean`): on a finite state space with
counting measure, `ρ` satisfies the four positions axioms exactly when
`L ↦ ρ (-L)` is an `IsCoherentRiskMeasure`.

* `MathFin.coherentRisk_isLUB` (`MathFin/RiskMeasures/AcceptanceSet.lean`) —
  the separation argument that yields the representation, applied to `L ↦ ρ (-L)`;
* `MathFin.worstCase_isCoherent` (`MathFin/RiskMeasures/WorstCaseRisk.lean`) —
  the coherence of worst-case loss, transported along the same bridge.

`ADEH.IsCoherentRisk` and `ADEH.representingSet` are declared here with the same
bodies as in the Challenge, so Comparator sees identical constants. The library
has no counterpart of `IsCoherentRisk` (that would be the duplicate), so the
axioms are handed to the bridge field by field; `ADEH.representingSet ρ` is the
library's `MathFin.representingSet` of `L ↦ ρ (-L)` under the sign flip.
-/

namespace ADEH

/-- The four Artzner–Delbaen–Eber–Heath axioms of a coherent risk measure on a
finite state space `ι`. -/
structure IsCoherentRisk {ι : Type*} [Fintype ι] (ρ : (ι → ℝ) → ℝ) : Prop where
  monotone : ∀ X Y : ι → ℝ, (∀ i, X i ≤ Y i) → ρ Y ≤ ρ X
  cashInvariant : ∀ (X : ι → ℝ) (m : ℝ), ρ (fun i ↦ X i + m) = ρ X - m
  posHom : ∀ (l : ℝ), 0 ≤ l → ∀ X : ι → ℝ, ρ (l • X) = l * ρ X
  subadditive : ∀ X Y : ι → ℝ, ρ (X + Y) ≤ ρ X + ρ Y

/-- The representing set of `ρ`. -/
def representingSet {ι : Type*} [Fintype ι] (ρ : (ι → ℝ) → ℝ) : Set (ι → ℝ) :=
  {q | (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧ ∀ Z ∈ {Y : ι → ℝ | ρ Y ≤ 0}, 0 ≤ ∑ i, q i * Z i}

/-- The ADEH representation theorem on a finite state space. -/
theorem coherentRisk_isLUB {ι : Type*} [Fintype ι] {ρ : (ι → ℝ) → ℝ}
    (hρ : IsCoherentRisk ρ) (X : ι → ℝ) :
    IsLUB ((fun q ↦ ∑ i, q i * (- X i)) '' representingSet ρ) (ρ X) := by
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  have hrep : MathFin.representingSet (fun L : ι → ℝ ↦ ρ (-L)) = representingSet ρ := by
    ext q
    have e (Y : ι → ℝ) : ∑ i, q i * (-Y) i = -∑ i, q i * Y i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ mul_neg _ _
    refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨fun h Y hY ↦ ?_, fun h Z hZ ↦ ?_⟩
    · have := h (-Y) (by show ρ (-(-Y)) ≤ 0; rw [neg_neg]; exact hY)
      rw [e] at this
      linarith
    · have := h (-Z) hZ
      rw [e] at this
      linarith
  have h := MathFin.coherentRisk_isLUB
    (MathFin.isCoherentRiskMeasure_count_neg_iff.2
      ⟨hρ.monotone, hρ.cashInvariant, hρ.posHom, hρ.subadditive⟩) (-X)
  rw [hrep] at h
  simpa only [neg_neg, Pi.neg_apply] using h

/-- Worst-case loss satisfies the four ADEH axioms. -/
theorem worstCase_isCoherentRisk {ι : Type*} [Fintype ι] [Nonempty ι] :
    IsCoherentRisk
      (fun X : ι → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ - X i)) := by
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  have e : (fun L : ι → ℝ ↦
      (fun X : ι → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ - X i)) (-L)) =
        MathFin.worstCase := by
    funext L
    simp only [MathFin.worstCase, Pi.neg_apply, neg_neg]
  have h : MathFin.IsCoherentRiskMeasure (MeasureTheory.Measure.count : MeasureTheory.Measure ι)
      (fun L : ι → ℝ ↦
        (fun X : ι → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ - X i)) (-L)) := by
    rw [e]; exact MathFin.worstCase_isCoherent
  obtain ⟨h₁, h₂, h₃, h₄⟩ := (MathFin.isCoherentRiskMeasure_count_neg_iff
    (ρ := fun X : ι → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ - X i))).1 h
  exact ⟨h₁, h₂, h₃, h₄⟩

end ADEH
