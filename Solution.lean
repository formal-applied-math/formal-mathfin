import MathFin.RiskMeasures.AcceptanceSet
import MathFin.RiskMeasures.WorstCaseRisk

/-!
# Proofs of the advertised statements

The two declarations of `Challenge.lean` are repeated here verbatim and proved
by discharging them against the proof development in `MathFin/RiskMeasures/`:

* `MathFin.coherentRisk_isLUB` (`MathFin/RiskMeasures/AcceptanceSet.lean`) —
  the separation argument that yields the representation;
* `MathFin.worstCase_isCoherent` (`MathFin/RiskMeasures/WorstCaseRisk.lean`) —
  the coherence of worst-case loss.

`ADEH.IsCoherentRisk` and `ADEH.representingSet` are declared here with the same
bodies as in the Challenge, so Comparator sees identical constants; the bridge
to their `MathFin` counterparts is definitional in both cases.
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
    IsLUB ((fun q ↦ ∑ i, q i * (- X i)) '' representingSet ρ) (ρ X) :=
  MathFin.coherentRisk_isLUB
    ⟨hρ.monotone, hρ.cashInvariant, hρ.posHom, hρ.subadditive⟩ X

/-- Worst-case loss satisfies the four ADEH axioms. -/
theorem worstCase_isCoherentRisk {ι : Type*} [Fintype ι] [Nonempty ι] :
    IsCoherentRisk
      (fun X : ι → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ - X i)) :=
  have h := MathFin.worstCase_isCoherent (ι := ι)
  ⟨h.monotone, h.cashInvariant, h.posHom, h.subadditive⟩

end ADEH
