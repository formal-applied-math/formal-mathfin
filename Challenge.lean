import Mathlib

/-!
# The Artzner–Delbaen–Eber–Heath representation of a coherent risk measure

A **coherent risk measure** on a finite state space `ι` is a functional
`ρ : (ι → ℝ) → ℝ` on state-contingent payoffs satisfying the four axioms of
Artzner, Delbaen, Eber and Heath, *Coherent measures of risk*,
Mathematical Finance **9** (1999) 203–228: monotonicity, cash invariance,
positive homogeneity, and subadditivity. `ρ X` is read as the capital that must
be added to the position `X` to make it acceptable.

The representation theorem of that paper says a coherent risk measure is always
a **worst-case expected loss**: there is a family `Q` of probability vectors on
`ι` with `ρ X = sup_{q ∈ Q} 𝔼_q[−X]`, and one may take `Q` to be the
*representing set* of `ρ` — the probability vectors that price every acceptable
payoff nonnegatively.

`coherentRisk_isLUB` states this in its sharp form: `ρ X` is the *least* upper
bound of `{𝔼_q[−X] : q ∈ representingSet ρ}`. Two things are worth noting about
that phrasing.

* `IsLUB` is strictly stronger than "`ρ X` is an upper bound". The upper-bound
  half is cash invariance; the least-upper-bound half is the substance, and is
  obtained by separating the rejected position `X + (ρ X − ε)·1` from the
  acceptance cone `{Y | ρ Y ≤ 0}` and normalising the separating functional to a
  probability vector.
* Because `ℝ` has no least element, `IsLUB ∅ c` is false for every `c`. So the
  statement also asserts that `representingSet ρ` is *nonempty*: the supremum
  ranges over a genuinely inhabited family of probability vectors rather than
  holding vacuously.

`worstCase_isCoherentRisk` is recorded alongside it so that the hypothesis of
the representation theorem is mechanically known to be satisfiable: on a
nonempty state space, worst-case loss `X ↦ maxᵢ (−Xᵢ)` is coherent. (On an
empty state space there is no coherent risk measure at all, since cash
invariance then demands `ρ X = ρ X − m` for every `m`.)

The state space is finite. The separation argument is therefore the
finite-dimensional one, and no topological dual or σ-additivity hypothesis
appears; the general (infinite-dimensional) ADEH statement is not claimed here.
-/

namespace ADEH

/-- The four Artzner–Delbaen–Eber–Heath axioms of a coherent risk measure on a
finite state space `ι`.

* `monotone` — a pointwise larger payoff is no riskier.
* `cashInvariant` — adding `m` units of cash to the position reduces the
  required capital by exactly `m`.
* `posHom` — positive homogeneity: scaling a position scales its risk.
* `subadditive` — diversification does not increase risk. -/
structure IsCoherentRisk {ι : Type*} [Fintype ι] (ρ : (ι → ℝ) → ℝ) : Prop where
  monotone : ∀ X Y : ι → ℝ, (∀ i, X i ≤ Y i) → ρ Y ≤ ρ X
  cashInvariant : ∀ (X : ι → ℝ) (m : ℝ), ρ (fun i ↦ X i + m) = ρ X - m
  posHom : ∀ (l : ℝ), 0 ≤ l → ∀ X : ι → ℝ, ρ (l • X) = l * ρ X
  subadditive : ∀ X Y : ι → ℝ, ρ (X + Y) ≤ ρ X + ρ Y

/-- The **representing set** of `ρ`: the probability vectors `q` on `ι`
(nonnegative, summing to `1`) that assign nonnegative price `∑ᵢ qᵢ Zᵢ` to every
acceptable position `Z`, i.e. to every `Z` with `ρ Z ≤ 0`.

These are exactly the densities of the "generalised scenarios" of Artzner,
Delbaen, Eber and Heath, obtained here as the linear functionals separating the
acceptance set from the rejected positions. -/
def representingSet {ι : Type*} [Fintype ι] (ρ : (ι → ℝ) → ℝ) : Set (ι → ℝ) :=
  {q | (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧ ∀ Z ∈ {Y : ι → ℝ | ρ Y ≤ 0}, 0 ≤ ∑ i, q i * Z i}

/-- **The ADEH representation theorem on a finite state space.** A coherent risk
measure `ρ` is the supremum of expected loss over its representing probability
vectors: `ρ X` is the least upper bound of `{∑ᵢ qᵢ(−Xᵢ) : q ∈ representingSet ρ}`.

As noted in the module docstring, `IsLUB` over `ℝ` also carries the assertion
that `representingSet ρ` is nonempty. -/
theorem coherentRisk_isLUB {ι : Type*} [Fintype ι] {ρ : (ι → ℝ) → ℝ}
    (hρ : IsCoherentRisk ρ) (X : ι → ℝ) :
    IsLUB ((fun q ↦ ∑ i, q i * (- X i)) '' representingSet ρ) (ρ X) := sorry

/-- **The hypothesis of `coherentRisk_isLUB` is satisfiable.** Worst-case loss
`X ↦ maxᵢ (−Xᵢ)` on a nonempty finite state space satisfies the four ADEH
axioms, so the representation theorem above is not vacuously quantified. -/
theorem worstCase_isCoherentRisk {ι : Type*} [Fintype ι] [Nonempty ι] :
    IsCoherentRisk
      (fun X : ι → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ - X i)) := sorry

end ADEH
