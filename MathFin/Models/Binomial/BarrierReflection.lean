/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.Binomial.PathMeasure
public import MathFin.Models.Binomial.PathReflection
public import Mathlib.Basic.Real.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Barrier-option counting via the reflection principle

`Models/Binomial/PathReflection.lean` builds André's reflection bijection
`reflectionPrincipleEquivBelow : {ω // hit a ∧ end = b} ≃ {ω // end = 2a − b}` (for
`0 < a`, `b ≤ a`) and notes that *"the `Fintype.card` identity is their immediate corollary
and is not separately stated here."* This file states it — the counting backbone of
binomial barrier-option pricing — and derives the **maximal-distribution identity**, the
running-maximum law that prices the knock-in.

## Main definitions

* `reflectHitLtGt`: the equivalence between paths that hit `a` and end below `a`, and paths that
  hit `a` and end above `a`.
* `hitAboveEquiv`: for `0 < a`, paths that hit `a` and end above `a` are in bijection with paths
  ending above `a`.
* `hitAtEquiv`: for `0 < a`, paths that hit `a` and end at `a` are in bijection with paths
  ending at `a`.

## Main results

* `reflection_principle_card` — for `0 < a`, `b ≤ a`, `#{hit a, end b} = #{end 2a−b}` (the
  counting form of the bijection), and its finance reading `barrierDigital_knockIn_reflection`:
  under the symmetric tree, a cash-or-nothing up-and-in digital at terminal `b ≤ a` equals the
  vanilla digital at the reflected level.
* `binomial_upAndIn_reflection`, `binomial_upAndOut_reflection`, `binomial_upAndOut_eq`: under
  `coinFlipMeasure (1/2)`, the up-and-in price of a payoff `g` of the terminal position is
  `E[g(Sₙ); Sₙ ≥ a] + E[g(2a − Sₙ); Sₙ > a]`; the up-and-out price is the vanilla price less it.
* `binomial_maximal_distribution`: `P(max ≥ a) = 2P(Sₙ > a) + P(Sₙ = a)` as a measure.
* `binomial_maximal_distribution_card` — the running-maximum distribution
  `#{ω : max ≥ a} = 2·#{end > a} + #{end = a}` (`a > 0`), the discrete
  `P(max ≥ a) = 2P(S_n > a) + P(S_n = a)` — obtained by trichotomising the hit-set and
  reflecting the below-barrier endpoints onto the above-barrier ones.

## References

* [André (1887)][Andre1887]

## Tags

barrier option, reflection principle, running maximum, knock-in, André reflection, lattice paths,
MSC 91G20, MSC 60G50, JEL G13
-/

@[expose] public section

namespace MathFin

open Finset

variable {n : ℕ}

/-- **Counting form of André's reflection principle.** For a barrier `0 < a` and terminal
`b ≤ a`, the number of `n`-step ±1 paths that touch `a` and finish at `b` equals the number
that finish at `2a − b`. Immediate from `reflectionPrincipleEquivBelow`. -/
theorem reflection_principle_card (a b : ℤ) (ha : 0 < a) (hb : b ≤ a) :
    Nat.card {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n = b}
      = Nat.card {ω : Fin n → Bool // walkPos ω n = 2 * a - b} :=
  Nat.card_congr (reflectionPrincipleEquivBelow a b ha hb)

/-- **Barrier cash-or-nothing knock-in = vanilla digital at the reflected level** (symmetric
tree). Under the symmetric `q = 1/2` binomial measure (each path weight `2⁻ⁿ`), the up-and-in
digital paying `1` on `{touch a, finish b}` (with `b ≤ a`) has the same price as the vanilla
digital paying `1` on `{finish 2a − b}`. -/
theorem barrierDigital_knockIn_reflection (a b : ℤ) (ha : 0 < a) (hb : b ≤ a) :
    (Nat.card {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n = b} : ℝ) / 2 ^ n
      = (Nat.card {ω : Fin n → Bool // walkPos ω n = 2 * a - b} : ℝ) / 2 ^ n := by
  rw [reflection_principle_card a b ha hb]

/-- Reflection swaps below-barrier and above-barrier endpoints on the hit-set:
`{hit a, end < a} ≃ {hit a, end > a}` via reflection at the first hit. -/
noncomputable def reflectHitLtGt (a : ℤ) :
    {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n < a} ≃
    {ω : Fin n → Bool // HitsLevel a ω ∧ a < walkPos ω n} where
  toFun ω := ⟨reflectAtFirstHit a ω.1, by
    refine ⟨?_, ?_⟩
    · rw [reflectAtFirstHit, dite_eq_left ω.2.1]
      exact HitsLevel.reflectAfter_firstHit ω.1 a ω.2.1
    · have h := walkPos_reflectAtFirstHit_endpoint ω.1 a (walkPos ω.1 n) ω.2.1 rfl
      have := ω.2.2; rw [h]; linarith⟩
  invFun ω := ⟨reflectAtFirstHit a ω.1, by
    refine ⟨?_, ?_⟩
    · rw [reflectAtFirstHit, dite_eq_left ω.2.1]
      exact HitsLevel.reflectAfter_firstHit ω.1 a ω.2.1
    · have h := walkPos_reflectAtFirstHit_endpoint ω.1 a (walkPos ω.1 n) ω.2.1 rfl
      have := ω.2.2; rw [h]; linarith⟩
  left_inv ω := Subtype.ext (reflectAtFirstHit_involutive a ω.1)
  right_inv ω := Subtype.ext (reflectAtFirstHit_involutive a ω.1)

/-- Above a positive barrier the hit condition is automatic (discrete IVT):
`{hit a, end > a} ≃ {end > a}`. -/
noncomputable def hitAboveEquiv (a : ℤ) (ha : 0 < a) :
    {ω : Fin n → Bool // HitsLevel a ω ∧ a < walkPos ω n} ≃
    {ω : Fin n → Bool // a < walkPos ω n} where
  toFun ω := ⟨ω.1, ω.2.2⟩
  invFun ω := ⟨ω.1, HitsLevel_of_endpoint_gt (le_of_lt ha) ω.2, ω.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- At a positive barrier the hit condition is automatic: `{hit a, end = a} ≃ {end = a}`. -/
noncomputable def hitAtEquiv (a : ℤ) (ha : 0 < a) :
    {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n = a} ≃
    {ω : Fin n → Bool // walkPos ω n = a} where
  toFun ω := ⟨ω.1, ω.2.2⟩
  invFun ω := ⟨ω.1, HitsLevel_of_walkPos_endpoint_ge ω.1 a (le_of_lt ha) ω.2.ge, ω.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The binomial maximal-distribution identity** (running-maximum law). For a barrier
`0 < a`, the number of `n`-step ±1 paths whose running maximum reaches `a` (i.e. that hit `a`)
is `2·#{end > a} + #{end = a}` — the discrete `P(max ≥ a) = 2·P(S_n > a) + P(S_n = a)`.

Proof: trichotomise the hit-set by the terminal position. Paths ending `> a` or `= a` hit `a`
automatically (`hitAboveEquiv`, `hitAtEquiv`, discrete IVT), and reflection at the first hit
(`reflectHitLtGt`) bijects the below-barrier endpoints onto the above-barrier ones, so
`#{hit a, end < a} = #{end > a}`. -/
theorem binomial_maximal_distribution_card (a : ℤ) (ha : 0 < a) :
    Nat.card {ω : Fin n → Bool // HitsLevel a ω}
      = 2 * Nat.card {ω : Fin n → Bool // a < walkPos ω n}
        + Nat.card {ω : Fin n → Bool // walkPos ω n = a} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- The three hit-set slices, with the ≥-barrier slices' hit condition dissolved by IVT.
  have e1 : (univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω ∧ a < walkPos ω n)).card
      = (univ.filter (fun ω : Fin n → Bool ↦ a < walkPos ω n)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]; exact Fintype.card_congr
        (hitAboveEquiv a ha)
  have e2 : (univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω ∧ walkPos ω n = a)).card
      = (univ.filter (fun ω : Fin n → Bool ↦ walkPos ω n = a)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]; exact Fintype.card_congr (hitAtEquiv a ha)
  have e3 : (univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω ∧ walkPos ω n < a)).card
      = (univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω ∧ a < walkPos ω n)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]; exact Fintype.card_congr (reflectHitLtGt a)
  -- Trichotomy partition of the hit-set by the terminal position.
  have hunion : (univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω))
      = (univ.filter (fun ω ↦ HitsLevel a ω ∧ a < walkPos ω n))
        ∪ (univ.filter (fun ω ↦ HitsLevel a ω ∧ walkPos ω n = a))
        ∪ (univ.filter (fun ω ↦ HitsLevel a ω ∧ walkPos ω n < a)) := by
    ext ω
    simp only [mem_filter, mem_union, mem_univ, true_and]
    constructor
    · intro h
      rcases lt_trichotomy (walkPos ω n) a with h1 | h1 | h1
      · exact Or.inr ⟨h, h1⟩
      · exact Or.inl (Or.inr ⟨h, h1⟩)
      · exact Or.inl (Or.inl ⟨h, h1⟩)
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  have hd12 : Disjoint (univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω ∧ a < walkPos ω n))
      (univ.filter (fun ω ↦ HitsLevel a ω ∧ walkPos ω n = a)) :=
    disjoint_filter.2 (fun ω _ hp hq ↦ by omega)
  have hd3 : Disjoint ((univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω ∧ a < walkPos ω n))
      ∪ (univ.filter (fun ω ↦ HitsLevel a ω ∧ walkPos ω n = a)))
      (univ.filter (fun ω ↦ HitsLevel a ω ∧ walkPos ω n < a)) := by
    rw [disjoint_union_left]
    exact ⟨disjoint_filter.2 (fun ω _ hp hq ↦ by omega),
      disjoint_filter.2 (fun ω _ hp hq ↦ by omega)⟩
  rw [hunion, card_union_of_disjoint hd3, card_union_of_disjoint hd12, e3]
  simp only [e1, e2]
  ring

/-! ### Barrier prices under the symmetric tree

Prices are expectations under `coinFlipMeasure (1/2)`, the symmetric walk (every `n`-step path
has weight `2⁻ⁿ`), of a payoff of the first `n` flips (`flips n`). -/

section Prices

open MeasureTheory
open scoped NNReal

/-- Under the symmetric flip law the expectation of a function of the first `n` flips is the
average over the `2ⁿ` paths. -/
theorem integral_flips_symm (hq : (1 / 2 : ℝ≥0) ≤ 1) (F : (Fin n → Bool) → ℝ) :
    ∫ ω, F (flips n ω) ∂coinFlipMeasure (1 / 2) hq = (∑ x, F x) / 2 ^ n := by
  rw [integral_comp_flips, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have : (∏ i, if x i then ((1 / 2 : ℝ≥0) : ℝ) else 1 - ((1 / 2 : ℝ≥0) : ℝ))
      = (1 / 2) ^ n := by
    rw [← Finset.card_univ (α := Fin n), ← Finset.prod_const]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    cases x i <;> norm_num
  rw [this]; ring

/-- The measure-theoretic form of the average: the symmetric probability of an event of the first
`n` flips is the proportion of paths in it. -/
theorem measureReal_flips_symm (hq : (1 / 2 : ℝ≥0) ≤ 1) (A : Set (Fin n → Bool))
    [DecidablePred (· ∈ A)] :
    (coinFlipMeasure (1 / 2) hq).real {ω | flips n ω ∈ A}
      = (Finset.univ.filter (· ∈ A)).card / 2 ^ n := by
  have hm : MeasurableSet {ω : ℕ → Bool | flips n ω ∈ A} :=
    (measurable_flips n) (MeasurableSet.of_discrete (s := A))
  rw [← integral_indicator_one hm]
  have := integral_flips_symm (n := n) hq fun x ↦ if x ∈ A then 1 else 0
  simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
  rw [this, Finset.sum_boole]

/-- **The reflected sum.** For `0 < a`, summing `G` of the terminal position over the paths that
touch `a` gives the sum over paths ending at or above `a` plus the sum of `G (2a − ·)` over
paths ending above `a`: the below-barrier endpoints are reflected at the first hit. -/
theorem sum_hits_eq (a : ℤ) (ha : 0 < a) (G : ℤ → ℝ) :
    (∑ x : Fin n → Bool, if HitsLevel a x then G (walkPos x n) else 0)
      = (∑ x : Fin n → Bool, if a ≤ walkPos x n then G (walkPos x n) else 0)
        + ∑ x : Fin n → Bool, if a < walkPos x n then G (2 * a - walkPos x n) else 0 := by
  classical
  have h1 : ∀ x : Fin n → Bool, (if HitsLevel a x then G (walkPos x n) else 0)
      = (if a ≤ walkPos x n then G (walkPos x n) else 0)
        + (if HitsLevel a x ∧ walkPos x n < a then G (walkPos x n) else 0) := by
    intro x
    by_cases h : a ≤ walkPos x n
    · simp [h, HitsLevel_of_walkPos_endpoint_ge x a ha.le h]
    · have := not_le.1 h
      simp [h, this]
  rw [Finset.sum_congr rfl fun x _ ↦ h1 x, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (reflectAtFirstHit a) (reflectAtFirstHit a) ?_ ?_
    (fun x _ ↦ reflectAtFirstHit_involutive a x) (fun x _ ↦ reflectAtFirstHit_involutive a x) ?_
  · intro x hx
    simpa using (reflectHitLtGt a ⟨x, by simpa using hx⟩).2.2
  · intro y hy
    have hy : a < walkPos y n := by simpa using hy
    simpa using ((reflectHitLtGt a).symm ⟨y, HitsLevel_of_endpoint_gt ha.le hy, hy⟩).2
  · intro x hx
    have hx : HitsLevel a x := (Finset.mem_filter.1 hx).2.1
    rw [walkPos_reflectAtFirstHit_endpoint x a _ hx rfl]
    congr 1; ring

variable (hq : (1 / 2 : ℝ≥0) ≤ 1)

/-- **Binomial up-and-in price by reflection** (symmetric tree). For a barrier `0 < a` and any
payoff `g` of the terminal position, the up-and-in price (`g` of the terminal position `Sₙ`
on the paths that touch `a`) is the vanilla price on `{Sₙ ≥ a}` plus the vanilla price of the
reflected payoff `g (2a − ·)` on `{Sₙ > a}`:
`E[g(Sₙ); max ≥ a] = E[g(Sₙ); Sₙ ≥ a] + E[g(2a − Sₙ); Sₙ > a]`. -/
theorem binomial_upAndIn_reflection (a : ℤ) (ha : 0 < a) (g : ℤ → ℝ) :
    ∫ ω, (if HitsLevel a (flips n ω) then g (walkPos (flips n ω) n) else 0)
        ∂coinFlipMeasure (1 / 2) hq
      = (∫ ω, (if a ≤ walkPos (flips n ω) n then g (walkPos (flips n ω) n) else 0)
          ∂coinFlipMeasure (1 / 2) hq)
        + ∫ ω, (if a < walkPos (flips n ω) n then g (2 * a - walkPos (flips n ω) n) else 0)
          ∂coinFlipMeasure (1 / 2) hq := by
  classical
  simp only [integral_flips_symm hq (n := n)
    (fun x ↦ if HitsLevel a x then g (walkPos x n) else 0), integral_flips_symm hq (n := n)
    (fun x ↦ if a ≤ walkPos x n then g (walkPos x n) else 0), integral_flips_symm hq (n := n)
    (fun x ↦ if a < walkPos x n then g (2 * a - walkPos x n) else 0)]
  rw [sum_hits_eq a ha g, add_div]

/-- **Binomial up-and-out price by reflection**: the vanilla price less the up-and-in price,
`E[g(Sₙ); max < a] = E[g(Sₙ); Sₙ < a] − E[g(2a − Sₙ); Sₙ > a]`. -/
theorem binomial_upAndOut_reflection (a : ℤ) (ha : 0 < a) (g : ℤ → ℝ) :
    ∫ ω, (if HitsLevel a (flips n ω) then 0 else g (walkPos (flips n ω) n))
        ∂coinFlipMeasure (1 / 2) hq
      = (∫ ω, g (walkPos (flips n ω) n) ∂coinFlipMeasure (1 / 2) hq)
        - ∫ ω, (if HitsLevel a (flips n ω) then g (walkPos (flips n ω) n) else 0)
          ∂coinFlipMeasure (1 / 2) hq := by
  classical
  simp only [integral_flips_symm hq (n := n) (fun x ↦ g (walkPos x n)),
    integral_flips_symm hq (n := n) (fun x ↦ if HitsLevel a x then 0 else g (walkPos x n)),
    integral_flips_symm hq (n := n) (fun x ↦ if HitsLevel a x then g (walkPos x n) else 0),
    ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  split_ifs <;> simp

/-- **The up-and-out price in closed form**:
`E[g(Sₙ); max < a] = E[g(Sₙ); Sₙ < a] − E[g(2a − Sₙ); Sₙ > a]`. -/
theorem binomial_upAndOut_eq (a : ℤ) (ha : 0 < a) (g : ℤ → ℝ) :
    ∫ ω, (if HitsLevel a (flips n ω) then 0 else g (walkPos (flips n ω) n))
        ∂coinFlipMeasure (1 / 2) hq
      = (∫ ω, (if walkPos (flips n ω) n < a then g (walkPos (flips n ω) n) else 0)
          ∂coinFlipMeasure (1 / 2) hq)
        - ∫ ω, (if a < walkPos (flips n ω) n then g (2 * a - walkPos (flips n ω) n) else 0)
          ∂coinFlipMeasure (1 / 2) hq := by
  classical
  have hI : ∀ F : (Fin n → Bool) → ℝ, ∫ ω, F (flips n ω) ∂coinFlipMeasure (1 / 2) hq
      = (∑ x, F x) / 2 ^ n := integral_flips_symm hq
  rw [binomial_upAndOut_reflection hq a ha g, binomial_upAndIn_reflection hq a ha g,
    hI (fun x ↦ g (walkPos x n)), hI (fun x ↦ if a ≤ walkPos x n then g (walkPos x n) else 0),
    hI (fun x ↦ if walkPos x n < a then g (walkPos x n) else 0)]
  have : (∑ x : Fin n → Bool, g (walkPos x n))
      = (∑ x : Fin n → Bool, if a ≤ walkPos x n then g (walkPos x n) else 0)
        + ∑ x : Fin n → Bool, if walkPos x n < a then g (walkPos x n) else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases h : a ≤ walkPos x n
    · simp [h]
    · simp [h, not_le.1 h]
  rw [this]; ring

/-- **The running-maximum law, in probability** (symmetric tree, `0 < a`):
`P(max ≥ a) = 2 P(Sₙ > a) + P(Sₙ = a)`. -/
theorem binomial_maximal_distribution (a : ℤ) (ha : 0 < a) :
    (coinFlipMeasure (1 / 2) hq).real {ω | HitsLevel a (flips n ω)}
      = 2 * (coinFlipMeasure (1 / 2) hq).real {ω | a < walkPos (flips n ω) n}
        + (coinFlipMeasure (1 / 2) hq).real {ω | walkPos (flips n ω) n = a} := by
  classical
  have h1 := measureReal_flips_symm (n := n) hq {x | HitsLevel a x}
  have h2 := measureReal_flips_symm (n := n) hq {x | a < walkPos x n}
  have h3 := measureReal_flips_symm (n := n) hq {x | walkPos x n = a}
  have hc := binomial_maximal_distribution_card (n := n) a ha
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  simp only [Set.mem_setOf_eq] at h1 h2 h3 ⊢
  rw [h1, h2, h3]
  have : ((Finset.univ.filter fun x : Fin n → Bool ↦ HitsLevel a x).card : ℝ)
      = 2 * (Finset.univ.filter fun x : Fin n → Bool ↦ a < walkPos x n).card
        + (Finset.univ.filter fun x : Fin n → Bool ↦ walkPos x n = a).card := by
    exact_mod_cast hc
  rw [this]; ring

end Prices

end MathFin
