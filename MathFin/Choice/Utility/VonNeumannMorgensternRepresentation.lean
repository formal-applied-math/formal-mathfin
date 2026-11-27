/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Choice.Utility.VonNeumannMorgenstern
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic.Linarith

/-!
# The von Neumann–Morgenstern representation theorem

`Choice.Utility.VonNeumannMorgenstern` supplies the mixture algebra of lotteries, the expected
utility functional `expectedUtility` and the soundness half of the theorem: an expected-utility
preference `prefersEU` satisfies the axioms. This file proves the representation half: a
preference on the lotteries over a finite set of outcomes that is complete, transitive, satisfies
independence and is continuous is represented by expected utility, and the utility is unique up
to a positive affine map.

## Setup

A lottery over the finite outcome type `O` is a function `p : O → ℝ` with nonnegative values
summing to one (`IsLottery`; the point set of Mathlib's standard simplex). A preference is a
relation `R : (O → ℝ) → (O → ℝ) → Prop` read `R p q` for "`p` is weakly preferred to `q`", the
orientation of `prefersEU`; only its values on lotteries are constrained. `IsVNMPreference R`
bundles the four axioms in the textbook form, for lotteries `p q r`:

* completeness, `R p q ∨ R q p`, and transitivity;
* independence: `R p q ↔ R (mix α p r) (mix α q r)` for every weight `α ∈ (0, 1]`;
* continuity (Archimedean axiom): if `p` is strictly preferred to `q` and `q` to `r`, then
  `mix α p r` is strictly preferred to `q` and `q` to `mix β p r` for some `α, β ∈ (0, 1)`.

Strict preference `p ≻ q` is `¬ R q p`.

## The proof

The proof is the one of Herstein and Milnor, as in Föllmer–Schied.

1. A finite set of degenerate lotteries has a best and a worst element for a total preorder
   (`exists_forall_of_total_trans`), and by independence the set of lotteries at most as good as
   a given one is closed under mixing, so a best (resp. worst) degenerate lottery `b` (`w`) is
   best (worst) among all lotteries, since the lotteries are the convex hull of the degenerate
   ones (`mem_of_mix_closed`, `exists_best`, `exists_worst`).
2. If `w` is at least as good as `b` all lotteries are indifferent and `u = 0` works.
3. Otherwise `b ≻ w`, and `mix a b w` is strictly increasing in the weight `a`
   (`strict_mono`). For a lottery `p` the supremum `a` of the weights `t` with `p ≽ mix t b w` has
   `mix a b w ∼ p`: either strict inequality would, by continuity and the supremum property,
   put a point of the segment on the wrong side of `p` (`exists_indiff`).
4. The calibration `V p` of that indifference weight is affine in the mixture, by independence
   applied in both slots, and represents `R` by strict monotonicity; an affine function on
   lotteries is the expectation of its values at the degenerate ones, so `V = EU` for
   `u o = V (δ_o)`.

Uniqueness compares two representations on the lotteries `mix λ δ_max δ_min`, which are
indifferent to the degenerate lotteries `δ_o`.

## Main definitions

* `IsLottery`: a probability vector `p : O → ℝ`.
* `IsVNMPreference`: the four axioms for a preference `R`.
* `IsEURepresentation`: `R p q ↔ prefersEU Finset.univ u p q` on lotteries.

## Main results

* `vnm_representation`: a preference with the von Neumann–Morgenstern axioms has an
  expected-utility representation `u`, and the representations are exactly `a • u + b`,
  `a > 0`.
* `isVNMPreference_iff_exists_eu`: a preference satisfies the axioms if and only if it is
  represented by expected utility.
* `isVNMPreference_prefersEU`: the expected-utility preference satisfies the axioms in the form
  used here.
* `IsEURepresentation.exists_affine`: two representations of the same preference differ by a
  positive affine map.

## References

* [von Neumann and Morgenstern, *Theory of Games and Economic Behavior*][VonNeumannMorgenstern1944]
* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §2.2

## Tags

von Neumann-Morgenstern, expected utility, representation theorem, independence axiom,
Archimedean axiom, finite lotteries, utility uniqueness, MSC 91B16, MSC 91B06, JEL D81
-/

@[expose] public section

namespace MathFin

variable {O : Type*} [Fintype O]

/-- A **lottery** over the finite outcome type `O`: a probability vector. This is the point set
of Mathlib's standard simplex, kept as the bare predicate the mixture algebra (`mix`,
`expectedUtility`) is stated for. -/
def IsLottery (p : O → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- A mixture of lotteries is a lottery. -/
theorem isLottery_mix {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) {p q : O → ℝ}
    (hp : IsLottery p) (hq : IsLottery q) : IsLottery (mix α p q) :=
  ⟨mix_nonneg hα₀ hα₁ hp.1 hq.1, sum_mix Finset.univ α hp.2 hq.2⟩

/-- The degenerate lottery at an outcome is a lottery. -/
theorem isLottery_single [DecidableEq O] (o : O) : IsLottery (Pi.single o 1 : O → ℝ) :=
  ⟨fun i ↦ by rw [Pi.single_apply]; split_ifs <;> norm_num, by simp⟩

/-- The expected utility of a degenerate lottery is the utility of its outcome. -/
theorem expectedUtility_single [DecidableEq O] (u : O → ℝ) (o : O) :
    expectedUtility Finset.univ u (Pi.single o 1 : O → ℝ) = u o := by
  simp [expectedUtility, Pi.single_apply]

/-- **The von Neumann–Morgenstern axioms** for a preference `R` on the lotteries over `O`, where
`R p q` reads "`p` is weakly preferred to `q`" and strict preference `p ≻ q` is `¬ R q p`:
completeness, transitivity, independence at every weight in `(0, 1]` and continuity in the
textbook form (`p ≻ q ≻ r` puts `q` strictly between `mix α p r` and `mix β p r` for some weights
`α, β ∈ (0, 1)`). Only the values of `R` on lotteries are constrained. -/
structure IsVNMPreference (R : (O → ℝ) → (O → ℝ) → Prop) : Prop where
  /-- Completeness. -/
  total : ∀ {p q : O → ℝ}, IsLottery p → IsLottery q → R p q ∨ R q p
  /-- Transitivity. -/
  trans : ∀ {p q r : O → ℝ}, IsLottery p → IsLottery q → IsLottery r → R p q → R q r → R p r
  /-- Independence: mixing a common lottery into both sides, at a positive weight, neither creates
  nor destroys a preference. -/
  independence : ∀ {p q r : O → ℝ} {α : ℝ}, IsLottery p → IsLottery q → IsLottery r →
    0 < α → α ≤ 1 → (R p q ↔ R (mix α p r) (mix α q r))
  /-- Continuity (the Archimedean axiom). -/
  continuity : ∀ {p q r : O → ℝ}, IsLottery p → IsLottery q → IsLottery r → ¬ R q p → ¬ R r q →
    ∃ α β : ℝ, 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧ ¬ R q (mix α p r) ∧ ¬ R (mix β p r) q

/-- A preference `R` is **represented by expected utility** with utility `u` when on lotteries
`R p q` holds exactly when `prefersEU Finset.univ u p q`, i.e. `∑ q i * u i ≤ ∑ p i * u i`. -/
def IsEURepresentation (R : (O → ℝ) → (O → ℝ) → Prop) (u : O → ℝ) : Prop :=
  ∀ p q : O → ℝ, IsLottery p → IsLottery q → (R p q ↔ prefersEU Finset.univ u p q)

/-! ### Mixture identities -/

theorem mix_mix_right (β a : ℝ) (b w : O → ℝ) :
    mix β b (mix a b w) = mix (β + (1 - β) * a) b w := by
  funext i
  simp only [mix]
  ring

theorem mix_mix_mix (γ a c : ℝ) (b w : O → ℝ) :
    mix γ (mix a b w) (mix c b w) = mix (γ * a + (1 - γ) * c) b w := by
  funext i
  simp only [mix]
  ring

/-! ### The lotteries are generated by the degenerate ones -/

/-- A set of vectors closed under mixing and containing the degenerate lotteries contains every
lottery: the lotteries are the convex hull of the degenerate ones. -/
theorem mem_of_mix_closed [DecidableEq O] {S : Set (O → ℝ)}
    (hS : ∀ p ∈ S, ∀ q ∈ S, ∀ α : ℝ, 0 ≤ α → α ≤ 1 → mix α p q ∈ S)
    (hδ : ∀ o, (Pi.single o 1 : O → ℝ) ∈ S) {p : O → ℝ} (hp : IsLottery p) : p ∈ S := by
  have hconv : Convex ℝ S := fun x hx y hy a b ha hb hab ↦ by
    obtain rfl : b = 1 - a := by linarith
    have e : a • x + (1 - a) • y = mix a x y := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mix]
    rw [e]
    exact hS x hx y hy a ha (by linarith)
  have h := hconv.sum_mem (t := Finset.univ) (w := p) (z := fun i ↦ (Pi.single i 1 : O → ℝ))
    (fun i _ ↦ hp.1 i) hp.2 (fun i _ ↦ hδ i)
  rw [pi_eq_sum_univ' p]
  exact h

/-- In a finite nonempty set, a total transitive relation has a top element. -/
theorem exists_forall_of_total_trans {α : Type*} (r : α → α → Prop) (htot : ∀ a b, r a b ∨ r b a)
    (htr : ∀ a b c, r a b → r b c → r a c) (s : Finset α) (hs : s.Nonempty) :
    ∃ m ∈ s, ∀ x ∈ s, r m x := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    exact ⟨a, by simp, fun x hx ↦ by rw [Finset.mem_singleton.1 hx]; exact (htot a a).elim id id⟩
  | @cons a s ha hs' ih =>
    obtain ⟨m, hm, hmx⟩ := ih
    rcases htot a m with h | h
    · refine ⟨a, Finset.mem_cons_self a s, fun x hx ↦ ?_⟩
      rcases Finset.mem_cons.1 hx with rfl | hx
      · exact (htot _ _).elim id id
      · exact htr _ _ _ h (hmx x hx)
    · refine ⟨m, Finset.mem_cons.2 (Or.inr hm), fun x hx ↦ ?_⟩
      rcases Finset.mem_cons.1 hx with rfl | hx
      · exact h
      · exact hmx x hx

namespace IsVNMPreference

variable {R : (O → ℝ) → (O → ℝ) → Prop}

theorem refl (hR : IsVNMPreference R) {p : O → ℝ} (hp : IsLottery p) : R p p :=
  (hR.total hp hp).elim id id

/-- Independence with the common lottery in the first slot, at a weight in `[0, 1)`. -/
theorem independence_right (hR : IsVNMPreference R) {q q' r : O → ℝ} {γ : ℝ}
    (hq : IsLottery q) (hq' : IsLottery q') (hr : IsLottery r) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1) :
    R q q' ↔ R (mix γ r q) (mix γ r q') := by
  have h := hR.independence hq hq' hr (sub_pos.2 hγ₁) (by linarith : 1 - γ ≤ 1)
  rwa [← mix_comm γ r q, ← mix_comm γ r q'] at h

/-- Strict independence: `p ≻ q` gives `mix α p r ≻ mix α q r`. -/
theorem strict_independence (hR : IsVNMPreference R) {p q r : O → ℝ} {α : ℝ}
    (hp : IsLottery p) (hq : IsLottery q) (hr : IsLottery r) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (h : ¬ R q p) : ¬ R (mix α q r) (mix α p r) :=
  fun h' ↦ h ((hR.independence hq hp hr hα₀ hα₁).2 h')

/-- If `p ≻ q` then every positive mixture of `p` with `q` is strictly better than `q`. -/
theorem strict_mix_left (hR : IsVNMPreference R) {p q : O → ℝ} (hp : IsLottery p)
    (hq : IsLottery q) {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) (h : ¬ R q p) :
    ¬ R q (mix α p q) := by
  have := hR.strict_independence hp hq hq hα₀ hα₁ h
  rwa [mix_self] at this

/-- If `x ≻ q` then `x` is strictly better than every proper mixture of `x` with `q`. -/
theorem strict_mix_right (hR : IsVNMPreference R) {x q : O → ℝ} (hx : IsLottery x)
    (hq : IsLottery q) {γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1) (h : ¬ R q x) :
    ¬ R (mix γ x q) x := by
  have := hR.strict_independence hx hq hx (sub_pos.2 hγ₁) (by linarith : 1 - γ ≤ 1) h
  rwa [mix_self, ← mix_comm γ x q] at this

/-- If `p ≻ q`, the mixture `mix α p q` is strictly increasing in the weight `α ∈ [0, 1]`. -/
theorem strict_mono (hR : IsVNMPreference R) {p q : O → ℝ} (hp : IsLottery p)
    (hq : IsLottery q) (h : ¬ R q p) {β α : ℝ} (hβ : 0 ≤ β) (hβα : β < α) (hα : α ≤ 1) :
    ¬ R (mix β p q) (mix α p q) := by
  have hα₀ : 0 < α := hβ.trans_lt hβα
  have hx := isLottery_mix hα₀.le hα hp hq
  have h1 := hR.strict_mix_left hp hq hα₀ hα h
  have h2 := hR.strict_mix_right hx hq (div_nonneg hβ hα₀.le) ((div_lt_one₀ hα₀).2 hβα) h1
  rwa [mix_compound, div_mul_cancel₀ β hα₀.ne'] at h2

/-- A lottery weakly below two lotteries is weakly below their mixtures. -/
theorem best_mix (hR : IsVNMPreference R) {x p q : O → ℝ} (hx : IsLottery x)
    (hp : IsLottery p) (hq : IsLottery q) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hxp : R x p) (hxq : R x q) : R x (mix α p q) := by
  rcases hα₀.eq_or_lt with rfl | hα₀'
  · rwa [mix_zero]
  rcases hα₁.eq_or_lt with rfl | hα₁'
  · rwa [mix_one]
  have h1 : R (mix α x q) (mix α p q) := (hR.independence hx hp hq hα₀' hα₁).1 hxp
  have h2 : R x (mix α x q) := by
    have := (hR.independence_right hx hq hx hα₀ hα₁').1 hxq
    rwa [mix_self] at this
  exact hR.trans hx (isLottery_mix hα₀ hα₁ hx hq) (isLottery_mix hα₀ hα₁ hp hq) h2 h1

/-- A lottery weakly above two lotteries is weakly above their mixtures. -/
theorem worst_mix (hR : IsVNMPreference R) {x p q : O → ℝ} (hx : IsLottery x)
    (hp : IsLottery p) (hq : IsLottery q) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hpx : R p x) (hqx : R q x) : R (mix α p q) x := by
  rcases hα₀.eq_or_lt with rfl | hα₀'
  · rwa [mix_zero]
  rcases hα₁.eq_or_lt with rfl | hα₁'
  · rwa [mix_one]
  have h1 : R (mix α p q) (mix α x q) := (hR.independence hp hx hq hα₀' hα₁).1 hpx
  have h2 : R (mix α x q) x := by
    have := (hR.independence_right hq hx hx hα₀ hα₁').1 hqx
    rwa [mix_self] at this
  exact hR.trans (isLottery_mix hα₀ hα₁ hp hq) (isLottery_mix hα₀ hα₁ hx hq) hx h1 h2

/-- Some lottery is weakly preferred to every lottery. -/
theorem exists_best [DecidableEq O] [Nonempty O] (hR : IsVNMPreference R) :
    ∃ b, IsLottery b ∧ ∀ p, IsLottery p → R b p := by
  obtain ⟨o, -, ho⟩ := exists_forall_of_total_trans
    (fun a b : O ↦ R (Pi.single a 1 : O → ℝ) (Pi.single b 1))
    (fun a b ↦ hR.total (isLottery_single a) (isLottery_single b))
    (fun a b c ↦ hR.trans (isLottery_single a) (isLottery_single b) (isLottery_single c))
    Finset.univ Finset.univ_nonempty
  have hS : ∀ p ∈ {p : O → ℝ | IsLottery p ∧ R (Pi.single o 1 : O → ℝ) p},
      ∀ q ∈ {p : O → ℝ | IsLottery p ∧ R (Pi.single o 1 : O → ℝ) p},
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        mix α p q ∈ {p : O → ℝ | IsLottery p ∧ R (Pi.single o 1 : O → ℝ) p} := by
    rintro p ⟨hp, hop⟩ q ⟨hq, hoq⟩ α h0 h1
    exact ⟨isLottery_mix h0 h1 hp hq, hR.best_mix (isLottery_single o) hp hq h0 h1 hop hoq⟩
  have hδ : ∀ o', (Pi.single o' 1 : O → ℝ) ∈
      {p : O → ℝ | IsLottery p ∧ R (Pi.single o 1 : O → ℝ) p} :=
    fun o' ↦ ⟨isLottery_single o', ho o' (Finset.mem_univ _)⟩
  exact ⟨Pi.single o 1, isLottery_single o, fun p hp ↦ (mem_of_mix_closed hS hδ hp).2⟩

/-- Some lottery is weakly worse than every lottery. -/
theorem exists_worst [DecidableEq O] [Nonempty O] (hR : IsVNMPreference R) :
    ∃ w, IsLottery w ∧ ∀ p, IsLottery p → R p w := by
  obtain ⟨o, -, ho⟩ := exists_forall_of_total_trans
    (fun a b : O ↦ R (Pi.single b 1 : O → ℝ) (Pi.single a 1))
    (fun a b ↦ hR.total (isLottery_single b) (isLottery_single a))
    (fun a b c hab hbc ↦ hR.trans (isLottery_single c) (isLottery_single b)
      (isLottery_single a) hbc hab)
    Finset.univ Finset.univ_nonempty
  have hS : ∀ p ∈ {p : O → ℝ | IsLottery p ∧ R p (Pi.single o 1 : O → ℝ)},
      ∀ q ∈ {p : O → ℝ | IsLottery p ∧ R p (Pi.single o 1 : O → ℝ)},
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        mix α p q ∈ {p : O → ℝ | IsLottery p ∧ R p (Pi.single o 1 : O → ℝ)} := by
    rintro p ⟨hp, hpo⟩ q ⟨hq, hqo⟩ α h0 h1
    exact ⟨isLottery_mix h0 h1 hp hq, hR.worst_mix (isLottery_single o) hp hq h0 h1 hpo hqo⟩
  have hδ : ∀ o', (Pi.single o' 1 : O → ℝ) ∈
      {p : O → ℝ | IsLottery p ∧ R p (Pi.single o 1 : O → ℝ)} :=
    fun o' ↦ ⟨isLottery_single o', ho o' (Finset.mem_univ _)⟩
  exact ⟨Pi.single o 1, isLottery_single o, fun p hp ↦ (mem_of_mix_closed hS hδ hp).2⟩

/-! ### Calibration against a best and a worst lottery -/

/-- For `b ≻ w` the better the weight on `b`, the better the mixture (weak form). -/
theorem rel_mix_weight (hR : IsVNMPreference R) {b w : O → ℝ} (hb : IsLottery b)
    (hw : IsLottery w) (hbw : ¬ R w b) {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ 1) :
    R (mix s b w) (mix t b w) := by
  rcases hts.eq_or_lt with rfl | hlt
  · exact hR.refl (isLottery_mix ht hs hb hw)
  · exact (hR.total (isLottery_mix (ht.trans hts) hs hb hw)
      (isLottery_mix ht (hts.trans hs) hb hw)).resolve_right (hR.strict_mono hb hw hbw ht hlt hs)

/-- For `b ≻ w`, `mix a b w` weakly preferred to `mix a' b w` forces `a' ≤ a`. -/
theorem le_of_rel_mix_weight (hR : IsVNMPreference R) {b w : O → ℝ} (hb : IsLottery b)
    (hw : IsLottery w) (hbw : ¬ R w b) {a a' : ℝ} (ha : 0 ≤ a) (ha' : a' ≤ 1)
    (h : R (mix a b w) (mix a' b w)) : a' ≤ a := by
  by_contra hlt
  exact hR.strict_mono hb hw hbw ha (not_le.1 hlt) ha' h

/-- **Calibration.** If `b` is a best and `w` a worst lottery with `b ≻ w`, every lottery is
indifferent to some mixture `mix a b w`. The weight is the supremum of the weights `t` with
`p ≽ mix t b w`; continuity excludes both strict inequalities at the supremum. -/
theorem exists_indiff (hR : IsVNMPreference R) {b w p : O → ℝ} (hb : IsLottery b)
    (hw : IsLottery w) (hp : IsLottery p) (hbest : ∀ q, IsLottery q → R b q)
    (hworst : ∀ q, IsLottery q → R q w) (hbw : ¬ R w b) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ R (mix a b w) p ∧ R p (mix a b w) := by
  by_cases hpw : R w p
  · exact ⟨0, le_rfl, zero_le_one, by rw [mix_zero]; exact ⟨hpw, hworst p hp⟩⟩
  by_cases hpb : R p b
  · exact ⟨1, zero_le_one, le_rfl, by rw [mix_one]; exact ⟨hbest p hp, hpb⟩⟩
  obtain ⟨T, hT⟩ : ∃ T : Set ℝ, ∀ t, t ∈ T ↔ 0 ≤ t ∧ t ≤ 1 ∧ R p (mix t b w) :=
    ⟨{t | 0 ≤ t ∧ t ≤ 1 ∧ R p (mix t b w)}, fun _ ↦ Iff.rfl⟩
  have hT0 : (0 : ℝ) ∈ T :=
    (hT 0).2 ⟨le_rfl, zero_le_one, by rw [mix_zero]; exact hworst p hp⟩
  have hbdd : BddAbove T := ⟨1, fun t ht ↦ ((hT t).1 ht).2.1⟩
  obtain ⟨a, ha0, ha1, hub, hlub⟩ : ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ (∀ t ∈ T, t ≤ a) ∧
      ∀ c < a, ∃ t ∈ T, c < t :=
    ⟨sSup T, le_csSup hbdd hT0, csSup_le ⟨0, hT0⟩ fun t ht ↦ ((hT t).1 ht).2.1,
      fun t ht ↦ le_csSup hbdd ht, fun c hc ↦ exists_lt_of_lt_csSup ⟨0, hT0⟩ hc⟩
  have hx := isLottery_mix ha0 ha1 hb hw
  refine ⟨a, ha0, ha1, ?_, ?_⟩
  · -- `p ≻ mix a b w` is impossible: the supremum would not be an upper bound
    by_contra hnot
    have ha1' : a < 1 := by
      rcases ha1.eq_or_lt with rfl | h
      · rw [mix_one] at hnot
        exact (hnot (hbest p hp)).elim
      · exact h
    obtain ⟨_, β, _, _, hβ0, hβ1, _, hβ⟩ := hR.continuity hb hp hx hpb hnot
    have hy : IsLottery (mix β b (mix a b w)) := isLottery_mix hβ0.le hβ1.le hb hx
    have hRy : R p (mix β b (mix a b w)) := (hR.total hp hy).resolve_right hβ
    rw [mix_mix_right] at hRy
    have h1β : 0 ≤ 1 - β := by linarith
    have hm := mul_nonneg h1β ha0
    have hm2 := mul_le_mul_of_nonneg_left ha1 h1β
    have hmem : β + (1 - β) * a ∈ T := (hT _).2 ⟨by linarith, by linarith, hRy⟩
    have := hub _ hmem
    nlinarith [mul_pos hβ0 (sub_pos.2 ha1')]
  · -- `mix a b w ≻ p` is impossible: weights below `a` are all in `T`
    by_contra hnot
    have ha0' : 0 < a := by
      rcases ha0.eq_or_lt with h | h
      · rw [← h, mix_zero] at hnot
        exact (hnot (hworst p hp)).elim
      · exact h
    obtain ⟨α', _, hα0, hα1, _, _, hα, _⟩ := hR.continuity hx hp hw hnot hpw
    rw [mix_compound] at hα
    have hlt : α' * a < a := by nlinarith [mul_pos (sub_pos.2 hα1) ha0']
    obtain ⟨s, hs, hts⟩ := hlub (α' * a) hlt
    obtain ⟨hs0, hs1, hps⟩ := (hT s).1 hs
    have ht0 : 0 ≤ α' * a := mul_nonneg hα0.le ha0
    exact hα (hR.trans hp (isLottery_mix hs0 hs1 hb hw)
      (isLottery_mix ht0 (hlt.le.trans ha1) hb hw) hps
      (hR.rel_mix_weight hb hw hbw ht0 hts.le hs1))

/-- **The representation theorem** (existence). -/
theorem exists_representation (hR : IsVNMPreference R) :
    ∃ u : O → ℝ, IsEURepresentation R u := by
  classical
  rcases isEmpty_or_nonempty O with hO | hO
  · exact ⟨0, fun p _ hp _ ↦ absurd hp.2 (by simp)⟩
  obtain ⟨b, hb, hbest⟩ := hR.exists_best
  obtain ⟨w, hw, hworst⟩ := hR.exists_worst
  by_cases hbw : R w b
  · -- everything is indifferent
    refine ⟨0, fun p q hp hq ↦ ⟨fun _ ↦ by simp [prefersEU, expectedUtility], fun _ ↦ ?_⟩⟩
    exact hR.trans hp hw hq (hworst p hp) (hR.trans hw hb hq hbw (hbest q hq))
  have hcal : ∀ p, IsLottery p → ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ R (mix a b w) p ∧ R p (mix a b w) :=
    fun p hp ↦ hR.exists_indiff hb hw hp hbest hworst hbw
  choose! V hV0 hV1 hV2 hV3 using hcal
  -- the calibration is affine in the mixture
  have hVaff : ∀ p q, IsLottery p → IsLottery q → ∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 →
      V (mix γ p q) = γ * V p + (1 - γ) * V q := by
    intro p q hp hq γ hγ0 hγ1
    rcases hγ0.eq_or_lt with rfl | hγ0'
    · rw [mix_zero]
      ring
    rcases hγ1.eq_or_lt with rfl | hγ1'
    · rw [mix_one]
      ring
    have hxp := isLottery_mix (hV0 p hp) (hV1 p hp) hb hw
    have hxq := isLottery_mix (hV0 q hq) (hV1 q hq) hb hw
    have hm := isLottery_mix hγ0 hγ1 hp hq
    have h1γ : 0 ≤ 1 - γ := by linarith
    have hc0 : 0 ≤ γ * V p + (1 - γ) * V q :=
      add_nonneg (mul_nonneg hγ0 (hV0 p hp)) (mul_nonneg h1γ (hV0 q hq))
    have hc1 : γ * V p + (1 - γ) * V q ≤ 1 := by
      have := mul_le_mul_of_nonneg_left (hV1 p hp) hγ0
      have := mul_le_mul_of_nonneg_left (hV1 q hq) h1γ
      linarith
    have hz := isLottery_mix hc0 hc1 hb hw
    have e := mix_mix_mix γ (V p) (V q) b w
    have hmid := isLottery_mix hγ0 hγ1 hxp hq
    have hmid' := isLottery_mix hγ0 hγ1 hxp hxq
    have hup : R (mix γ p q) (mix (γ * V p + (1 - γ) * V q) b w) := by
      rw [← e]
      exact hR.trans hm hmid hmid'
        ((hR.independence hp hxp hq hγ0' hγ1).1 (hV3 p hp))
        ((hR.independence_right hq hxq hxp hγ0 hγ1').1 (hV3 q hq))
    have hlow : R (mix (γ * V p + (1 - γ) * V q) b w) (mix γ p q) := by
      rw [← e]
      exact hR.trans hmid' hmid hm
        ((hR.independence_right hxq hq hxp hγ0 hγ1').1 (hV2 q hq))
        ((hR.independence hxp hp hq hγ0' hγ1).1 (hV2 p hp))
    have hVx := isLottery_mix (hV0 (mix γ p q) hm) (hV1 (mix γ p q) hm) hb hw
    exact le_antisymm
      (hR.le_of_rel_mix_weight hb hw hbw hc0 (hV1 _ hm)
        (hR.trans hz hm hVx hlow (hV3 _ hm)))
      (hR.le_of_rel_mix_weight hb hw hbw (hV0 _ hm) hc1
        (hR.trans hVx hm hz (hV2 _ hm) hup))
  -- the calibration represents the preference
  have hrep : ∀ p q, IsLottery p → IsLottery q → (R p q ↔ V q ≤ V p) := by
    intro p q hp hq
    have hxp := isLottery_mix (hV0 p hp) (hV1 p hp) hb hw
    have hxq := isLottery_mix (hV0 q hq) (hV1 q hq) hb hw
    constructor
    · intro h
      exact hR.le_of_rel_mix_weight hb hw hbw (hV0 p hp) (hV1 q hq)
        (hR.trans hxp hp hxq (hV2 p hp) (hR.trans hp hq hxq h (hV3 q hq)))
    · intro h
      have := hR.rel_mix_weight hb hw hbw (hV0 q hq) h (hV1 p hp)
      exact hR.trans hp hxp hq (hV3 p hp) (hR.trans hxp hxq hq this (hV2 q hq))
  -- an affine function on lotteries is the expectation of its values at the degenerate ones
  have hVeu : ∀ p, IsLottery p →
      V p = expectedUtility Finset.univ (fun o ↦ V (Pi.single o 1)) p := by
    intro p hp
    have hS : ∀ p ∈ {p : O → ℝ | IsLottery p ∧
          V p = expectedUtility Finset.univ (fun o ↦ V (Pi.single o 1)) p},
        ∀ q ∈ {p : O → ℝ | IsLottery p ∧
          V p = expectedUtility Finset.univ (fun o ↦ V (Pi.single o 1)) p},
        ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
          mix α p q ∈ {p : O → ℝ | IsLottery p ∧
            V p = expectedUtility Finset.univ (fun o ↦ V (Pi.single o 1)) p} := by
      rintro p ⟨hp, hVp⟩ q ⟨hq, hVq⟩ α h0 h1
      exact ⟨isLottery_mix h0 h1 hp hq,
        by rw [hVaff p q hp hq α h0 h1, expectedUtility_mix, hVp, hVq]⟩
    have hδ : ∀ o, (Pi.single o 1 : O → ℝ) ∈ {p : O → ℝ | IsLottery p ∧
          V p = expectedUtility Finset.univ (fun o ↦ V (Pi.single o 1)) p} :=
      fun o ↦ ⟨isLottery_single o, by rw [expectedUtility_single]⟩
    exact (mem_of_mix_closed hS hδ hp).2
  refine ⟨fun o ↦ V (Pi.single o 1), fun p q hp hq ↦ ?_⟩
  have := hrep p q hp hq
  rw [hVeu p hp, hVeu q hq] at this
  exact this

end IsVNMPreference

/-! ### The converse and the uniqueness -/

/-- **Expected-utility preferences satisfy the axioms**: a preference represented by expected
utility is complete, transitive, independent and continuous. -/
theorem IsEURepresentation.isVNMPreference {R : (O → ℝ) → (O → ℝ) → Prop} {u : O → ℝ}
    (hu : IsEURepresentation R u) : IsVNMPreference R where
  total := fun {p q} hp hq ↦
    (prefersEU_total Finset.univ u p q).imp (hu p q hp hq).2 (hu q p hq hp).2
  trans := fun {p q r} hp hq hr hpq hqr ↦
    (hu p r hp hr).2 (prefersEU_trans Finset.univ u ((hu p q hp hq).1 hpq) ((hu q r hq hr).1 hqr))
  independence := by
    intro p q r α hp hq hr hα₀ hα₁
    rw [hu p q hp hq, hu _ _ (isLottery_mix hα₀.le hα₁ hp hr) (isLottery_mix hα₀.le hα₁ hq hr)]
    simp only [prefersEU, expectedUtility_mix, add_le_add_iff_right,
      mul_le_mul_iff_of_pos_left hα₀]
  continuity := by
    intro p q r hp hq hr h1 h2
    have h1' : expectedUtility Finset.univ u q < expectedUtility Finset.univ u p :=
      not_le.1 ((hu q p hq hp).not.1 h1)
    have h2' : expectedUtility Finset.univ u r < expectedUtility Finset.univ u q :=
      not_le.1 ((hu r q hr hq).not.1 h2)
    obtain ⟨a, ha0, ha1, ha⟩ := exists_mix_weight h1' h2'
    have hPR : 0 < expectedUtility Finset.univ u p - expectedUtility Finset.univ u r := by
      linarith
    refine ⟨(1 + a) / 2, a / 2, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
    · refine (hu q _ hq (isLottery_mix (by linarith) (by linarith) hp hr)).not.2
        (not_le.2 ?_)
      rw [expectedUtility_mix]
      nlinarith [mul_pos (sub_pos.2 ha1) hPR]
    · refine (hu _ q (isLottery_mix (by linarith) (by linarith) hp hr) hq).not.2
        (not_le.2 ?_)
      rw [expectedUtility_mix]
      nlinarith [mul_pos ha0 hPR]

/-- The expected-utility preference `prefersEU` satisfies the axioms in the form used here. -/
theorem isVNMPreference_prefersEU (u : O → ℝ) :
    IsVNMPreference (prefersEU (Finset.univ : Finset O) u) :=
  IsEURepresentation.isVNMPreference (fun _ _ _ _ ↦ Iff.rfl)

/-- **Uniqueness up to a positive affine map**: two expected-utility representations of the same
preference differ by `v = a • u + b` with `a > 0`. If `u` is constant all lotteries are
indifferent and `v` is constant too; otherwise the degenerate lotteries at a best and a worst
outcome of `u` calibrate `a` and `b`, every `δ_o` being indifferent to a mixture of these two. -/
theorem IsEURepresentation.exists_affine {R : (O → ℝ) → (O → ℝ) → Prop} {u v : O → ℝ}
    (hu : IsEURepresentation R u) (hv : IsEURepresentation R v) :
    ∃ a b : ℝ, 0 < a ∧ ∀ o, v o = a * u o + b := by
  classical
  rcases isEmpty_or_nonempty O with hO | hO
  · exact ⟨1, 0, one_pos, fun o ↦ (IsEmpty.false o).elim⟩
  have hiff : ∀ p q, IsLottery p → IsLottery q →
      (expectedUtility Finset.univ u q ≤ expectedUtility Finset.univ u p ↔
        expectedUtility Finset.univ v q ≤ expectedUtility Finset.univ v p) :=
    fun p q hp hq ↦ (hu p q hp hq).symm.trans (hv p q hp hq)
  have hd : ∀ o o', (u o' ≤ u o ↔ v o' ≤ v o) := fun o o' ↦ by
    have := hiff (Pi.single o 1) (Pi.single o' 1) (isLottery_single o) (isLottery_single o')
    simpa only [expectedUtility_single] using this
  have heq : ∀ p q, IsLottery p → IsLottery q →
      expectedUtility Finset.univ u p = expectedUtility Finset.univ u q →
      expectedUtility Finset.univ v p = expectedUtility Finset.univ v q :=
    fun p q hp hq h ↦ le_antisymm ((hiff q p hq hp).1 h.le) ((hiff p q hp hq).1 h.ge)
  obtain ⟨imax, hmax⟩ := Finite.exists_max u
  obtain ⟨imin, hmin⟩ := Finite.exists_min u
  by_cases hconst : u imax = u imin
  · refine ⟨1, v imax - u imax, one_pos, fun o ↦ ?_⟩
    have huo : u o = u imax := le_antisymm (hmax o) (hconst.le.trans (hmin o))
    have hvo : v o = v imax :=
      le_antisymm ((hd imax o).1 (hmax o)) ((hd o imax).1 (le_of_eq huo.symm))
    rw [hvo, huo]
    ring
  · have hlt : u imin < u imax := lt_of_le_of_ne (hmin imax) (Ne.symm hconst)
    have hDpos : 0 < u imax - u imin := sub_pos.2 hlt
    have hvlt : v imin < v imax := by
      by_contra hcon
      exact absurd ((hd imin imax).2 (not_lt.1 hcon)) (not_le.2 hlt)
    obtain ⟨a, ha_pos, ha⟩ : ∃ a : ℝ, 0 < a ∧ a * (u imax - u imin) = v imax - v imin :=
      ⟨(v imax - v imin) / (u imax - u imin), div_pos (sub_pos.2 hvlt) hDpos,
        div_mul_cancel₀ _ hDpos.ne'⟩
    refine ⟨a, v imin - a * u imin, ha_pos, fun o ↦ ?_⟩
    obtain ⟨l, hl0, hl1, hl⟩ : ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ l * (u imax - u imin) = u o - u imin :=
      ⟨(u o - u imin) / (u imax - u imin), div_nonneg (sub_nonneg.2 (hmin o)) hDpos.le,
        (div_le_one₀ hDpos).2 (by linarith [hmax o]), div_mul_cancel₀ _ hDpos.ne'⟩
    have hm := isLottery_mix hl0 hl1 (isLottery_single imax) (isLottery_single imin)
    have hEu : expectedUtility Finset.univ u (mix l (Pi.single imax 1) (Pi.single imin 1))
        = expectedUtility Finset.univ u (Pi.single o 1 : O → ℝ) := by
      simp only [expectedUtility_mix, expectedUtility_single]
      linear_combination hl
    have hEv := heq _ _ hm (isLottery_single o) hEu
    simp only [expectedUtility_mix, expectedUtility_single] at hEv
    rw [← hEv, show u o = l * (u imax - u imin) + u imin by linarith]
    linear_combination (-l) * ha

/-- A positive affine transformation of a representing utility is again a representation. -/
theorem IsEURepresentation.affine {R : (O → ℝ) → (O → ℝ) → Prop} {u : O → ℝ}
    (hu : IsEURepresentation R u) {a : ℝ} (b : ℝ) (ha : 0 < a) :
    IsEURepresentation R (fun o ↦ a * u o + b) :=
  fun p q hp hq ↦
    (hu p q hp hq).trans (prefersEU_affine_invariant Finset.univ u (b := b) ha hp.2 hq.2).symm

/-- **The von Neumann–Morgenstern representation theorem.** A preference on the lotteries over a
finite set of outcomes that is complete, transitive, independent and continuous
(`IsVNMPreference`) is represented by expected utility: there is `u : O → ℝ` with
`R p q ↔ ∑ q i * u i ≤ ∑ p i * u i` on lotteries, and the utilities representing `R` are exactly
the positive affine transformations `a * u + b`, `a > 0`, of `u`. -/
theorem vnm_representation {R : (O → ℝ) → (O → ℝ) → Prop} (hR : IsVNMPreference R) :
    ∃ u : O → ℝ, IsEURepresentation R u ∧
      ∀ v : O → ℝ, IsEURepresentation R v ↔ ∃ a b : ℝ, 0 < a ∧ ∀ o, v o = a * u o + b := by
  obtain ⟨u, hu⟩ := hR.exists_representation
  refine ⟨u, hu, fun v ↦ ⟨fun hv ↦ hu.exists_affine hv, ?_⟩⟩
  rintro ⟨a, b, ha, hv⟩
  obtain rfl : v = fun o ↦ a * u o + b := funext hv
  exact hu.affine b ha

/-- A preference satisfies the von Neumann–Morgenstern axioms if and only if it is represented by
expected utility. -/
theorem isVNMPreference_iff_exists_eu {R : (O → ℝ) → (O → ℝ) → Prop} :
    IsVNMPreference R ↔ ∃ u : O → ℝ, IsEURepresentation R u :=
  ⟨fun hR ↦ hR.exists_representation, fun ⟨_, hu⟩ ↦ hu.isVNMPreference⟩

end MathFin
