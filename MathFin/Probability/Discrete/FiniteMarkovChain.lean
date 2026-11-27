/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Discrete.MarkovPathSpace
public import MathFin.Probability.Analysis.StdSimplexMix
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.NumberTheory.FrobeniusNumber
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Finite Markov chains: the stationary distribution and the convergence theorem

The one-step law of a Markov chain on a finite state space `S` is a row-stochastic matrix
`P : Matrix S S ℝ` (Mathlib's `Matrix.rowStochastic`), and `(P ^ n) i j` is the `n`-step transition
probability. For the chain with one-step laws `K : S → PMF S`, whose law on trajectories is
`chainLaw K i` (`MarkovPathSpace.lean`), the matrix is `transitionMatrix K`, and
`chainLaw_visit_toReal_eq_pow` identifies `(P ^ n) i j` with `ℙ_i(X_n = j)`. This file proves the
two classical results on the long-run behaviour of such a chain
(Saporito, ch. 1, §1.4) from first principles, for every row-stochastic matrix (they are linear
algebra), and states them for the chain as one-line corollaries:

* an irreducible chain has at most one stationary distribution, and at least one (so exactly one);
* an irreducible aperiodic chain converges: `(P ^ n) i j → π j` for the stationary distribution `π`.

The proofs are elementary. Uniqueness is a maximum-principle argument: the positive part of the
difference of two stationary distributions is again a stationary vector, hence strictly positive
or zero, and the positive and negative parts cannot both be strictly positive. Convergence is
Doeblin's contraction: if every entry of `P ^ m` is at least `ε > 0`, the spread of any column of
`P ^ n` shrinks by the factor `1 - |S| ε` every `m` steps, so each column converges and the limits
do not depend on the row. Irreducible and aperiodic gives some power with all entries positive by
Schur's theorem on additive semigroups of `ℕ` (`Nat.exists_mem_closure_of_ge`). Existence of a
stationary distribution for an irreducible chain comes from the convergence theorem applied to
the lazy chain `(I + P) / 2`, which has the same stationary vectors and is primitive.

## Main definitions

* `MathFin.FiniteMarkov.IsStationary`: `π`, a point of Mathlib's standard simplex
  `Convexity.StdSimplex ℝ S` (a probability vector), satisfies `π ᵥ* P = π`.
* `MathFin.FiniteMarkov.IsIrreducible`: every state reaches every state, `0 < (P ^ n) i j` for
  some `n`; for a chain, `isIrreducible_transitionMatrix_iff` says this is `0 < ℙ_i(X_n = j)` for
  some `n`.
* `MathFin.FiniteMarkov.IsAperiodic`: the only natural number dividing every return time
  `n ≥ 1` with `0 < (P ^ n) i i` of a state `i` is `1` (the gcd of the return times is `1`).
* `MathFin.FiniteMarkov.IsPrimitive`: some positive power of `P` has all entries positive.
* `MathFin.FiniteMarkov.lazyChain`: the lazy chain `(I + P) / 2`.

## Main results

* `MathFin.FiniteMarkov.IsStationary.eq_of_isIrreducible`: for an irreducible stochastic matrix,
  two stationary distributions are equal (Saporito Theorem 1.4.25, uniqueness).
* `MathFin.FiniteMarkov.exists_isStationary_of_isIrreducible`: an irreducible stochastic matrix
  on a nonempty finite state space has a stationary distribution.
* `MathFin.FiniteMarkov.existsUnique_isStationary_of_isIrreducible`: hence exactly one.
* `MathFin.FiniteMarkov.isPrimitive_of_isIrreducible_of_isAperiodic`: irreducible and aperiodic
  imply primitive.
* `MathFin.FiniteMarkov.exists_isStationary_tendsto_pow_of_isPrimitive`: a primitive stochastic
  matrix has a stationary distribution `π` with `(P ^ n) i j → π j` for all `i j`.
* `MathFin.FiniteMarkov.tendsto_pow_of_isStationary`: for an irreducible aperiodic stochastic
  matrix and any stationary distribution `π`, `(P ^ n) i j → π j` (Saporito Theorem 1.4.40).
* `MathFin.FiniteMarkov.isIrreducible_transitionMatrix_iff`,
  `MathFin.FiniteMarkov.IsStationary.sum_mul_chainLaw` and
  `MathFin.FiniteMarkov.tendsto_chainLaw_visit`: the same notions and the convergence theorem for
  the chain `chainLaw K i`.

## Implementation notes

The state space is finite, so positive recurrence is automatic and is not a hypothesis. The matrix
theorems are stated for any row-stochastic matrix, because the argument is linear algebra; the
chain statements at the end of the file instantiate them at `transitionMatrix K`, the real matrix
of the one-step laws `K : S → PMF S` of `markovPathMeasure`. Aperiodicity is stated as a condition
on return times, which is the textbook definition; no rate of convergence is part of the
statements (the proof does give a geometric one).

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorems 1.4.25 and 1.4.40

## Tags

Markov chain, stationary distribution, irreducible, aperiodic, primitive matrix, Doeblin
condition, convergence to equilibrium, stochastic matrix, MSC 60J10
-/

@[expose] public section

namespace MathFin.FiniteMarkov

open Matrix Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-- `P` is irreducible: every state can reach every state, `0 < (P ^ n) i j` for some `n`. -/
def IsIrreducible (P : Matrix S S ℝ) : Prop :=
  ∀ i j, ∃ n : ℕ, 0 < (P ^ n) i j

/-- `P` is aperiodic: the only natural number dividing every return time `n ≥ 1` of a state `i`
(that is, every `n ≥ 1` with `0 < (P ^ n) i i`) is `1`. Equivalently the gcd of the return times of
every state is `1`. -/
def IsAperiodic (P : Matrix S S ℝ) : Prop :=
  ∀ i, ∀ d : ℕ, (∀ n : ℕ, 0 < n → 0 < (P ^ n) i i → d ∣ n) → d = 1

/-- `P` is primitive: some positive power of `P` has all entries strictly positive. -/
def IsPrimitive (P : Matrix S S ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∀ i j, 0 < (P ^ m) i j

/-- `π` is a stationary distribution for `P`: a probability vector (a point of Mathlib's standard
simplex) with `π ᵥ* P = π`. -/
def IsStationary (P : Matrix S S ℝ) (π : Convexity.StdSimplex ℝ S) : Prop :=
  (⇑π.weights) ᵥ* P = ⇑π.weights

/-- The lazy chain `(I + P) / 2`: stay put with probability `1/2`, otherwise move by `P`. -/
noncomputable def lazyChain (P : Matrix S S ℝ) : Matrix S S ℝ :=
  (1 / 2 : ℝ) • (1 : Matrix S S ℝ) + (1 / 2 : ℝ) • P

lemma IsStationary.sum_mul {π : Convexity.StdSimplex ℝ S} (h : IsStationary P π) (j : S) :
    ∑ i, π.weights i * P i j = π.weights j :=
  congrFun h j

lemma IsPrimitive.isIrreducible (h : IsPrimitive P) : IsIrreducible P :=
  fun i j => by
    obtain ⟨m, -, hm⟩ := h
    exact ⟨m, hm i j⟩

/-! ### Positivity -/

lemma pos_mul_apply {A B : Matrix S S ℝ} (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    {i j l : S} (h₁ : 0 < A i j) (h₂ : 0 < B j l) : 0 < (A * B) i l := by
  rw [Matrix.mul_apply]
  exact lt_of_lt_of_le (mul_pos h₁ h₂)
    (Finset.single_le_sum (f := fun k => A i k * B k l)
      (fun k _ => mul_nonneg (hA i k) (hB k l)) (Finset.mem_univ j))

lemma pow_add_pos (hP : P ∈ rowStochastic ℝ S) {a b : ℕ} {i j l : S}
    (h₁ : 0 < (P ^ a) i j) (h₂ : 0 < (P ^ b) j l) : 0 < (P ^ (a + b)) i l := by
  rw [pow_add]
  exact pos_mul_apply (A := P ^ a) (B := P ^ b)
    (fun _ _ => nonneg_of_mem_rowStochastic (pow_mem hP a))
    (fun _ _ => nonneg_of_mem_rowStochastic (pow_mem hP b)) h₁ h₂

lemma vecMul_pow_eq {u : S → ℝ} (hu : u ᵥ* P = u) (n : ℕ) : u ᵥ* P ^ n = u := by
  induction n with
  | zero => rw [pow_zero, Matrix.vecMul_one]
  | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hu]

/-- A nonnegative `P`-invariant vector of an irreducible chain that is positive somewhere is
positive everywhere. -/
lemma pos_of_isIrreducible (hP : P ∈ rowStochastic ℝ S) (hirr : IsIrreducible P) {u : S → ℝ}
    (hu0 : ∀ i, 0 ≤ u i) (hu : ∀ j, ∑ i, u i * P i j = u j) {i₁ : S} (hi₁ : 0 < u i₁)
    (j : S) : 0 < u j := by
  obtain ⟨n, hn⟩ := hirr i₁ j
  have h := congrFun (vecMul_pow_eq (funext hu : u ᵥ* P = u) n) j
  rw [Matrix.vecMul_apply_eq_sum] at h
  rw [← h]
  exact lt_of_lt_of_le (mul_pos hi₁ hn)
    (Finset.single_le_sum (f := fun i => u i * (P ^ n) i j)
      (fun i _ => mul_nonneg (hu0 i) (nonneg_of_mem_rowStochastic (pow_mem hP n)))
      (Finset.mem_univ i₁))

/-- The positive part of a `P`-invariant signed vector is `P`-invariant. -/
lemma posPart_sum (hP : P ∈ rowStochastic ℝ S) {w : S → ℝ}
    (hw : ∀ j, ∑ i, w i * P i j = w j) (j : S) :
    ∑ i, max (w i) 0 * P i j = max (w j) 0 := by
  obtain ⟨hP0, hrow⟩ := Matrix.mem_rowStochastic_iff_sum.1 hP
  have hle : ∀ j ∈ (Finset.univ : Finset S), max (w j) 0 ≤ ∑ i, max (w i) 0 * P i j := by
    intro j _
    refine max_le ?_ (Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (hP0 i j))
    calc w j = ∑ i, w i * P i j := (hw j).symm
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hP0 i j)
  have hsum : ∑ j, ∑ i, max (w i) 0 * P i j = ∑ j, max (w j) 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hrow i, mul_one]
  exact ((Finset.sum_eq_sum_iff_of_le hle).1 hsum.symm j (Finset.mem_univ j)).symm

/-- If the positive part `u` of a signed `P`-invariant vector is positive somewhere, then `u` and
the negative part `v` are both positive everywhere. -/
lemma pos_pair (hP : P ∈ rowStochastic ℝ S) (hirr : IsIrreducible P) {u v : S → ℝ}
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i)
    (hu : ∀ j, ∑ i, u i * P i j = u j) (hv : ∀ j, ∑ i, v i * P i j = v j)
    (hsum : ∑ i, u i = ∑ i, v i) {j₀ : S} (hj₀ : 0 < u j₀) (j : S) : 0 < u j ∧ 0 < v j := by
  have hsu : 0 < ∑ i, u i :=
    lt_of_lt_of_le hj₀ (Finset.single_le_sum (fun i _ => hu0 i) (Finset.mem_univ j₀))
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, 0 < v i₁ := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ i, v i ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
    linarith
  exact ⟨pos_of_isIrreducible hP hirr hu0 hu hj₀ j, pos_of_isIrreducible hP hirr hv0 hv hi₁ j⟩

/-- **Uniqueness of the stationary distribution** (Saporito Theorem 1.4.25): an irreducible
stochastic matrix has at most one stationary distribution. -/
theorem IsStationary.eq_of_isIrreducible (hP : P ∈ rowStochastic ℝ S) (hirr : IsIrreducible P)
    {π ν : Convexity.StdSimplex ℝ S} (hπ : IsStationary P π) (hν : IsStationary P ν) : ν = π := by
  have hd : ∀ j, ∑ i, (ν.weights i - π.weights i) * P i j = ν.weights j - π.weights j :=
    fun j => by simp only [sub_mul, Finset.sum_sub_distrib, hν.sum_mul j, hπ.sum_mul j]
  have he : ∀ j, ∑ i, (π.weights i - ν.weights i) * P i j = π.weights j - ν.weights j :=
    fun j => by simp only [sub_mul, Finset.sum_sub_distrib, hν.sum_mul j, hπ.sum_mul j]
  have hu : ∀ j, ∑ i, max (ν.weights i - π.weights i) 0 * P i j
      = max (ν.weights j - π.weights j) 0 :=
    posPart_sum hP (w := fun i => ν.weights i - π.weights i) hd
  have hv : ∀ j, ∑ i, max (π.weights i - ν.weights i) 0 * P i j
      = max (π.weights j - ν.weights j) 0 :=
    posPart_sum hP (w := fun i => π.weights i - ν.weights i) he
  have key : ∀ j, max (ν.weights j - π.weights j) 0 - max (π.weights j - ν.weights j) 0
      = ν.weights j - π.weights j := fun j => by
    rcases le_total (ν.weights j) (π.weights j) with h | h
    · rw [max_eq_right (show ν.weights j - π.weights j ≤ 0 by linarith),
        max_eq_left (show 0 ≤ π.weights j - ν.weights j by linarith)]
      ring
    · rw [max_eq_left (show 0 ≤ ν.weights j - π.weights j by linarith),
        max_eq_right (show π.weights j - ν.weights j ≤ 0 by linarith)]
      ring
  have hsum : ∑ j, max (ν.weights j - π.weights j) 0 = ∑ j, max (π.weights j - ν.weights j) 0 := by
    have h1 : ∑ j, max (ν.weights j - π.weights j) 0 - ∑ j, max (π.weights j - ν.weights j) 0
        = ∑ j, ν.weights j - ∑ j, π.weights j := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => key j
    rw [ν.total_of_fintype, π.total_of_fintype] at h1
    linarith
  refine Convexity.StdSimplex.ext (Finsupp.ext fun j₀ => ?_)
  by_contra hj₀
  rcases lt_or_gt_of_ne hj₀ with h | h
  · have hvpos : 0 < max (π.weights j₀ - ν.weights j₀) 0 := lt_max_of_lt_left (by linarith)
    have h2 : 0 < max (ν.weights j₀ - π.weights j₀) 0 :=
      (pos_pair hP hirr (u := fun j => max (π.weights j - ν.weights j) 0)
        (v := fun j => max (ν.weights j - π.weights j) 0) (fun i => le_max_right _ _)
        (fun i => le_max_right _ _) hv hu hsum.symm hvpos j₀).2
    rw [max_eq_right (show ν.weights j₀ - π.weights j₀ ≤ 0 by linarith)] at h2
    exact lt_irrefl _ h2
  · have hupos : 0 < max (ν.weights j₀ - π.weights j₀) 0 := lt_max_of_lt_left (by linarith)
    have h2 : 0 < max (π.weights j₀ - ν.weights j₀) 0 :=
      (pos_pair hP hirr (u := fun j => max (ν.weights j - π.weights j) 0)
        (v := fun j => max (π.weights j - ν.weights j) 0) (fun i => le_max_right _ _)
        (fun i => le_max_right _ _) hu hv hsum hupos j₀).2
    rw [max_eq_right (show π.weights j₀ - ν.weights j₀ ≤ 0 by linarith)] at h2
    exact lt_irrefl _ h2

/-! ### Doeblin's contraction -/

lemma sum_mul_le_of_le {R : Matrix S S ℝ} (hR0 : ∀ i j, 0 ≤ R i j) (hR1 : ∀ i, ∑ j, R i j = 1)
    {v : S → ℝ} {b : ℝ} (hv : ∀ k, v k ≤ b) (i : S) : ∑ k, R i k * v k ≤ b :=
  calc ∑ k, R i k * v k ≤ ∑ k, R i k * b :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hv k) (hR0 i k)
    _ = b := by rw [← Finset.sum_mul, hR1 i, one_mul]

lemma le_sum_mul_of_le {R : Matrix S S ℝ} (hR0 : ∀ i j, 0 ≤ R i j) (hR1 : ∀ i, ∑ j, R i j = 1)
    {v : S → ℝ} {a : ℝ} (hv : ∀ k, a ≤ v k) (i : S) : a ≤ ∑ k, R i k * v k :=
  calc a = ∑ k, R i k * a := by rw [← Finset.sum_mul, hR1 i, one_mul]
    _ ≤ ∑ k, R i k * v k :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hv k) (hR0 i k)

/-- One Doeblin step: if every entry of the stochastic matrix `Q` is at least `ε` and the values
of `v` lie within `δ` of each other, then the values of `Q v` lie within `(1 - |S| ε) δ`. -/
lemma doeblin_step {Q : Matrix S S ℝ} {ε : ℝ} (hQ0 : ∀ i j, 0 ≤ Q i j)
    (hQ1 : ∀ i, ∑ j, Q i j = 1) (hε : ∀ i j, ε ≤ Q i j) {v : S → ℝ} {δ : ℝ}
    (hv : ∀ k l, v k - v l ≤ δ) (i i' : S) :
    ∑ k, Q i k * v k - ∑ k, Q i' k * v k ≤ (1 - (Fintype.card S : ℝ) * ε) * δ := by
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_min_image Finset.univ v ⟨i, Finset.mem_univ i⟩
  have hlo : ∀ k, v k₀ ≤ v k := fun k => hk₀ k (Finset.mem_univ k)
  have hhi : ∀ k, v k ≤ v k₀ + δ := fun k => by linarith [hv k k₀]
  have hW : ∀ i, ∑ k, (Q i k - ε) = 1 - (Fintype.card S : ℝ) * ε := fun i => by
    rw [Finset.sum_sub_distrib, hQ1 i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsplit : ∀ i, ∑ k, Q i k * v k = ∑ k, (Q i k - ε) * v k + ε * ∑ k, v k := fun i => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hupper : ∑ k, (Q i k - ε) * v k ≤ (1 - (Fintype.card S : ℝ) * ε) * (v k₀ + δ) :=
    calc ∑ k, (Q i k - ε) * v k ≤ ∑ k, (Q i k - ε) * (v k₀ + δ) :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hhi k) (sub_nonneg.2 (hε i k))
      _ = _ := by rw [← Finset.sum_mul, hW i]
  have hlower : (1 - (Fintype.card S : ℝ) * ε) * v k₀ ≤ ∑ k, (Q i' k - ε) * v k :=
    calc (1 - (Fintype.card S : ℝ) * ε) * v k₀ = ∑ k, (Q i' k - ε) * v k₀ := by
          rw [← Finset.sum_mul, hW i']
      _ ≤ _ := Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (hlo k) (sub_nonneg.2 (hε i' k))
  rw [hsplit i, hsplit i']
  linarith

/-- The spread of a column of `P ^ n` is at most `(1 - |S| ε) ^ k` once `n ≥ k m`, when every
entry of `P ^ m` is at least `ε`. -/
lemma spread_pow (hP : P ∈ rowStochastic ℝ S) {m : ℕ} {ε : ℝ} (hε : ∀ i j, ε ≤ (P ^ m) i j)
    (j : S) : ∀ k n : ℕ, k * m ≤ n → ∀ i i' : S,
      (P ^ n) i j - (P ^ n) i' j ≤ (1 - (Fintype.card S : ℝ) * ε) ^ k := by
  intro k
  induction k with
  | zero =>
    intro n _ i i'
    have h1 := le_one_of_mem_rowStochastic (pow_mem hP n) (i := i) (j := j)
    have h2 := nonneg_of_mem_rowStochastic (pow_mem hP n) (i := i') (j := j)
    rw [pow_zero]
    linarith
  | succ k ih =>
    intro n hn i i'
    have hn' : k * m + m ≤ n := by
      rw [← Nat.succ_mul]
      exact hn
    have hmn : m ≤ n := le_trans (Nat.le_add_left m (k * m)) hn'
    have hkm : k * m ≤ n - m := Nat.le_sub_of_add_le hn'
    have hpow : P ^ n = P ^ m * P ^ (n - m) := by rw [← pow_add, Nat.add_sub_of_le hmn]
    obtain ⟨hQ0, hQ1⟩ := Matrix.mem_rowStochastic_iff_sum.1 (pow_mem hP m)
    have h := doeblin_step hQ0 hQ1 hε (v := fun l => (P ^ (n - m)) l j) (ih (n - m) hkm) i i'
    rw [pow_succ', hpow]
    simpa only [Matrix.mul_apply] using h

/-- Along a column, later entries of `P ^ n` stay within the spread of an earlier one. -/
lemma abs_pow_sub_le (hP : P ∈ rowStochastic ℝ S) {N n : ℕ} (hNn : N ≤ n) {j : S} {δ : ℝ}
    (hδ : ∀ i i', (P ^ N) i j - (P ^ N) i' j ≤ δ) (i : S) :
    |(P ^ n) i j - (P ^ N) i j| ≤ δ := by
  have hpow : P ^ n = P ^ (n - N) * P ^ N := by rw [← pow_add, Nat.sub_add_cancel hNn]
  obtain ⟨h0, h1⟩ := Matrix.mem_rowStochastic_iff_sum.1 (pow_mem hP (n - N))
  have hn : (P ^ n) i j = ∑ l, (P ^ (n - N)) i l * (P ^ N) l j := by
    rw [hpow, Matrix.mul_apply]
  have hlo : (P ^ N) i j - δ ≤ ∑ l, (P ^ (n - N)) i l * (P ^ N) l j :=
    le_sum_mul_of_le h0 h1 (v := fun l => (P ^ N) l j) (fun l => by linarith [hδ i l]) i
  have hhi : ∑ l, (P ^ (n - N)) i l * (P ^ N) l j ≤ (P ^ N) i j + δ :=
    sum_mul_le_of_le h0 h1 (v := fun l => (P ^ N) l j) (fun l => by linarith [hδ l i]) i
  rw [abs_le]
  constructor <;> linarith

/-- If some power `P ^ m` has all entries at least `ε > 0`, each column of `P ^ n` converges, to a
limit that does not depend on the row. -/
lemma exists_tendsto_col [Nonempty S] (hP : P ∈ rowStochastic ℝ S) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ i j, ε ≤ (P ^ m) i j) (j : S) :
    ∃ L : ℝ, ∀ i, Tendsto (fun n : ℕ => (P ^ n) i j) atTop (𝓝 L) := by
  obtain ⟨_, h1⟩ := Matrix.mem_rowStochastic_iff_sum.1 (pow_mem hP m)
  have hcard : (Fintype.card S : ℝ) * ε ≤ 1 := by
    obtain ⟨i₀⟩ := (inferInstance : Nonempty S)
    calc (Fintype.card S : ℝ) * ε = ∑ _k : S, ε := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ k, (P ^ m) i₀ k := Finset.sum_le_sum fun k _ => hε i₀ k
      _ = 1 := h1 i₀
  have hpos : 0 < (Fintype.card S : ℝ) * ε := mul_pos (Nat.cast_pos.2 Fintype.card_pos) hε0
  have hc0 : 0 ≤ 1 - (Fintype.card S : ℝ) * ε := by linarith
  have hc1 : 1 - (Fintype.card S : ℝ) * ε < 1 := by linarith
  have hosc := spread_pow hP hε j
  have hlim : Tendsto (fun N : ℕ => (1 - (Fintype.card S : ℝ) * ε) ^ (N / m)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).comp (Nat.tendsto_div_const_atTop hm.ne')
  have hb : Tendsto (fun N : ℕ => 2 * (1 - (Fintype.card S : ℝ) * ε) ^ (N / m)) atTop (𝓝 0) := by
    simpa using hlim.const_mul 2
  have hcau : ∀ i, CauchySeq (fun n : ℕ => (P ^ n) i j) := fun i =>
    cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 * (1 - (Fintype.card S : ℝ) * ε) ^ (N / m))
      (fun n n' N hn hn' => by
        simp only [Real.dist_eq]
        have hδ := hosc (N / m) N (Nat.div_mul_le_self N m)
        have h1 := abs_pow_sub_le hP hn hδ i
        have h2 := abs_pow_sub_le hP hn' hδ i
        have h3 := abs_sub_le ((P ^ n) i j) ((P ^ N) i j) ((P ^ n') i j)
        rw [abs_sub_comm ((P ^ N) i j) ((P ^ n') i j)] at h3
        linarith) hb
  choose L hL using fun i => cauchySeq_tendsto_of_complete (hcau i)
  have hdiff : ∀ i i', Tendsto (fun n : ℕ => (P ^ n) i j - (P ^ n) i' j) atTop (𝓝 0) :=
    fun i i' => by
      refine squeeze_zero_norm (fun n => ?_) hlim
      simp only [Real.norm_eq_abs, abs_le]
      have hn := hosc (n / m) n (Nat.div_mul_le_self n m)
      constructor
      · linarith [hn i' i]
      · exact hn i i'
  have hLeq : ∀ i i', L i = L i' := fun i i' =>
    sub_eq_zero.1 (tendsto_nhds_unique ((hL i).sub (hL i')) (hdiff i i'))
  exact ⟨L (Classical.arbitrary S), fun i => by
    rw [← hLeq i (Classical.arbitrary S)]
    exact hL i⟩

/-! ### Convergence for primitive matrices -/

/-- **Convergence for a primitive chain**: a primitive stochastic matrix on a nonempty finite state
space has a stationary distribution `π`, and `(P ^ n) i j → π j` for every `i` and `j`. -/
theorem exists_isStationary_tendsto_pow_of_isPrimitive [Nonempty S]
    (hP : P ∈ rowStochastic ℝ S) (hprim : IsPrimitive P) :
    ∃ π : Convexity.StdSimplex ℝ S, IsStationary P π ∧
      ∀ i j, Tendsto (fun n : ℕ => (P ^ n) i j) atTop (𝓝 (π.weights j)) := by
  obtain ⟨m, hm, hpos⟩ := hprim
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image (Finset.univ : Finset (S × S))
    (fun p => (P ^ m) p.1 p.2) ⟨(Classical.arbitrary S, Classical.arbitrary S), Finset.mem_univ _⟩
  have hε0 : 0 < (P ^ m) p.1 p.2 := hpos p.1 p.2
  have hε : ∀ i j, (P ^ m) p.1 p.2 ≤ (P ^ m) i j := fun i j => hp (i, j) (Finset.mem_univ _)
  choose L hL using fun j => exists_tendsto_col hP hm hε0 hε j
  have i₀ : S := Classical.arbitrary S
  have hL0 : ∀ j, 0 ≤ L j := fun j => ge_of_tendsto' (hL j i₀) fun n =>
    nonneg_of_mem_rowStochastic (pow_mem hP n)
  have hL1 : ∑ j, L j = 1 := by
    have h1 : Tendsto (fun n : ℕ => ∑ j, (P ^ n) i₀ j) atTop (𝓝 (∑ j, L j)) :=
      tendsto_finsetSum _ fun j _ => hL j i₀
    have h2 : (fun n : ℕ => ∑ j, (P ^ n) i₀ j) = fun _ => 1 :=
      funext fun n => sum_row_of_mem_rowStochastic (pow_mem hP n) i₀
    rw [h2] at h1
    exact (tendsto_nhds_unique tendsto_const_nhds h1).symm
  obtain ⟨π, hπ⟩ := Convexity.StdSimplex.exists_weights_eq_iff.2 ⟨hL0, hL1⟩
  refine ⟨π, ?_, fun i j => by rw [congrFun hπ j]; exact hL j i⟩
  · show (⇑π.weights) ᵥ* P = ⇑π.weights
    rw [hπ]
    funext j
    rw [Matrix.vecMul_apply_eq_sum]
    have h1 : Tendsto (fun n : ℕ => (P ^ (n + 1)) i₀ j) atTop (𝓝 (L j)) :=
      (hL j i₀).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => (P ^ (n + 1)) i₀ j) atTop (𝓝 (∑ k, L k * P k j)) := by
      have h3 : Tendsto (fun n : ℕ => ∑ k, (P ^ n) i₀ k * P k j) atTop
          (𝓝 (∑ k, L k * P k j)) :=
        tendsto_finsetSum _ fun k _ => (hL k i₀).mul_const (P k j)
      refine h3.congr fun n => ?_
      rw [pow_succ, Matrix.mul_apply]
    exact tendsto_nhds_unique h2 h1

/-! ### Irreducible and aperiodic imply primitive -/

/-- The additive monoid of return times of the state `i`, including `0`. -/
def returnTimes (hP : P ∈ rowStochastic ℝ S) (i : S) : AddSubmonoid ℕ where
  carrier := {n | 0 < (P ^ n) i i}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => pow_add_pos hP (i := i) (j := i) (l := i) ha hb

/-- **Irreducible and aperiodic imply primitive**: by Schur's theorem, the return times of each
state contain all large integers, and irreducibility connects any two states. -/
theorem isPrimitive_of_isIrreducible_of_isAperiodic (hP : P ∈ rowStochastic ℝ S)
    (hirr : IsIrreducible P) (hap : IsAperiodic P) : IsPrimitive P := by
  have hN : ∀ i, ∃ N : ℕ, ∀ n ≥ N, 0 < (P ^ n) i i := fun i => by
    obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge {n : ℕ | 0 < (P ^ n) i i}
    refine ⟨N, fun n hn => ?_⟩
    have hg : Nat.setGcd {n : ℕ | 0 < (P ^ n) i i} = 1 :=
      hap i _ fun n _ hpos =>
        Nat.setGcd_dvd_of_mem (s := {n : ℕ | 0 < (P ^ n) i i}) hpos
    have hmem : n ∈ AddSubmonoid.closure {n : ℕ | 0 < (P ^ n) i i} :=
      hN n hn (by rw [hg]; exact one_dvd n)
    exact (AddSubmonoid.closure_le.2 (fun x hx => hx : {n : ℕ | 0 < (P ^ n) i i} ⊆
      (returnTimes hP i : Set ℕ))) hmem
  choose N hN using hN
  choose a ha using (hirr : ∀ i j, ∃ n : ℕ, 0 < (P ^ n) i j)
  obtain ⟨N', hN'⟩ : ∃ N' : ℕ, ∀ i, N i ≤ N' :=
    ⟨Finset.univ.sup N, fun i => Finset.le_sup (f := N) (Finset.mem_univ i)⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ, ∀ i j, a i j ≤ A :=
    ⟨Finset.univ.sup fun p : S × S => a p.1 p.2, fun i j =>
      Finset.le_sup (f := fun p : S × S => a p.1 p.2) (Finset.mem_univ (i, j))⟩
  refine ⟨N' + A + 1, Nat.succ_pos _, fun i j => ?_⟩
  have h1 := hA i j
  have h2 := hN' j
  have h3 := pow_add_pos hP (ha i j) (hN j (N' + A + 1 - a i j) (by omega))
  rwa [Nat.add_sub_of_le (show a i j ≤ N' + A + 1 by omega)] at h3

/-! ### Existence for an irreducible chain, through the lazy chain -/

lemma lazyChain_mem (hP : P ∈ rowStochastic ℝ S) : lazyChain P ∈ rowStochastic ℝ S := by
  have h1 : (1 : Matrix S S ℝ) ∈ rowStochastic ℝ S := one_mem _
  show (1 / 2 : ℝ) • (1 : Matrix S S ℝ) + (1 / 2 : ℝ) • P ∈ rowStochastic ℝ S
  exact convex_rowStochastic (R := ℝ) (n := S) h1 hP (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)

lemma lazyChain_apply (P : Matrix S S ℝ) (i j : S) :
    lazyChain P i j = 1 / 2 * (1 : Matrix S S ℝ) i j + 1 / 2 * P i j := by
  simp only [lazyChain, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

lemma lazyChain_diag_pos (hP : P ∈ rowStochastic ℝ S) (i : S) : 0 < lazyChain P i i := by
  rw [lazyChain_apply, Matrix.one_apply_eq]
  have := nonneg_of_mem_rowStochastic hP (i := i) (j := i)
  linarith

lemma lazyChain_pos_of_pos {i l : S} (h : 0 < P i l) :
    0 < lazyChain P i l := by
  rw [lazyChain_apply]
  have := Matrix.zero_le_one_elem (α := ℝ) i l
  linarith

/-- A path of length `k ≤ n` for `P` is a path of length `n` for the lazy chain. -/
lemma lazyChain_pow_pos (hP : P ∈ rowStochastic ℝ S) :
    ∀ n k : ℕ, k ≤ n → ∀ i j, 0 < (P ^ k) i j → 0 < (lazyChain P ^ n) i j := by
  have hQ := lazyChain_mem hP
  intro n
  induction n with
  | zero =>
    intro k hk i j h
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    simpa using h
  | succ n ih =>
    intro k hk i j h
    rw [pow_succ']
    rcases Nat.le_succ_iff.1 hk with hk | rfl
    · exact pos_mul_apply (fun _ _ => nonneg_of_mem_rowStochastic hQ)
        (fun _ _ => nonneg_of_mem_rowStochastic (pow_mem hQ n))
        (lazyChain_diag_pos hP i) (ih k hk i j h)
    · rw [pow_succ', Matrix.mul_apply] at h
      obtain ⟨l, hl⟩ : ∃ l, 0 < P i l * (P ^ n) l j := by
        by_contra hcon
        push_neg at hcon
        exact absurd h (not_lt.2 (Finset.sum_nonpos fun l _ => hcon l))
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hl with ⟨h1, h2⟩ | ⟨h1, -⟩
      · exact pos_mul_apply (fun _ _ => nonneg_of_mem_rowStochastic hQ)
          (fun _ _ => nonneg_of_mem_rowStochastic (pow_mem hQ n))
          (lazyChain_pos_of_pos h1) (ih n le_rfl l j h2)
      · exact absurd h1 (not_lt.2 (nonneg_of_mem_rowStochastic hP))

/-- **Existence of a stationary distribution** for an irreducible stochastic matrix on a nonempty
finite state space. -/
theorem exists_isStationary_of_isIrreducible [Nonempty S] (hP : P ∈ rowStochastic ℝ S)
    (hirr : IsIrreducible P) : ∃ π : Convexity.StdSimplex ℝ S, IsStationary P π := by
  choose a ha using (hirr : ∀ i j, ∃ n : ℕ, 0 < (P ^ n) i j)
  obtain ⟨A, hA⟩ : ∃ A : ℕ, ∀ i j, a i j ≤ A :=
    ⟨Finset.univ.sup fun p : S × S => a p.1 p.2, fun i j =>
      Finset.le_sup (f := fun p : S × S => a p.1 p.2) (Finset.mem_univ (i, j))⟩
  have hprim : IsPrimitive (lazyChain P) :=
    ⟨A + 1, Nat.succ_pos A, fun i j =>
      lazyChain_pow_pos hP (A + 1) (a i j) (by have := hA i j; omega) i j (ha i j)⟩
  obtain ⟨π, hπ, -⟩ := exists_isStationary_tendsto_pow_of_isPrimitive (lazyChain_mem hP) hprim
  refine ⟨π, ?_⟩
  have h : (⇑π.weights) ᵥ* lazyChain P = ⇑π.weights := hπ
  simp only [lazyChain] at h
  rw [Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_smul, Matrix.vecMul_one] at h
  show (⇑π.weights) ᵥ* P = ⇑π.weights
  funext j
  have hj := congrFun h j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
  linarith

/-- An irreducible stochastic matrix on a nonempty finite state space has exactly one stationary
distribution (Saporito Theorem 1.4.25). -/
theorem existsUnique_isStationary_of_isIrreducible [Nonempty S] (hP : P ∈ rowStochastic ℝ S)
    (hirr : IsIrreducible P) : ∃! π : Convexity.StdSimplex ℝ S, IsStationary P π :=
  let ⟨π, hπ⟩ := exists_isStationary_of_isIrreducible hP hirr
  ⟨π, hπ, fun _ hν => hπ.eq_of_isIrreducible hP hirr hν⟩

/-- **Convergence to the stationary distribution** (Saporito Theorem 1.4.40): for an irreducible
aperiodic stochastic matrix and a stationary distribution `π`, `(P ^ n) i j → π j` for all `i`
and `j`. -/
theorem tendsto_pow_of_isStationary (hP : P ∈ rowStochastic ℝ S) (hirr : IsIrreducible P)
    (hap : IsAperiodic P) {π : Convexity.StdSimplex ℝ S} (hπ : IsStationary P π) (i j : S) :
    Tendsto (fun n : ℕ => (P ^ n) i j) atTop (𝓝 (π.weights j)) := by
  haveI := π.nonempty
  obtain ⟨π', hπ', hlim⟩ := exists_isStationary_tendsto_pow_of_isPrimitive hP
    (isPrimitive_of_isIrreducible_of_isAperiodic hP hirr hap)
  rw [hπ'.eq_of_isIrreducible hP hirr hπ]
  exact hlim i j

/-! ### The chain `chainLaw K i` -/

section Chain

variable [MeasurableSpace S] [MeasurableSingletonClass S] (K : S → PMF S)

/-- **Irreducibility of a chain**: the transition matrix of the one-step laws `K` is irreducible
exactly when every state is reached from every state with positive probability, `0 < ℙ_i(X_n = j)`
for some `n`. -/
theorem isIrreducible_transitionMatrix_iff :
    IsIrreducible (transitionMatrix K) ↔ ∀ i j, ∃ n : ℕ, 0 < chainLaw K i {ω | ω n = j} := by
  refine forall₂_congr fun i j => exists_congr fun n => ?_
  rw [← chainLaw_visit_toReal_eq_pow, ENNReal.toReal_pos_iff]
  exact (and_iff_left (MeasureTheory.measure_lt_top _ _)).symm

/-- **Stationarity of a chain**: if `π` is stationary for the transition matrix of `K`, the
chain started from `π` has marginal `π` at every time, `∑ᵢ πᵢ ℙ_i(X_n = j) = π j`. -/
theorem IsStationary.sum_mul_chainLaw {π : Convexity.StdSimplex ℝ S}
    (h : IsStationary (transitionMatrix K) π) (j : S) (n : ℕ) :
    ∑ i, π.weights i * (chainLaw K i {ω | ω n = j}).toReal = π.weights j := by
  have h1 := congrFun (vecMul_pow_eq (u := ⇑π.weights) h n) j
  rw [Matrix.vecMul_apply_eq_sum] at h1
  simpa only [chainLaw_visit_toReal_eq_pow K] using h1

/-- **Convergence to equilibrium for a chain** (Saporito Theorem 1.4.40): if the transition matrix
of `K` is irreducible and aperiodic and `π` is stationary, then `ℙ_i(X_n = j) → π j`. -/
theorem tendsto_chainLaw_visit (hirr : IsIrreducible (transitionMatrix K))
    (hap : IsAperiodic (transitionMatrix K)) {π : Convexity.StdSimplex ℝ S}
    (hπ : IsStationary (transitionMatrix K) π) (i j : S) :
    Tendsto (fun n : ℕ => (chainLaw K i {ω | ω n = j}).toReal) atTop (𝓝 (π.weights j)) := by
  simp only [chainLaw_visit_toReal_eq_pow K]
  exact tendsto_pow_of_isStationary (transitionMatrix_mem_rowStochastic K) hirr hap hπ i j

end Chain

end MathFin.FiniteMarkov
