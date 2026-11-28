/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Discrete.MarkovPathMeasure
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Data.Matrix.Mul

public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Markov chains on path space: the recurrence criterion and the strong Markov property

`MarkovPathMeasure.lean` builds the law of the chain `(init, P)` on the space `ℕ → ι` of
trajectories (Ionescu–Tulcea) and proves the cylinder formula of Saporito Theorem 1.1.2. This file
works with that law, `markovPathMeasure init P`, and proves two statements about it.

**The Markov property at a fixed time, then at a stopping time** (Saporito Theorem 1.2.11). From the
cylinder formula, and the fact that two finite measures on trajectories with the same marginals on
every initial segment are equal (the projective-limit uniqueness behind `Kernel.eq_traj`), the
law of the post-`k` process `ω ↦ (ω (k + m))ₘ` on `{X_k = j}` is the law of the chain started at
`j`, independently of the history up to `k`
(`markovPathMeasure_inter_shift`). Summing over the values of a stopping time of the chain's
natural filtration `Filtration.piLE` gives the strong Markov property
(`markovPathMeasure_strong_markov`), for every initial law.

**The recurrence criterion** (Saporito Theorem 1.3.12). On a countable state space the chain
returns to `i` with probability one if and only if `∑ₙ ℙ_i(X_n = i) = ∞`
(`chainLaw_return_eq_one_iff_tsum_eq_top`). The proof is the first-passage decomposition of the
`n`-step return probability, proved from the Markov property at the first return time, and a
renewal argument on sequences. On a finite state space `ℙ_i(X_n = i)` is the matrix power
`(Pⁿ) i i` over `ℝ≥0∞` (`chainLaw_visit_eq_pow`, `chainLaw_return_eq_one_iff`).

**The 0–1 law for visits** (`chainLaw_visits_infinitely_often_eq_one_iff`). The first Borel–Cantelli
lemma gives that a state with `∑ₙ ℙ_i(X_n = i) < ∞` is visited infinitely often with probability
zero. If instead the return probability `f` is one, the number of returns is geometric,
`ℙ_i(at least k + 1 returns) = f · ℙ_i(at least k returns)` (the Markov property at the first
return time, applied to the shifted trajectory), so all these probabilities are one and the state
is visited infinitely often almost surely.

**The real transition matrix.** The transition law is `P : ι → PMF ι` (the convention of
`MarkovPathMeasure.lean`). Its real matrix `transitionMatrix P` is row-stochastic, and its powers
are the `n`-step probabilities (`chainLaw_visit_toReal_eq_pow`), so the matrix theory of
`FiniteMarkovChain.lean` (irreducibility, stationary distributions, convergence) is a statement
about the chain.

The ergodic theorem is not proved here (see `MarkovErgodic.lean`).

## Main definitions

* `shiftBy`: the post-`k` process `m ↦ ω (k + m)` of a trajectory.
* `chainLaw`: the law of the chain started at `i`, `markovPathMeasure (PMF.pure i) P`.
* `firstReturnAt`: the event that the first return of the chain to `i` happens at time `k`.

## Main results

* `markovPathMeasure_inter_shift`: the Markov property at the fixed time `k`; for every event of the
  history up to time `k` ending in `j` and every event `A` of the post-`k` process, the probability
  of the intersection is `ℙ(history) · ℙ_j(A)`.
* `markovPathMeasure_strong_markov`: the strong Markov property; for a stopping time `τ` of the
  natural filtration, `C ∈ 𝓕_τ` and an event `A` of trajectories,
  `ℙ(C ∩ {τ < ∞, X_τ = j, θ_τ X ∈ A}) = ℙ(C ∩ {τ < ∞, X_τ = j}) · ℙ_j(A)`.
* `chainLaw_visit_eq_pow`: `ℙ_i(X_n = j) = (Pⁿ) i j`.
* `transitionMatrix`, `transitionMatrix_mem_rowStochastic`, `chainLaw_visit_toReal_eq_pow`: the
  real transition matrix `(P a b).toReal`, its row-stochasticity, and `(ℙ_i(X_n = j)).toReal`
  as its `n`-th power entry.
* `chainLaw_visit_succ`: the first-passage decomposition `ℙ_i(X_{n+1} = i)
  = ∑_{k ≤ n} ℙ_i(τ_i⁺ = k + 1) ℙ_i(X_{n-k} = i)`.
* `chainLaw_return_eq_one_iff_tsum_eq_top`: `ℙ_i(τ_i⁺ < ∞) = 1 ↔ ∑ₙ ℙ_i(X_n = i) = ∞`
  (Theorem 1.3.12, countable state space); `chainLaw_return_eq_one_iff` is the matrix-power form
  for a finite state space.
* `chainLaw_visits_infinitely_often_null`, `chainLaw_visits_infinitely_often_eq_one`,
  `chainLaw_visits_infinitely_often_eq_one_iff`: `ℙ_i(X_n = i` infinitely often`)` is one if
  `∑ₙ ℙ_i(X_n = i) = ∞` and zero otherwise.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorems 1.2.11 and 1.3.12

## Tags

Markov chain, strong Markov property, recurrence criterion, first return time, renewal equation,
stopping time, Borel–Cantelli lemma, path space, MSC 60J10, MSC 60G40
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]

/-! ### Trajectories with the same initial-segment marginals are equal -/

omit [MeasurableSingletonClass ι] [Countable ι] in
/-- Two measures on trajectories, the first finite, whose images under every restriction to an
initial segment `{0, …, n}` agree, are equal. This is the uniqueness of the projective limit
(`IsProjectiveLimit.unique`) that stands behind `Kernel.eq_traj`. -/
lemma ext_of_map_frestrictLe {μ ν : Measure (ℕ → ι)} [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (frestrictLe (π := fun _ : ℕ ↦ ι) n)
      = ν.map (frestrictLe (π := fun _ : ℕ ↦ ι) n)) :
    μ = ν := by
  have hproj : IsProjectiveMeasureFamily (α := fun _ : ℕ ↦ ι)
      (inducedFamily (X := fun _ : ℕ ↦ ι) fun n ↦ μ.map (frestrictLe (π := fun _ : ℕ ↦ ι) n)) :=
    isProjectiveMeasureFamily_inducedFamily (X := fun _ : ℕ ↦ ι)
      (fun n ↦ μ.map (frestrictLe (π := fun _ : ℕ ↦ ι) n)) fun a b hab ↦ by
      change (μ.map (frestrictLe (π := fun _ : ℕ ↦ ι) b)).map
          (frestrictLe₂ (π := fun _ : ℕ ↦ ι) hab) = μ.map (frestrictLe (π := fun _ : ℕ ↦ ι) a)
      rw [Measure.map_map (measurable_frestrictLe₂ (X := fun _ : ℕ ↦ ι) hab)
        (measurable_frestrictLe (X := fun _ : ℕ ↦ ι) b), frestrictLe₂_comp_frestrictLe]
  exact ((isProjectiveLimit_nat_iff hproj μ).2 fun n ↦ by rw [inducedFamily_Iic]).unique
    ((isProjectiveLimit_nat_iff hproj ν).2 fun n ↦ by rw [inducedFamily_Iic, h n])

/-! ### The Markov property at a fixed time -/

/-- The post-`k` process of a trajectory: `m ↦ ω (k + m)`. -/
def shiftBy (k : ℕ) (ω : ℕ → ι) : ℕ → ι := fun m ↦ ω (k + m)

omit [MeasurableSingletonClass ι] [Countable ι] in
lemma measurable_shiftBy (k : ℕ) : Measurable (shiftBy (ι := ι) k) :=
  Measurable.of_eval fun m ↦ measurable_pi_apply (k + m)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
/-- A history up to time `m` is the restriction of a trajectory, namely the cylinder of any
extension of it, and the extension can be chosen to end where the history does. -/
lemma exists_pathCylinder_eq_preimage (a : ι) {m : ℕ} (h : Π _ : Iic m, ι) :
    ∃ path : ℕ → ι, frestrictLe (π := fun _ : ℕ ↦ ι) m ⁻¹' {h} = pathCylinder path m ∧
      path m = h ⟨m, mem_Iic.2 le_rfl⟩ := by
  refine ⟨fun l ↦ if hl : l ≤ m then h ⟨l, mem_Iic.2 hl⟩ else a, ?_, ?_⟩
  · ext ω
    constructor
    · intro hω l hl
      have h1 : frestrictLe (π := fun _ : ℕ ↦ ι) m ω = h := hω
      subst h1
      show ω l = if hl' : l ≤ m then (frestrictLe (π := fun _ : ℕ ↦ ι) m ω) ⟨l, mem_Iic.2 hl'⟩
        else a
      rw [dif_pos hl]
      try rfl
    · intro hω
      show frestrictLe (π := fun _ : ℕ ↦ ι) m ω = h
      funext i
      have h1 : ω i = if hl : (i : ℕ) ≤ m then h ⟨i, mem_Iic.2 hl⟩ else a :=
        hω (i : ℕ) (mem_Iic.1 i.2)
      rw [dif_pos (mem_Iic.1 i.2)] at h1
      exact h1
  · show (if hl : m ≤ m then h ⟨m, mem_Iic.2 hl⟩ else a) = h ⟨m, mem_Iic.2 le_rfl⟩
    rw [dif_pos (le_refl m)]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
/-- Splicing: a path `q` up to time `k` and a path `hpath` that starts where `q` is at time `k`
glue to one path. -/
lemma exists_path_splice (q hpath : ℕ → ι) (k : ℕ) (h0 : hpath 0 = q k) :
    ∃ r : ℕ → ι, (∀ l ≤ k, r l = q l) ∧ ∀ x, r (k + x) = hpath x := by
  refine ⟨fun l ↦ if l ≤ k then q l else hpath (l - k), ?_, ?_⟩
  · intro l hl
    show (if l ≤ k then q l else hpath (l - k)) = q l
    rw [if_pos hl]
  · intro x
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · show (if k + 0 ≤ k then q (k + 0) else hpath (k + 0 - k)) = hpath 0
      have hc : k + 0 ≤ k := by omega
      rw [if_pos hc]
      exact h0.symm
    · show (if k + x ≤ k then q (k + x) else hpath (k + x - k)) = hpath x
      have hc : ¬ k + x ≤ k := by omega
      rw [if_neg hc, Nat.add_sub_cancel_left]

/-- The cylinder up to time `k` along `q`, intersected with the event that the post-`k` process
lies in a cylinder along `hpath`, has probability the product of the two cylinder probabilities,
the second under the chain started at `q k`: the cylinder formula, split at time `k`. -/
lemma cylinder_inter_shift_cylinder (init : PMF ι) (P : ι → PMF ι) (q : ℕ → ι) (k : ℕ)
    (hpath : ℕ → ι) (m : ℕ) :
    markovPathMeasure init P (pathCylinder q k ∩ shiftBy k ⁻¹' pathCylinder hpath m)
      = markovPathMeasure init P (pathCylinder q k)
          * markovPathMeasure (PMF.pure (q k)) P (pathCylinder hpath m) := by
  by_cases h0 : hpath 0 = q k
  · obtain ⟨r, hr0, hr1⟩ := exists_path_splice q hpath k h0
    have hset : pathCylinder q k ∩ shiftBy k ⁻¹' pathCylinder hpath m
        = pathCylinder r (k + m) := by
      ext ω
      constructor
      · rintro ⟨h1, h2⟩ l hl
        by_cases hlk : l ≤ k
        · rw [hr0 l hlk]
          exact h1 l hlk
        · obtain ⟨x, rfl⟩ : ∃ x, l = k + x := ⟨l - k, by omega⟩
          rw [hr1 x]
          exact h2 x (by omega)
      · intro h
        refine ⟨?_, ?_⟩
        · intro l hl
          rw [← hr0 l hl]
          exact h l (by omega)
        · intro l hl
          show ω (k + l) = hpath l
          rw [← hr1 l]
          exact h (k + l) (by omega)
    have e1 : ∏ x ∈ Finset.range k, P (r x) (r (x + 1))
        = ∏ x ∈ Finset.range k, P (q x) (q (x + 1)) :=
      Finset.prod_congr rfl fun x hx ↦ by
        rw [hr0 x (Finset.mem_range.1 hx).le, hr0 (x + 1) (Finset.mem_range.1 hx)]
    have e2 : ∏ x ∈ Finset.range m, P (r (k + x)) (r (k + x + 1))
        = ∏ x ∈ Finset.range m, P (hpath x) (hpath (x + 1)) :=
      Finset.prod_congr rfl fun x _ ↦ by
        rw [hr1 x, Nat.add_assoc k x 1, hr1 (x + 1)]
    rw [hset, markovPathMeasure_cylinder, markovPathMeasure_cylinder,
      markovPathMeasure_cylinder, Finset.prod_range_add, hr0 0 (Nat.zero_le k), e1, e2, h0,
      PMF.pure_apply_self]
    ring
  · have hempty : pathCylinder q k ∩ shiftBy k ⁻¹' pathCylinder hpath m = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω ↦ h0 ?_
      have a : ω k = q k := hω.1 k le_rfl
      have b : ω (k + 0) = hpath 0 := hω.2 0 (Nat.zero_le m)
      rw [Nat.add_zero] at b
      exact b.symm.trans a
    rw [hempty, measure_empty, markovPathMeasure_cylinder (PMF.pure (q k)) P hpath m,
      PMF.pure_apply_of_ne (q k) (hpath 0) h0, zero_mul, mul_zero]

/-- The Markov property at a fixed time along a single path: the cylinder up to time `k` along `q`
and the event `shiftBy k ω ∈ A` are independent, the second having the law of the chain started
at `q k`. -/
lemma markovPathMeasure_cylinder_inter_shift (init : PMF ι) (P : ι → PMF ι) (q : ℕ → ι) (k : ℕ)
    {A : Set (ℕ → ι)} (hA : MeasurableSet A) :
    markovPathMeasure init P (pathCylinder q k ∩ shiftBy k ⁻¹' A)
      = markovPathMeasure init P (pathCylinder q k)
          * markovPathMeasure (PMF.pure (q k)) P A := by
  have hν1 : ∀ S : Set (ℕ → ι), MeasurableSet S →
      (((markovPathMeasure init P).restrict (pathCylinder q k)).map (shiftBy k)) S
        = markovPathMeasure init P (pathCylinder q k ∩ shiftBy k ⁻¹' S) := by
    intro S hS
    rw [Measure.map_apply (measurable_shiftBy k) hS,
      Measure.restrict_apply ((measurable_shiftBy k) hS), Set.inter_comm]
  have key : ((markovPathMeasure init P).restrict (pathCylinder q k)).map (shiftBy k)
      = markovPathMeasure init P (pathCylinder q k) • markovPathMeasure (PMF.pure (q k)) P := by
    refine ext_of_map_frestrictLe fun m ↦ Measure.ext_of_singleton fun h ↦ ?_
    have hS : MeasurableSet (frestrictLe (π := fun _ : ℕ ↦ ι) m ⁻¹' {h}) :=
      (measurable_frestrictLe (X := fun _ : ℕ ↦ ι) m) (measurableSet_singleton h)
    obtain ⟨path, hcyl, -⟩ := exists_pathCylinder_eq_preimage (q k) h
    rw [Measure.map_apply (measurable_frestrictLe (X := fun _ : ℕ ↦ ι) m)
        (measurableSet_singleton h),
      Measure.map_apply (measurable_frestrictLe (X := fun _ : ℕ ↦ ι) m)
        (measurableSet_singleton h),
      hν1 _ hS, Measure.smul_apply, smul_eq_mul, hcyl]
    exact cylinder_inter_shift_cylinder init P q k path m
  have h1 := hν1 A hA
  rw [key, Measure.smul_apply, smul_eq_mul] at h1
  exact h1.symm

/-- **The Markov property at a fixed time.** Let `B` be a set of histories up to time `k`, all of
which end in the state `j`, and `A` a measurable set of trajectories. Under the law of the chain
with any initial distribution, the event "the history up to `k` lies in `B`" and the event "the
post-`k` process lies in `A`" are independent in the following sense: the probability that both
happen is the probability of the first times the probability of `A` under the chain started at
`j`. -/
theorem markovPathMeasure_inter_shift (init : PMF ι) (P : ι → PMF ι) (k : ℕ) {j : ι}
    (B : Set (Π _ : Iic k, ι)) (hB : ∀ h ∈ B, h ⟨k, mem_Iic.2 le_rfl⟩ = j)
    {A : Set (ℕ → ι)} (hA : MeasurableSet A) :
    markovPathMeasure init P (frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' B ∩ shiftBy k ⁻¹' A)
      = markovPathMeasure init P (frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' B)
          * markovPathMeasure (PMF.pure j) P A := by
  have hmeas : ∀ h : Π _ : Iic k, ι,
      MeasurableSet (frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' {h}) := fun h ↦
    (measurable_frestrictLe (X := fun _ : ℕ ↦ ι) k) (measurableSet_singleton h)
  have hterm : ∀ h ∈ B,
      markovPathMeasure init P (frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' {h} ∩ shiftBy k ⁻¹' A)
        = markovPathMeasure init P (frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' {h})
          * markovPathMeasure (PMF.pure j) P A := by
    intro h hh
    obtain ⟨q, hq, hqk⟩ := exists_pathCylinder_eq_preimage j h
    rw [hq, markovPathMeasure_cylinder_inter_shift init P q k hA, hqk, hB h hh]
  have hdisj : B.PairwiseDisjoint
      (fun h ↦ frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' {h}) := by
    intro h _ h' _ hne
    exact Disjoint.preimage _ (Set.disjoint_singleton.2 hne)
  have hdisj' : B.PairwiseDisjoint
      (fun h ↦ frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' {h} ∩ shiftBy k ⁻¹' A) :=
    hdisj.mono fun h ↦ Set.inter_subset_left
  have hU : ∀ S : Set (ℕ → ι), frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' B ∩ S
      = ⋃ h ∈ B, (frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' {h} ∩ S) := by
    intro S
    ext ω
    constructor
    · rintro ⟨hω, hS⟩
      exact Set.mem_iUnion₂.2 ⟨frestrictLe (π := fun _ : ℕ ↦ ι) k ω, hω, rfl, hS⟩
    · intro hω
      obtain ⟨h, hh, hωh, hωS⟩ := Set.mem_iUnion₂.1 hω
      refine ⟨?_, hωS⟩
      have e : frestrictLe (π := fun _ : ℕ ↦ ι) k ω = h := hωh
      show frestrictLe (π := fun _ : ℕ ↦ ι) k ω ∈ B
      rw [e]
      exact hh
  have hU0 := hU Set.univ
  simp only [Set.inter_univ] at hU0
  rw [hU (shiftBy k ⁻¹' A), measure_biUnion (Set.to_countable B) hdisj'
      (fun h _ ↦ (hmeas h).inter (measurable_shiftBy k hA)),
    hU0, measure_biUnion (Set.to_countable B) hdisj (fun h _ ↦ hmeas h),
    ← ENNReal.tsum_mul_right]
  exact tsum_congr fun p ↦ hterm p p.2

/-! ### The strong Markov property -/

/-- **The strong Markov property** (Saporito Theorem 1.2.11). Let `τ` be a stopping time of the
natural filtration `Filtration.piLE` of the coordinate process on `ℕ → ι`, `C` an event of the
stopped σ-algebra `𝓕_τ`, `j` a state and `A` a measurable set of trajectories. Under the law of the
chain with any initial distribution,

  `ℙ(C ∩ {τ < ∞, X_τ = j, (X_{τ+m})ₘ ∈ A}) = ℙ(C ∩ {τ < ∞, X_τ = j}) · ℙ_j(A)`,

where `ℙ_j = markovPathMeasure (PMF.pure j) P` is the law of the chain started at `j`. In words:
on `{τ < ∞, X_τ = j}` the post-`τ` process has the law of the chain started at `j` and is
independent of `𝓕_τ`. -/
theorem markovPathMeasure_strong_markov (init : PMF ι) (P : ι → PMF ι)
    {τ : (ℕ → ι) → WithTop ℕ} (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ ι)) τ)
    {C : Set (ℕ → ι)} (hC : MeasurableSet[hτ.measurableSpace] C) (j : ι)
    {A : Set (ℕ → ι)} (hA : MeasurableSet A) :
    markovPathMeasure init P
        (C ∩ {ω | ∃ k : ℕ, τ ω = (k : WithTop ℕ) ∧ ω k = j ∧ shiftBy k ω ∈ A})
      = markovPathMeasure init P (C ∩ {ω | ∃ k : ℕ, τ ω = (k : WithTop ℕ) ∧ ω k = j})
          * markovPathMeasure (PMF.pure j) P A := by
  -- the event `C ∩ {τ = k} ∩ {X_k = j}` is a set of histories up to time `k`
  have key : ∀ k : ℕ, ∃ B : Set (Π _ : Iic k, ι), (∀ h ∈ B, h ⟨k, mem_Iic.2 le_rfl⟩ = j) ∧
      C ∩ {ω | τ ω = (k : WithTop ℕ)} ∩ {ω | ω k = j}
        = frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' B := by
    intro k
    have hτk : MeasurableSet[hτ.measurableSpace] {ω | τ ω = (k : WithTop ℕ)} :=
      hτ.measurableSet_eq_of_countable' k
    have hCk : MeasurableSet[Filtration.piLE (X := fun _ : ℕ ↦ ι) k]
        (C ∩ {ω | τ ω = (k : WithTop ℕ)}) :=
      (hτ.measurableSet_inter_eq_iff C k).1 (hC.inter hτk)
    rw [Filtration.piLE_eq_comap_frestrictLe] at hCk
    obtain ⟨S, -, hS⟩ := MeasurableSpace.measurableSet_comap.1 hCk
    refine ⟨S ∩ {h | h ⟨k, mem_Iic.2 le_rfl⟩ = j}, fun h hh ↦ hh.2, ?_⟩
    ext ω
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : ω ∈ frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' S := by
        rw [hS]
        exact h1
      exact Set.mem_preimage.2 (Set.mem_inter h1' h2)
    · intro hω
      have hω' := Set.mem_preimage.1 hω
      have h1 : ω ∈ frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' S := hω'.1
      rw [hS] at h1
      exact Set.mem_inter h1 hω'.2
  have hmeasD : ∀ k : ℕ, MeasurableSet (C ∩ {ω | τ ω = (k : WithTop ℕ)} ∩ {ω | ω k = j}) := by
    intro k
    obtain ⟨B, -, hDB⟩ := key k
    rw [hDB]
    exact (measurable_frestrictLe (X := fun _ : ℕ ↦ ι) k) (Set.to_countable B).measurableSet
  have hdisjD : Pairwise (Function.onFun Disjoint
      fun k : ℕ ↦ C ∩ {ω | τ ω = (k : WithTop ℕ)} ∩ {ω | ω k = j}) := by
    intro k k' hne
    refine Set.disjoint_left.2 fun ω h h' ↦ hne ?_
    have e1 : τ ω = (k : WithTop ℕ) := h.1.2
    have e2 : τ ω = (k' : WithTop ℕ) := h'.1.2
    have e := e1.symm.trans e2
    first
      | exact WithTop.coe_injective e
      | exact_mod_cast e
      | simpa using e
  have hdisj1 : Pairwise (Function.onFun Disjoint
      fun k : ℕ ↦ (C ∩ {ω | τ ω = (k : WithTop ℕ)} ∩ {ω | ω k = j}) ∩ shiftBy k ⁻¹' A) :=
    fun k k' hne ↦
      Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hdisjD hne)
  have hL : C ∩ {ω | ∃ k : ℕ, τ ω = (k : WithTop ℕ) ∧ ω k = j ∧ shiftBy k ω ∈ A}
      = ⋃ k : ℕ, (C ∩ {ω | τ ω = (k : WithTop ℕ)} ∩ {ω | ω k = j}) ∩ shiftBy k ⁻¹' A := by
    ext ω
    constructor
    · rintro ⟨hωC, k, hk, hωj, hωA⟩
      exact Set.mem_iUnion.2 ⟨k, Set.mem_inter (Set.mem_inter (Set.mem_inter hωC hk) hωj) hωA⟩
    · intro hω
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hω
      obtain ⟨⟨⟨hωC, hτk⟩, hωj⟩, hωA⟩ := hk
      exact ⟨hωC, k, hτk, hωj, hωA⟩
  have hR : C ∩ {ω | ∃ k : ℕ, τ ω = (k : WithTop ℕ) ∧ ω k = j}
      = ⋃ k : ℕ, C ∩ {ω | τ ω = (k : WithTop ℕ)} ∩ {ω | ω k = j} := by
    ext ω
    constructor
    · rintro ⟨hωC, k, hk, hωj⟩
      exact Set.mem_iUnion.2 ⟨k, Set.mem_inter (Set.mem_inter hωC hk) hωj⟩
    · intro hω
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hω
      obtain ⟨⟨hωC, hτk⟩, hωj⟩ := hk
      exact ⟨hωC, k, hτk, hωj⟩
  rw [hL, hR, measure_iUnion hdisj1 fun k ↦ (hmeasD k).inter (measurable_shiftBy k hA),
    measure_iUnion hdisjD hmeasD, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun k ↦ ?_
  obtain ⟨B, hB, hDB⟩ := key k
  rw [hDB]
  exact markovPathMeasure_inter_shift init P k B hB hA

/-! ### Return times and the renewal decomposition -/

/-- The law of the chain started at the state `i`. -/
noncomputable abbrev chainLaw (P : ι → PMF ι) (i : ι) : Measure (ℕ → ι) :=
  markovPathMeasure (PMF.pure i) P

/-- The histories up to time `k` that are at `i` at time `k` and not at `i` at any time
`0 < l < k`: the first return to `i` happens at time `k`. -/
def firstReturnHist (i : ι) (k : ℕ) : Set (Π _ : Iic k, ι) :=
  {h | h ⟨k, mem_Iic.2 le_rfl⟩ = i ∧ ∀ l : Iic k, 0 < (l : ℕ) → (l : ℕ) < k → h l ≠ i}

/-- The trajectories whose first return to `i` (at a time `> 0`) happens at time `k`:
`{τ_i⁺ = k}`, an event of the first `k` coordinates. -/
def firstReturnAt (i : ι) (k : ℕ) : Set (ℕ → ι) :=
  frestrictLe (π := fun _ : ℕ ↦ ι) k ⁻¹' firstReturnHist i k

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma mem_firstReturnAt (i : ι) (k : ℕ) (ω : ℕ → ι) :
    ω ∈ firstReturnAt i k ↔ ω k = i ∧ ∀ l, 0 < l → l < k → ω l ≠ i := by
  constructor
  · intro h
    exact ⟨h.1, fun l hl hlk ↦ h.2 ⟨l, mem_Iic.2 hlk.le⟩ hl hlk⟩
  · intro h
    first
      | exact And.intro h.1 fun l hl hlk ↦ h.2 l hl hlk
      | exact ⟨h.1, fun l hl hlk ↦ h.2 l hl hlk⟩

lemma measurableSet_firstReturnAt (i : ι) (k : ℕ) : MeasurableSet (firstReturnAt i k) :=
  (measurable_frestrictLe (X := fun _ : ℕ ↦ ι) k) (Set.to_countable _).measurableSet

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
/-- Two first-return events at distinct positive times are disjoint. -/
lemma firstReturnAt_disjoint (i : ι) {k k' : ℕ} (hk : 0 < k) (hk' : 0 < k') (hne : k ≠ k') :
    Disjoint (firstReturnAt i k) (firstReturnAt i k') := by
  refine Set.disjoint_left.2 fun ω h h' ↦ ?_
  rw [mem_firstReturnAt] at h h'
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.2 k hk hlt h.1
  · exact h.2 k' hk' hlt h'.1

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
/-- A trajectory that is at `i` at a positive time `n` has a first return to `i`, at a time
`k + 1 ≤ n`. -/
lemma exists_firstReturn {ω : ℕ → ι} {i : ι} {n : ℕ} (hn : 0 < n) (hω : ω n = i) :
    ∃ k, k + 1 ≤ n ∧ ω ∈ firstReturnAt i (k + 1) := by
  classical
  have hex : ∃ m, 0 < m ∧ ω m = i := ⟨n, hn, hω⟩
  obtain ⟨hpos, hωK⟩ := Nat.find_spec hex
  have hle : Nat.find hex ≤ n := Nat.find_min' hex ⟨hn, hω⟩
  refine ⟨Nat.find hex - 1, by omega, ?_⟩
  have hk : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  rw [hk, mem_firstReturnAt]
  exact ⟨hωK, fun l hl hlK hli ↦ Nat.find_min hex hlK ⟨hl, hli⟩⟩

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
/-- "The chain returns to `i`" is the disjoint union of the first-return events. -/
lemma setOf_return_eq_iUnion (i : ι) :
    {ω : ℕ → ι | ∃ n, 0 < n ∧ ω n = i} = ⋃ k : ℕ, firstReturnAt i (k + 1) := by
  ext ω
  constructor
  · rintro ⟨n, hn, hωn⟩
    obtain ⟨k, -, hk⟩ := exists_firstReturn hn hωn
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  · intro hω
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hω
    exact ⟨k + 1, Nat.succ_pos k, ((mem_firstReturnAt i (k + 1) ω).1 hk).1⟩

lemma measurableSet_visit (i : ι) (m : ℕ) : MeasurableSet {ω : ℕ → ι | ω m = i} := by
  change MeasurableSet ((fun ω : ℕ → ι ↦ ω m) ⁻¹' {i})
  exact (measurable_pi_apply m) (measurableSet_singleton i)

/-- **First-passage decomposition.** The probability of being at `i` at time `n + 1` is the sum
over the first return time `k + 1 ≤ n + 1`:
`ℙ_i(X_{n+1} = i) = ∑_{k ≤ n} ℙ_i(τ_i⁺ = k + 1) · ℙ_i(X_{n-k} = i)`.
Proved from the Markov property at the first return time, an event of the history up to `k + 1`
that forces `X_{k+1} = i`. -/
theorem chainLaw_visit_succ (P : ι → PMF ι) (i : ι) (n : ℕ) :
    chainLaw P i {ω | ω (n + 1) = i}
      = ∑ k ∈ Finset.range (n + 1),
          chainLaw P i (firstReturnAt i (k + 1)) * chainLaw P i {ω | ω (n - k) = i} := by
  have hset : {ω : ℕ → ι | ω (n + 1) = i}
      = ⋃ k ∈ Finset.range (n + 1),
          (firstReturnAt i (k + 1) ∩ shiftBy (k + 1) ⁻¹' {ω | ω (n - k) = i}) := by
    ext ω
    constructor
    · intro hω
      obtain ⟨k, hk, hfr⟩ := exists_firstReturn (Nat.succ_pos n) hω
      refine Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (by omega), Set.mem_inter hfr ?_⟩
      show ω (k + 1 + (n - k)) = i
      rw [show k + 1 + (n - k) = n + 1 by omega]
      exact hω
    · intro hω
      obtain ⟨k, hk, hfr, hshift⟩ := Set.mem_iUnion₂.1 hω
      have hk' := Finset.mem_range.1 hk
      have h2 : ω (k + 1 + (n - k)) = i := hshift
      rw [show k + 1 + (n - k) = n + 1 by omega] at h2
      exact h2
  have hdisj : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint
      (fun k ↦ firstReturnAt i (k + 1) ∩ shiftBy (k + 1) ⁻¹' {ω | ω (n - k) = i}) := by
    intro k _ k' _ hne
    exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left
      (firstReturnAt_disjoint i (k := k + 1) (k' := k' + 1) (by omega) (by omega) (by omega))
  rw [hset, measure_biUnion_finset hdisj fun k _ ↦
    (measurableSet_firstReturnAt i (k + 1)).inter
      (measurable_shiftBy (k + 1) (measurableSet_visit i (n - k)))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact markovPathMeasure_inter_shift (PMF.pure i) P (k + 1) (firstReturnHist i (k + 1))
    (fun h hh ↦ hh.1) (measurableSet_visit i (n - k))

/-! ### The `n`-step return probabilities are matrix powers -/

/-- The trajectories with `X₀ = a` and `X₁ = b`. -/
def stepCylinder (a b : ι) : Set (ℕ → ι) :=
  pathCylinder (fun l ↦ if l = 0 then a else b) 1

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma mem_stepCylinder (a b : ι) (ω : ℕ → ι) : ω ∈ stepCylinder a b ↔ ω 0 = a ∧ ω 1 = b := by
  constructor
  · intro h
    exact ⟨by simpa using h 0 (Nat.zero_le 1), by simpa using h 1 le_rfl⟩
  · rintro ⟨h0, h1⟩ l hl
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simpa using h0
    · simpa using h1

lemma measurableSet_stepCylinder (a b : ι) : MeasurableSet (stepCylinder a b) :=
  measurableSet_pathCylinder _ 1

lemma markovPathMeasure_stepCylinder (P : ι → PMF ι) (a b : ι) :
    markovPathMeasure (PMF.pure a) P (stepCylinder a b) = P a b := by
  unfold stepCylinder
  rw [markovPathMeasure_cylinder]
  simp [PMF.pure_apply_self]

lemma chainLaw_visit_zero [DecidableEq ι] (P : ι → PMF ι) (i j : ι) :
    chainLaw P i {ω | ω 0 = j} = if i = j then 1 else 0 := by
  have hset : {ω : ℕ → ι | ω 0 = j} = pathCylinder (fun _ ↦ j) 0 := by
    ext ω
    constructor
    · intro h k hk
      obtain rfl := Nat.le_zero.1 hk
      exact h
    · intro h
      exact h 0 le_rfl
  rw [hset]
  show markovPathMeasure (PMF.pure i) P (pathCylinder (fun _ ↦ j) 0) = _
  rw [markovPathMeasure_cylinder_zero]
  by_cases h : i = j
  · rw [if_pos h, ← h, PMF.pure_apply_self]
  · rw [if_neg h, PMF.pure_apply_of_ne i j (Ne.symm h)]

/-- The one-step recursion of the marginals, from the Markov property at time `n`. -/
lemma chainLaw_visit_succ_apply [Fintype ι] (P : ι → PMF ι) (i j : ι) (n : ℕ) :
    chainLaw P i {ω | ω (n + 1) = j} = ∑ k, chainLaw P i {ω | ω n = k} * P k j := by
  have hU : {ω : ℕ → ι | ω (n + 1) = j}
      = ⋃ k ∈ (Finset.univ : Finset ι),
          ({ω : ℕ → ι | ω n = k} ∩ shiftBy n ⁻¹' stepCylinder k j) := by
    ext ω
    constructor
    · intro hω
      exact Set.mem_iUnion₂.2 ⟨ω n, Finset.mem_univ _, rfl,
        (mem_stepCylinder (ω n) j (shiftBy n ω)).2 ⟨rfl, hω⟩⟩
    · intro hω
      obtain ⟨k, -, hk1, hk2⟩ := Set.mem_iUnion₂.1 hω
      exact ((mem_stepCylinder k j (shiftBy n ω)).1 hk2).2
  have hdisj : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun k ↦ {ω : ℕ → ι | ω n = k} ∩ shiftBy n ⁻¹' stepCylinder k j) := by
    intro k _ k' _ hne
    refine Set.disjoint_left.2 fun ω h h' ↦ hne ?_
    have e1 : ω n = k := h.1
    have e2 : ω n = k' := h'.1
    exact e1.symm.trans e2
  rw [hU, measure_biUnion_finset hdisj fun k _ ↦
    (measurableSet_visit k n).inter (measurable_shiftBy n (measurableSet_stepCylinder k j))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h := markovPathMeasure_inter_shift (PMF.pure i) P n (j := k)
    {h | h ⟨n, mem_Iic.2 le_rfl⟩ = k} (fun h hh ↦ hh) (measurableSet_stepCylinder k j)
  rw [markovPathMeasure_stepCylinder] at h
  exact h

/-- **The `n`-step transition probabilities are the entries of the matrix power:**
`ℙ_i(X_n = j) = (Pⁿ) i j`, the matrix of one-step probabilities taken over `ℝ≥0∞`. -/
theorem chainLaw_visit_eq_pow [Fintype ι] [DecidableEq ι] (P : ι → PMF ι) (i : ι) (n : ℕ)
    (j : ι) :
    chainLaw P i {ω | ω n = j} = ((Matrix.of fun a b ↦ P a b) ^ n) i j := by
  induction n generalizing j with
  | zero => rw [chainLaw_visit_zero, pow_zero, Matrix.one_apply]
  | succ n ih =>
    rw [chainLaw_visit_succ_apply, pow_succ, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [ih k, Matrix.of_apply]

/-! ### The real transition matrix -/

/-- The transition matrix of the one-step laws `P` as a real matrix, `(P a b).toReal`: the
matrix to which the linear algebra of `FiniteMarkovChain.lean` applies. -/
noncomputable def transitionMatrix [Fintype ι] (P : ι → PMF ι) : Matrix ι ι ℝ :=
  Matrix.of fun a b ↦ (P a b).toReal

lemma transitionMatrix_apply [Fintype ι] (P : ι → PMF ι) (a b : ι) :
    transitionMatrix P a b = (P a b).toReal := rfl

/-- The transition matrix of one-step laws is row-stochastic. -/
lemma transitionMatrix_mem_rowStochastic [Fintype ι] [DecidableEq ι] (P : ι → PMF ι) :
    transitionMatrix P ∈ Matrix.rowStochastic ℝ ι := by
  refine Matrix.mem_rowStochastic_iff_sum.2 ⟨fun a b ↦ ENNReal.toReal_nonneg, fun a ↦ ?_⟩
  simp only [transitionMatrix_apply]
  have h : ∑ b, P a b = 1 := by simpa [tsum_fintype] using PMF.tsum_coe (P a)
  rw [← ENNReal.toReal_sum fun b _ ↦ PMF.apply_ne_top (P a) b, h, ENNReal.toReal_one]

/-- **The `n`-step transition probabilities, as real matrix powers:**
`(ℙ_i(X_n = j)).toReal = (Pⁿ) i j` for the real transition matrix, derived from
`chainLaw_visit_eq_pow` by pushing the `ℝ≥0∞` matrix power through the ring homomorphisms
`ℝ≥0 → ℝ≥0∞` and `ℝ≥0 → ℝ`. -/
theorem chainLaw_visit_toReal_eq_pow [Fintype ι] [DecidableEq ι] (P : ι → PMF ι) (i : ι) (n : ℕ)
    (j : ι) :
    (chainLaw P i {ω | ω n = j}).toReal = (transitionMatrix P ^ n) i j := by
  let N : Matrix ι ι NNReal := Matrix.of fun a b ↦ (P a b).toNNReal
  have h1 : (Matrix.of fun a b ↦ P a b : Matrix ι ι ℝ≥0∞) = ENNReal.ofNNRealHom.mapMatrix N := by
    ext a b
    exact (ENNReal.coe_toNNReal (PMF.apply_ne_top (P a) b)).symm
  have h2 : transitionMatrix P = NNReal.toRealHom.mapMatrix N := by
    ext a b
    rfl
  rw [chainLaw_visit_eq_pow, h1, h2, ← map_pow ENNReal.ofNNRealHom.mapMatrix,
    ← map_pow NNReal.toRealHom.mapMatrix]
  exact ENNReal.coe_toReal _

/-! ### Renewal sequences -/

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
/-- The Cauchy product, for sums in `ℝ≥0∞`. -/
lemma tsum_range_mul_eq (g q : ℕ → ℝ≥0∞) :
    ∑' n, ∑ k ∈ Finset.range (n + 1), g k * q (n - k) = (∑' k, g k) * ∑' n, q n := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ g k * q l]
  symm
  calc (∑' k, g k) * ∑' n, q n = ∑' p : ℕ × ℕ, g p.1 * q p.2 := by
         rw [ENNReal.tsum_prod (f := fun k l ↦ g k * q l)]
         simp_rw [ENNReal.tsum_mul_left]
         rw [ENNReal.tsum_mul_right]
    _ = _ := by
      rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
        (fun p : ℕ × ℕ ↦ g p.1 * q p.2)]
      rw [ENNReal.tsum_sigma']
      apply tsum_congr
      intro n
      rw [tsum_fintype]
      change (∑ p : antidiagonal n, g p.val.1 * q p.val.2) = _
      exact Finset.sum_finset_coe (fun p : ℕ × ℕ ↦ g p.1 * q p.2) (antidiagonal n)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma tsum_eq_one_add_mul (g p : ℕ → ℝ≥0∞) (hp0 : p 0 = 1)
    (hp : ∀ n, p (n + 1) = ∑ k ∈ Finset.range (n + 1), g k * p (n - k)) :
    ∑' n, p n = 1 + (∑' k, g k) * ∑' n, p n :=
  calc ∑' n, p n = p 0 + ∑' n, p (n + 1) := tsum_eq_zero_add' ENNReal.summable
    _ = 1 + ∑' n, ∑ k ∈ Finset.range (n + 1), g k * p (n - k) := by
      rw [hp0, tsum_congr hp]
    _ = 1 + (∑' k, g k) * ∑' n, p n := by rw [tsum_range_mul_eq]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma tsum_le_one_add_mul (g q : ℕ → ℝ≥0∞) (hq0 : q 0 ≤ 1)
    (hq : ∀ n, q (n + 1) ≤ ∑ k ∈ Finset.range (n + 1), g k * q (n - k)) :
    ∑' n, q n ≤ 1 + (∑' k, g k) * ∑' n, q n :=
  calc ∑' n, q n = q 0 + ∑' n, q (n + 1) := tsum_eq_zero_add' ENNReal.summable
    _ ≤ 1 + ∑' n, ∑ k ∈ Finset.range (n + 1), g k * q (n - k) :=
      add_le_add hq0 (ENNReal.tsum_le_tsum hq)
    _ = 1 + (∑' k, g k) * ∑' n, q n := by rw [tsum_range_mul_eq]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
/-- A finite `x` with `x ≤ 1 + F x` and `F < 1` is bounded by `1 / (1 - F)`. -/
lemma le_ofReal_one_div_of_le_add_mul {x F : ℝ≥0∞} (hF : F < 1) (hx : x ≠ ∞)
    (h : x ≤ 1 + F * x) : x ≤ ENNReal.ofReal (1 / (1 - F.toReal)) := by
  have hFne : F ≠ ∞ := ne_top_of_lt hF
  have hFr : F.toReal < 1 := by
    have := (ENNReal.toReal_lt_toReal hFne ENNReal.one_ne_top).2 hF
    rwa [ENNReal.toReal_one] at this
  have hne : 1 + F * x ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hFne hx⟩
  have h' := ENNReal.toReal_mono hne h
  rw [ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.mul_ne_top hFne hx), ENNReal.toReal_mul,
    ENNReal.toReal_one] at h'
  have hb : x.toReal ≤ 1 / (1 - F.toReal) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [h']
  calc x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hb

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
/-- **A renewal criterion.** Let `g` be a sequence of total mass at most one (the first-return
probabilities) and `p` a sequence with `p 0 = 1`, `p ≤ 1` and the renewal equation
`p (n + 1) = ∑_{k ≤ n} g k · p (n - k)`. Then `∑ g = 1` exactly when `∑ p = ∞`. -/
theorem tsum_eq_one_iff_tsum_eq_top_of_renewal (g p : ℕ → ℝ≥0∞) (hg : ∑' k, g k ≤ 1)
    (hp0 : p 0 = 1) (hp1 : ∀ n, p n ≤ 1)
    (hp : ∀ n, p (n + 1) = ∑ k ∈ Finset.range (n + 1), g k * p (n - k)) :
    ∑' k, g k = 1 ↔ ∑' n, p n = ∞ := by
  constructor
  · intro hF
    by_contra hS
    have h := tsum_eq_one_add_mul g p hp0 hp
    rw [hF, one_mul] at h
    have h2 := ENNReal.lt_add_right hS one_ne_zero
    rw [add_comm, ← h] at h2
    exact lt_irrefl _ h2
  · intro hS
    by_contra hF
    have hlt : ∑' k, g k < 1 := lt_of_le_of_ne hg hF
    have hbound : ∑' n, p n ≤ ENNReal.ofReal (1 / (1 - (∑' k, g k).toReal)) := by
      refine ENNReal.tsum_le_of_sum_range_le fun N ↦ ?_
      have hfin : ∑' n, (if n < N then p n else 0) ≠ ∞ := by
        have e : ∑' n, (if n < N then p n else 0)
            = ∑ n ∈ Finset.range N, (if n < N then p n else 0) :=
          tsum_eq_sum fun n hn ↦ if_neg (by simpa using hn)
        rw [e]
        refine ENNReal.sum_ne_top.2 fun n _ ↦ ne_top_of_le_ne_top ENNReal.one_ne_top ?_
        split_ifs
        · exact hp1 n
        · exact zero_le
      have hq : ∀ n, (if n + 1 < N then p (n + 1) else 0)
          ≤ ∑ k ∈ Finset.range (n + 1), g k * (if n - k < N then p (n - k) else 0) := by
        intro n
        by_cases hn : n + 1 < N
        · rw [if_pos hn, hp n]
          refine (Finset.sum_congr rfl fun k hk ↦ ?_).le
          have hlt : n - k < N := by
            have := Finset.mem_range.1 hk
            omega
          rw [if_pos hlt]
        · rw [if_neg hn]
          exact zero_le
      calc ∑ n ∈ Finset.range N, p n
          = ∑ n ∈ Finset.range N, (if n < N then p n else 0) :=
            Finset.sum_congr rfl fun n hn ↦ (if_pos (Finset.mem_range.1 hn)).symm
        _ ≤ ∑' n, (if n < N then p n else 0) := ENNReal.sum_le_tsum _
        _ ≤ _ := le_ofReal_one_div_of_le_add_mul hlt hfin
              (tsum_le_one_add_mul g (fun n ↦ if n < N then p n else 0)
                (by
                  show (if 0 < N then p 0 else 0) ≤ 1
                  split_ifs
                  · exact hp1 0
                  · exact zero_le)
                hq)
    rw [hS] at hbound
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hbound)

/-! ### The recurrence criterion -/

/-- The return probability is the sum of the first-return probabilities. -/
lemma chainLaw_return_eq_tsum (P : ι → PMF ι) (i : ι) :
    chainLaw P i {ω | ∃ n, 0 < n ∧ ω n = i}
      = ∑' k, chainLaw P i (firstReturnAt i (k + 1)) := by
  rw [setOf_return_eq_iUnion]
  exact measure_iUnion
    (fun k k' hne ↦
      firstReturnAt_disjoint i (k := k + 1) (k' := k' + 1) (by omega) (by omega) (by omega))
    fun k ↦ measurableSet_firstReturnAt i (k + 1)

/-- **The recurrence criterion** (Saporito Theorem 1.3.12), for a countable state space. The chain
started at `i` returns to `i` at some time `n > 0` with probability one if and only if its
`n`-step return probabilities `ℙ_i(X_n = i)` have infinite sum. -/
theorem chainLaw_return_eq_one_iff_tsum_eq_top (P : ι → PMF ι) (i : ι) :
    chainLaw P i {ω | ∃ n, 0 < n ∧ ω n = i} = 1 ↔
      ∑' n, chainLaw P i {ω | ω n = i} = ∞ := by
  classical
  have hg : ∑' k, chainLaw P i (firstReturnAt i (k + 1)) ≤ 1 := by
    rw [← chainLaw_return_eq_tsum]
    exact prob_le_one
  have hp0 : chainLaw P i {ω | ω 0 = i} = 1 := by
    rw [chainLaw_visit_zero, if_pos rfl]
  rw [chainLaw_return_eq_tsum]
  exact tsum_eq_one_iff_tsum_eq_top_of_renewal
    (fun k ↦ chainLaw P i (firstReturnAt i (k + 1))) (fun n ↦ chainLaw P i {ω | ω n = i})
    hg hp0 (fun n ↦ prob_le_one) (chainLaw_visit_succ P i)

/-- The recurrence criterion on a finite state space, with the `n`-step return probabilities
written as matrix powers: `ℙ_i(τ_i⁺ < ∞) = 1 ↔ ∑ₙ (Pⁿ) i i = ∞`. -/
theorem chainLaw_return_eq_one_iff [Fintype ι] [DecidableEq ι] (P : ι → PMF ι) (i : ι) :
    chainLaw P i {ω | ∃ n, 0 < n ∧ ω n = i} = 1 ↔
      ∑' n, ((Matrix.of fun a b ↦ P a b) ^ n) i i = ∞ := by
  have hsum : ∑' n, ((Matrix.of fun a b ↦ P a b) ^ n) i i
      = ∑' n, chainLaw P i {ω | ω n = i} :=
    tsum_congr fun n ↦ (chainLaw_visit_eq_pow P i n i).symm
  rw [hsum]
  exact chainLaw_return_eq_one_iff_tsum_eq_top P i

/-- **The transient half of the dichotomy.** If `∑ₙ ℙ_i(X_n = i) < ∞`, the chain started at `i`
visits `i` infinitely often with probability zero (the first Borel–Cantelli lemma). -/
theorem chainLaw_visits_infinitely_often_null (P : ι → PMF ι) (i : ι)
    (h : ∑' n, chainLaw P i {ω | ω n = i} ≠ ∞) :
    chainLaw P i (Filter.limsup (fun n ↦ {ω : ℕ → ι | ω n = i}) Filter.atTop) = 0 :=
  measure_limsup_atTop_eq_zero h

/-! ### The recurrent half: the number of returns -/

/-- The trajectories with at least `k` returns to `i`: after the first return at time `m + 1`, the
shifted trajectory has at least `k - 1` returns. -/
def returnsAtLeast (i : ι) : ℕ → Set (ℕ → ι)
  | 0 => Set.univ
  | k + 1 => ⋃ m : ℕ, firstReturnAt i (m + 1) ∩ shiftBy (m + 1) ⁻¹' returnsAtLeast i k

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma returnsAtLeast_succ (i : ι) (k : ℕ) :
    returnsAtLeast i (k + 1)
      = ⋃ m : ℕ, firstReturnAt i (m + 1) ∩ shiftBy (m + 1) ⁻¹' returnsAtLeast i k := rfl

lemma measurableSet_returnsAtLeast (i : ι) (k : ℕ) : MeasurableSet (returnsAtLeast i k) := by
  induction k with
  | zero => exact MeasurableSet.univ
  | succ k ih =>
    rw [returnsAtLeast_succ]
    exact MeasurableSet.iUnion fun m ↦
      (measurableSet_firstReturnAt i (m + 1)).inter (measurable_shiftBy (m + 1) ih)

/-- **The number of returns is geometric** (strong Markov at the first return time, in its
fixed-time form): `ℙ_i(at least k + 1 returns) = f · ℙ_i(at least k returns)`, where
`f = ∑ₘ ℙ_i(τ_i⁺ = m + 1)` is the return probability. -/
lemma chainLaw_returnsAtLeast_succ (P : ι → PMF ι) (i : ι) (k : ℕ) :
    chainLaw P i (returnsAtLeast i (k + 1))
      = (∑' m, chainLaw P i (firstReturnAt i (m + 1))) * chainLaw P i (returnsAtLeast i k) := by
  rw [returnsAtLeast_succ, measure_iUnion
    (fun m m' hne ↦ Disjoint.mono Set.inter_subset_left Set.inter_subset_left
      (firstReturnAt_disjoint i (k := m + 1) (k' := m' + 1) (by omega) (by omega) (by omega)))
    fun m ↦ (measurableSet_firstReturnAt i (m + 1)).inter
      (measurable_shiftBy (m + 1) (measurableSet_returnsAtLeast i k)),
    ← ENNReal.tsum_mul_right]
  exact tsum_congr fun m ↦
    markovPathMeasure_inter_shift (PMF.pure i) P (m + 1) (firstReturnHist i (m + 1))
      (fun h hh ↦ hh.1) (measurableSet_returnsAtLeast i k)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma exists_ge_of_mem_returnsAtLeast {i : ι} {k : ℕ} {ω : ℕ → ι}
    (h : ω ∈ returnsAtLeast i k) : ∃ n, k ≤ n ∧ (0 < k → ω n = i) := by
  induction k generalizing ω with
  | zero => exact ⟨0, le_rfl, fun h0 ↦ absurd h0 (lt_irrefl 0)⟩
  | succ k ih =>
    rw [returnsAtLeast_succ] at h
    obtain ⟨m, hfr, hsh⟩ := Set.mem_iUnion.1 h
    obtain ⟨n', hn', hk'⟩ := ih hsh
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨m + 1, by omega, fun _ ↦ ((mem_firstReturnAt i (m + 1) ω).1 hfr).1⟩
    · exact ⟨m + 1 + n', by omega, fun _ ↦ hk' hk0⟩

/-- **The recurrent half of the dichotomy.** If the chain started at `i` returns to `i` with
probability one, it visits `i` infinitely often with probability one. -/
theorem chainLaw_visits_infinitely_often_eq_one (P : ι → PMF ι) (i : ι)
    (hret : chainLaw P i {ω | ∃ n, 0 < n ∧ ω n = i} = 1) :
    chainLaw P i (Filter.limsup (fun n ↦ {ω : ℕ → ι | ω n = i}) Filter.atTop) = 1 := by
  have hk : ∀ k, chainLaw P i (returnsAtLeast i k) = 1 := by
    intro k
    induction k with
    | zero => exact measure_univ
    | succ k ih =>
      rw [chainLaw_returnsAtLeast_succ, ← chainLaw_return_eq_tsum, hret, ih, one_mul]
  have hmeas : MeasurableSet (⋂ k : ℕ, returnsAtLeast i (k + 1)) :=
    MeasurableSet.iInter fun k ↦ measurableSet_returnsAtLeast i (k + 1)
  have h1 : chainLaw P i (⋂ k : ℕ, returnsAtLeast i (k + 1)) = 1 := by
    refine (prob_compl_eq_zero_iff hmeas).1 ?_
    rw [Set.compl_iInter]
    exact measure_iUnion_null fun k ↦
      (prob_compl_eq_zero_iff (measurableSet_returnsAtLeast i (k + 1))).2 (hk (k + 1))
  have hsub : (⋂ k : ℕ, returnsAtLeast i (k + 1))
      ⊆ Filter.limsup (fun n ↦ {ω : ℕ → ι | ω n = i}) Filter.atTop := by
    intro ω hω
    rw [Filter.mem_limsup_iff_frequently_mem, Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, hωn⟩ := exists_ge_of_mem_returnsAtLeast (Set.mem_iInter.1 hω N)
    exact ⟨n, by omega, hωn (Nat.succ_pos N)⟩
  exact le_antisymm prob_le_one (h1.symm.le.trans (measure_mono hsub))

/-- **The 0–1 law for visits to a state.** The chain started at `i` visits `i` infinitely often
with probability one if `∑ₙ ℙ_i(X_n = i) = ∞`, and with probability zero otherwise. -/
theorem chainLaw_visits_infinitely_often_eq_one_iff (P : ι → PMF ι) (i : ι) :
    chainLaw P i (Filter.limsup (fun n ↦ {ω : ℕ → ι | ω n = i}) Filter.atTop) = 1 ↔
      ∑' n, chainLaw P i {ω | ω n = i} = ∞ := by
  constructor
  · intro h
    by_contra hS
    have := chainLaw_visits_infinitely_often_null P i hS
    rw [this] at h
    exact zero_ne_one h
  · intro hS
    exact chainLaw_visits_infinitely_often_eq_one P i
      ((chainLaw_return_eq_one_iff_tsum_eq_top P i).2 hS)

end MathFin
