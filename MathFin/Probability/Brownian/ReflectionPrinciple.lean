/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.BrownianMarkov
public import MathFin.Probability.Gaussian.GaussianMoments
public import BrownianMotion.Gaussian.BrownianMotion

/-!
# The reflection principle for Brownian motion

For a Brownian motion `B` and levels `a > 0`,

  `P(B_s ≥ a for some s ∈ [0, t]) = 2 · P(B_t ≥ a)`.

The proof is the reflection argument on a grid of mesh `τ = t/n`, then a limit as `n → ∞`; it
needs only the simple Markov property at *fixed* grid times (`shift_indep_natural`) and the
symmetry of the Gaussian law, not the strong Markov property.

On the grid `S_k = B_{kτ}`, let `E_k` be the event that `k` is the first grid index with
`S_k ≥ a`. The events `E_0, …, E_n` are disjoint, lie in the natural σ-algebra at time `kτ`, and
their union is the grid event `H_n = {max_{k ≤ n} S_k ≥ a}`. The increment `Z_k = S_n − S_k` is
independent of `E_k` and symmetric, so `P(F ∩ {Z_k < −c}) = P(F ∩ {Z_k > c})` for every
`F ∈ 𝓕_{kτ}` (`reflect`).

* *Upper bound.* On `E_k`, `S_k ≥ a`, so `{S_n < a} ⊆ {Z_k < 0}`, and reflecting,
  `P(E_k ∩ {S_n < a}) ≤ P(E_k ∩ {Z_k > 0}) ≤ P(E_k ∩ {S_n > a})`. Summing over the disjoint
  `E_k`: `P(H_n) ≤ P(S_n ≥ a) + P(S_n > a)`.
* *Lower bound.* The overshoot `S_k − a` at the first passage is at most `δ` unless some grid
  increment exceeds `δ`, an event of probability at most `n · 3τ²/δ⁴ = 3t²/(nδ⁴) → 0` by Markov's
  inequality for the fourth moment. On the good event, reflecting at `δ` gives
  `P(S_n ≥ a) + P(S_n > a + 2δ) ≤ P(H_n) + P(bad)`.

Continuity of paths then passes to `n → ∞` (the grid maximum increases to the maximum over
`[0, t]`, up to the level shift `ε`), and the absence of atoms of the Gaussian law removes the
shifts `ε, δ`.

## Main results

* `measure_exists_grid_le`: the grid inequality `P(H_n) ≤ P(S_n ≥ a) + P(S_n > a)`
* `measure_ge_add_le`: the grid inequality `P(S_n ≥ a) + P(S_n > a + 2δ) ≤ P(H_n) + P(bad)`
* `ProbabilityTheory.IsBrownianReal.reflection_principle`: the reflection principle
  `P(∃ s ≤ t, a ≤ B_s) = 2 · P(a ≤ B_t)` for `a > 0`

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 5.1.7
* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  §2.6

## Tags

reflection principle, running maximum, Brownian motion, first passage, Markov property, MSC 60J65
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

section Gaussian

/-- **Fourth-moment tail bound.** `N(0, v)(x > δ) ≤ 3v²/δ⁴` (Markov's inequality for `x ↦ x⁴`). -/
theorem gaussianReal_Ioi_le (v : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    gaussianReal 0 v (Set.Ioi δ) ≤ ENNReal.ofReal (3 * (v : ℝ) ^ 2 / δ ^ 4) := by
  have hM : δ ^ 4 * (gaussianReal 0 v).real {x : ℝ | δ ^ 4 ≤ x ^ 4} ≤ 3 * (v : ℝ) ^ 2 :=
    (mul_meas_ge_le_integral_of_nonneg (μ := gaussianReal 0 v) (f := fun x : ℝ ↦ x ^ 4)
      (ae_of_all _ fun x ↦ (by positivity : (0 : ℝ) ≤ x ^ 4)) (integrable_pow4_gaussianReal v)
      (δ ^ 4)).trans_eq (integral_pow4_gaussianReal v)
  have hsub : Set.Ioi δ ⊆ {x : ℝ | δ ^ 4 ≤ x ^ 4} := fun x hx ↦
    pow_le_pow_left₀ hδ.le (le_of_lt hx) 4
  calc gaussianReal 0 v (Set.Ioi δ) ≤ gaussianReal 0 v {x : ℝ | δ ^ 4 ≤ x ^ 4} :=
        measure_mono hsub
    _ = ENNReal.ofReal ((gaussianReal 0 v).real {x : ℝ | δ ^ 4 ≤ x ^ 4}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (3 * (v : ℝ) ^ 2 / δ ^ 4) :=
        ENNReal.ofReal_le_ofReal ((le_div_iff₀ (by positivity)).2 (by linarith))

/-- **Symmetry of the centred Gaussian law**: `N(0, v)(x < −c) = N(0, v)(x > c)`. -/
theorem gaussianReal_Iio_neg (v : ℝ≥0) (c : ℝ) :
    gaussianReal 0 v (Set.Iio (-c)) = gaussianReal 0 v (Set.Ioi c) := by
  have h := gaussianReal_map_neg (μ := 0) (v := v)
  rw [neg_zero] at h
  calc gaussianReal 0 v (Set.Iio (-c))
      = gaussianReal 0 v ((fun x : ℝ ↦ -x) ⁻¹' Set.Ioi c) := by
        congr 1
        ext x
        simp only [Set.mem_Iio, Set.mem_preimage, Set.mem_Ioi]
        constructor <;> intro hx <;> linarith
    _ = (gaussianReal 0 v).map (fun x : ℝ ↦ -x) (Set.Ioi c) :=
        (Measure.map_apply measurable_neg measurableSet_Ioi).symm
    _ = gaussianReal 0 v (Set.Ioi c) := by rw [h]

end Gaussian

section GridEvents

/-- The first-passage event on the grid `ℕ τ`: `k` is the first index with `X (kτ) ≥ a`. -/
private def firstHit (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (a : ℝ) (k : ℕ) : Set Ω :=
  (⋂ j ∈ Finset.range k, X ((j : ℝ≥0) * τ) ⁻¹' Set.Iio a) ∩ X ((k : ℝ≥0) * τ) ⁻¹' Set.Ici a

private lemma mem_firstHit {τ : ℝ≥0} {a : ℝ} {k : ℕ} {ω : Ω} :
    ω ∈ firstHit X τ a k ↔ (∀ j < k, X ((j : ℝ≥0) * τ) ω < a) ∧ a ≤ X ((k : ℝ≥0) * τ) ω := by
  simp [firstHit]

/-- A section `X s` with `s ≤ t` is measurable for the natural σ-algebra at time `t`. -/
private lemma measurable_natural_of_le (hm : ∀ t, Measurable (X t)) {s t : ℝ≥0} (hst : s ≤ t) :
    Measurable[Filtration.natural X (fun u ↦ (hm u).stronglyMeasurable) t] (X s) :=
  Measurable.of_comap_le
    (le_iSup₂ (f := fun j (_ : j ≤ t) ↦ MeasurableSpace.comap (X j) inferInstance) s hst)

private lemma measurableSet_natural_firstHit (hm : ∀ t, Measurable (X t)) (τ : ℝ≥0) (a : ℝ)
    (k : ℕ) :
    MeasurableSet[Filtration.natural X (fun u ↦ (hm u).stronglyMeasurable) ((k : ℝ≥0) * τ)]
      (firstHit X τ a k) := by
  refine MeasurableSet.inter (Finset.measurableSet_biInter _ fun j hj ↦ ?_) ?_
  · exact (measurable_natural_of_le hm (mul_le_mul_of_nonneg_right
      (Nat.cast_le.2 (Finset.mem_range.1 hj).le) zero_le)) measurableSet_Iio
  · exact (measurable_natural_of_le hm le_rfl) measurableSet_Ici

private lemma measurableSet_firstHit (hm : ∀ t, Measurable (X t)) (τ : ℝ≥0) (a : ℝ) (k : ℕ) :
    MeasurableSet (firstHit X τ a k) :=
  ((Filtration.natural X (fun u ↦ (hm u).stronglyMeasurable)).le _) _
    (measurableSet_natural_firstHit hm τ a k)

private lemma disjoint_firstHit (τ : ℝ≥0) (a : ℝ) {k l : ℕ} (hkl : k < l) :
    Disjoint (firstHit X τ a k) (firstHit X τ a l) := by
  rw [Set.disjoint_left]
  intro ω hk hl
  rw [mem_firstHit] at hk hl
  exact absurd hk.2 (not_le.2 (hl.1 k hkl))

private lemma pairwiseDisjoint_firstHit (τ : ℝ≥0) (a : ℝ) (s : Finset ℕ) :
    (↑s : Set ℕ).PairwiseDisjoint (firstHit X τ a) := fun k _ l _ hkl ↦ by
  rcases lt_or_gt_of_ne hkl with h | h
  · exact disjoint_firstHit τ a h
  · exact (disjoint_firstHit τ a h).symm

/-- The first-passage events cover the grid event `{∃ k ≤ n, a ≤ X (kτ)}`. -/
private lemma biUnion_firstHit (τ : ℝ≥0) (a : ℝ) (n : ℕ) :
    (⋃ k ∈ Finset.range (n + 1), firstHit X τ a k)
      = {ω | ∃ k ≤ n, a ≤ X ((k : ℝ≥0) * τ) ω} := by
  classical
  ext ω
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq, exists_prop, mem_firstHit]
  constructor
  · rintro ⟨k, hk, -, hak⟩
    exact ⟨k, Nat.lt_succ_iff.1 hk, hak⟩
  · rintro ⟨k₀, hk₀, hak₀⟩
    have hex : ∃ k : ℕ, a ≤ X ((k : ℝ≥0) * τ) ω := ⟨k₀, hak₀⟩
    exact ⟨Nat.find hex, Nat.lt_succ_of_le ((Nat.find_min' hex hak₀).trans hk₀),
      fun j hj ↦ not_le.1 (Nat.find_min hex hj), Nat.find_spec hex⟩

/-- A family of measurable sets inside the first-passage events has additive measure. -/
private lemma measure_biUnion_firstHit {τ : ℝ≥0} {a : ℝ} {f : ℕ → Set Ω}
    (hf : ∀ k, f k ⊆ firstHit X τ a k) (hmeas : ∀ k, MeasurableSet (f k)) (n : ℕ) :
    P (⋃ k ∈ Finset.range (n + 1), f k) = ∑ k ∈ Finset.range (n + 1), P (f k) :=
  measure_biUnion_finset ((pairwiseDisjoint_firstHit τ a _).mono hf) fun k _ ↦ hmeas k

private lemma sum_firstHit_inter_le (hm : ∀ t, Measurable (X t)) (τ : ℝ≥0) (a : ℝ) (n : ℕ)
    {G : Set Ω} (hG : MeasurableSet G) :
    ∑ k ∈ Finset.range (n + 1), P (firstHit X τ a k ∩ G) ≤ P G := by
  refine (measure_biUnion_firstHit (f := fun k ↦ firstHit X τ a k ∩ G)
    (fun k ↦ Set.inter_subset_left)
    (fun k ↦ (measurableSet_firstHit hm τ a k).inter hG) n).symm.trans_le ?_
  exact measure_mono (Set.iUnion₂_subset fun k _ ↦ Set.inter_subset_right)

end GridEvents

section Reflection

/-- **Independence at a fixed time.** For `F ∈ σ(X_u : u ≤ t₀)`, the event `F` is independent of
the Brownian increment `X (t₀ + d) − X t₀ ~ N(0, d)`. -/
private lemma measure_inter_increment (hX : IsPreBrownianReal X P) (hm : ∀ t, Measurable (X t))
    (t₀ d : ℝ≥0) {F : Set Ω}
    (hF : MeasurableSet[Filtration.natural X (fun u ↦ (hm u).stronglyMeasurable) t₀] F)
    {S : Set ℝ} (hS : MeasurableSet S) :
    P (F ∩ {ω | X (t₀ + d) ω - X t₀ ω ∈ S}) = P F * gaussianReal 0 d S := by
  have hI := (Indep_iff _ _ _).1 (shift_indep_natural hX hm t₀)
  have hT : MeasurableSet[MeasurableSpace.comap
      (fun ω (t : ℝ≥0) ↦ X (t₀ + t) ω - X t₀ ω) inferInstance]
      {ω | X (t₀ + d) ω - X t₀ ω ∈ S} :=
    ⟨(fun f : ℝ≥0 → ℝ ↦ f d) ⁻¹' S, measurable_pi_apply d hS, rfl⟩
  have hlaw : P {ω | X (t₀ + d) ω - X t₀ ω ∈ S} = gaussianReal 0 d S := by
    have h := hasLaw_increment hX (s := t₀) (t := t₀ + d) le_self_add
    rw [add_tsub_cancel_left] at h
    exact h.measure_eq (p := (· ∈ S)) hS
  rw [Set.inter_comm, hI _ _ hT hF, hlaw, mul_comm]

/-- **The reflection step.** For `F ∈ σ(X_u : u ≤ t₀)`, reflecting the future increment
`X (t₀ + d) − X t₀` leaves `P(F ∩ ·)` unchanged: `P(F ∩ {Z < −c}) = P(F ∩ {Z > c})`. -/
private lemma reflect (hX : IsPreBrownianReal X P) (hm : ∀ t, Measurable (X t)) (t₀ d : ℝ≥0)
    {F : Set Ω}
    (hF : MeasurableSet[Filtration.natural X (fun u ↦ (hm u).stronglyMeasurable) t₀] F) (c : ℝ) :
    P (F ∩ {ω | X (t₀ + d) ω - X t₀ ω < -c}) = P (F ∩ {ω | c < X (t₀ + d) ω - X t₀ ω}) := by
  have h1 := measure_inter_increment hX hm t₀ d hF (S := Set.Iio (-c)) measurableSet_Iio
  have h2 := measure_inter_increment hX hm t₀ d hF (S := Set.Ioi c) measurableSet_Ioi
  rw [gaussianReal_Iio_neg] at h1
  exact h1.trans h2.symm

/-- The reflection step between the grid times `kτ ≤ nτ`. -/
private lemma reflect_grid (hX : IsPreBrownianReal X P) (hm : ∀ t, Measurable (X t)) (τ : ℝ≥0)
    {n k : ℕ} (hk : k ≤ n) {F : Set Ω}
    (hF : MeasurableSet[Filtration.natural X (fun u ↦ (hm u).stronglyMeasurable)
      ((k : ℝ≥0) * τ)] F) (c : ℝ) :
    P (F ∩ {ω | X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω < -c})
      = P (F ∩ {ω | c < X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω}) := by
  have hsum : (k : ℝ≥0) * τ + ((n - k : ℕ) : ℝ≥0) * τ = (n : ℝ≥0) * τ := by
    rw [← add_mul, ← Nat.cast_add, Nat.add_sub_of_le hk]
  have h := reflect hX hm ((k : ℝ≥0) * τ) (((n - k : ℕ) : ℝ≥0) * τ) hF c
  rwa [hsum] at h

end Reflection

section Discrete

/-- **The grid inequality (Lévy).** `P(max_{k ≤ n} X (kτ) ≥ a) ≤ P(X (nτ) ≥ a) + P(X (nτ) > a)`. -/
theorem measure_exists_grid_le (hX : IsPreBrownianReal X P) (hm : ∀ t, Measurable (X t))
    (τ : ℝ≥0) (n : ℕ) (a : ℝ) :
    P {ω | ∃ k ≤ n, a ≤ X ((k : ℝ≥0) * τ) ω}
      ≤ P {ω | a ≤ X ((n : ℝ≥0) * τ) ω} + P {ω | a < X ((n : ℝ≥0) * τ) ω} := by
  have hG₁ : MeasurableSet {ω | a ≤ X ((n : ℝ≥0) * τ) ω} := measurableSet_le measurable_const (hm _)
  have hG₂ : MeasurableSet {ω | a < X ((n : ℝ≥0) * τ) ω} := measurableSet_lt measurable_const (hm _)
  have hk : ∀ k ∈ Finset.range (n + 1), P (firstHit X τ a k)
      ≤ P (firstHit X τ a k ∩ {ω | a ≤ X ((n : ℝ≥0) * τ) ω})
        + P (firstHit X τ a k ∩ {ω | a < X ((n : ℝ≥0) * τ) ω}) := by
    intro k hkn
    have hkn' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hkn)
    calc P (firstHit X τ a k)
        ≤ P (firstHit X τ a k ∩ {ω | a ≤ X ((n : ℝ≥0) * τ) ω})
          + P (firstHit X τ a k \ {ω | a ≤ X ((n : ℝ≥0) * τ) ω}) :=
          measure_le_inter_add_sdiff _ _ _
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          calc P (firstHit X τ a k \ {ω | a ≤ X ((n : ℝ≥0) * τ) ω})
              ≤ P (firstHit X τ a k ∩ {ω | X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω < -0}) := by
                refine measure_mono fun ω ⟨hE, hG⟩ ↦ ⟨hE, ?_⟩
                have h1 : ¬ a ≤ X ((n : ℝ≥0) * τ) ω := hG
                have h2 := (mem_firstHit.1 hE).2
                show X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω < -0
                rw [neg_zero]
                linarith [not_le.1 h1]
            _ = P (firstHit X τ a k ∩ {ω | 0 < X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω}) :=
                reflect_grid hX hm τ hkn' (measurableSet_natural_firstHit hm τ a k) 0
            _ ≤ P (firstHit X τ a k ∩ {ω | a < X ((n : ℝ≥0) * τ) ω}) := by
                refine measure_mono fun ω ⟨hE, hZ⟩ ↦ ⟨hE, ?_⟩
                have h2 := (mem_firstHit.1 hE).2
                have hZ' : 0 < X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω := hZ
                show a < X ((n : ℝ≥0) * τ) ω
                linarith
  calc P {ω | ∃ k ≤ n, a ≤ X ((k : ℝ≥0) * τ) ω}
      = P (⋃ k ∈ Finset.range (n + 1), firstHit X τ a k) := by rw [biUnion_firstHit]
    _ ≤ ∑ k ∈ Finset.range (n + 1), P (firstHit X τ a k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          (P (firstHit X τ a k ∩ {ω | a ≤ X ((n : ℝ≥0) * τ) ω})
            + P (firstHit X τ a k ∩ {ω | a < X ((n : ℝ≥0) * τ) ω})) := Finset.sum_le_sum hk
    _ = ∑ k ∈ Finset.range (n + 1), P (firstHit X τ a k ∩ {ω | a ≤ X ((n : ℝ≥0) * τ) ω})
          + ∑ k ∈ Finset.range (n + 1), P (firstHit X τ a k ∩ {ω | a < X ((n : ℝ≥0) * τ) ω}) :=
        Finset.sum_add_distrib
    _ ≤ _ := add_le_add (sum_firstHit_inter_le hm τ a n hG₁) (sum_firstHit_inter_le hm τ a n hG₂)

/-- The probability that some grid increment exceeds `δ`, or the path starts above `a`, is at
most `n · 3τ²/δ⁴`. -/
private lemma measure_bad_le (hX : IsPreBrownianReal X P) (τ : ℝ≥0) (n : ℕ) {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) :
    P ({ω | a ≤ X (((0 : ℕ) : ℝ≥0) * τ) ω}
        ∪ ⋃ j ∈ Finset.range n,
          {ω | δ < X (((j + 1 : ℕ) : ℝ≥0) * τ) ω - X ((j : ℝ≥0) * τ) ω})
      ≤ n * ENNReal.ofReal (3 * (τ : ℝ) ^ 2 / δ ^ 4) := by
  have h0 : P {ω | a ≤ X (((0 : ℕ) : ℝ≥0) * τ) ω} = 0 := by
    refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.1 hX.eval_zero_ae_eq_zero)
    show ¬ X 0 ω = 0
    intro h
    have hω' : a ≤ X (((0 : ℕ) : ℝ≥0) * τ) ω := hω
    rw [Nat.cast_zero, zero_mul, h] at hω'
    linarith
  have hj : ∀ j ∈ Finset.range n,
      P {ω | δ < X (((j + 1 : ℕ) : ℝ≥0) * τ) ω - X ((j : ℝ≥0) * τ) ω}
        ≤ ENNReal.ofReal (3 * (τ : ℝ) ^ 2 / δ ^ 4) := by
    intro j _
    have hst : (j : ℝ≥0) * τ ≤ ((j + 1 : ℕ) : ℝ≥0) * τ :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_succ j)) zero_le
    have hv : ((j + 1 : ℕ) : ℝ≥0) * τ - (j : ℝ≥0) * τ = τ := by
      rw [Nat.cast_succ, add_mul, one_mul, add_tsub_cancel_left]
    have h := hasLaw_increment hX hst
    rw [hv] at h
    exact ((h.measure_eq (p := fun x ↦ δ < x) measurableSet_Ioi).trans_le
      (gaussianReal_Ioi_le τ hδ))
  calc _ ≤ P {ω | a ≤ X (((0 : ℕ) : ℝ≥0) * τ) ω}
        + P (⋃ j ∈ Finset.range n,
          {ω | δ < X (((j + 1 : ℕ) : ℝ≥0) * τ) ω - X ((j : ℝ≥0) * τ) ω}) := measure_union_le _ _
    _ ≤ 0 + ∑ j ∈ Finset.range n,
          P {ω | δ < X (((j + 1 : ℕ) : ℝ≥0) * τ) ω - X ((j : ℝ≥0) * τ) ω} :=
        add_le_add h0.le (measure_biUnion_finset_le _ _)
    _ ≤ 0 + ∑ j ∈ Finset.range n, ENNReal.ofReal (3 * (τ : ℝ) ^ 2 / δ ^ 4) :=
        add_le_add le_rfl (Finset.sum_le_sum hj)
    _ = n * ENNReal.ofReal (3 * (τ : ℝ) ^ 2 / δ ^ 4) := by
        rw [zero_add, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The overshoot grid inequality.** At the first grid passage of `a > 0` the overshoot is at
most `δ` unless some grid increment exceeds `δ`; reflecting at `δ` gives
`P(X (nτ) ≥ a) + P(X (nτ) > a + 2δ) ≤ P(max_{k ≤ n} X (kτ) ≥ a) + n · 3τ²/δ⁴`. -/
theorem measure_ge_add_le (hX : IsPreBrownianReal X P) (hm : ∀ t, Measurable (X t))
    (τ : ℝ≥0) (n : ℕ) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    P {ω | a ≤ X ((n : ℝ≥0) * τ) ω} + P {ω | a + 2 * δ < X ((n : ℝ≥0) * τ) ω}
      ≤ P {ω | ∃ k ≤ n, a ≤ X ((k : ℝ≥0) * τ) ω}
        + n * ENNReal.ofReal (3 * (τ : ℝ) ^ 2 / δ ^ 4) := by
  classical
  have hG₁ : MeasurableSet {ω | a ≤ X ((n : ℝ≥0) * τ) ω} := measurableSet_le measurable_const (hm _)
  -- the sets `W k`: first passage at `k` with overshoot at most `δ`
  let W : ℕ → Set Ω := fun k ↦ firstHit X τ a k ∩ X ((k : ℝ≥0) * τ) ⁻¹' Set.Iic (a + δ)
  have hWn : ∀ k : ℕ, MeasurableSet[Filtration.natural X (fun u ↦ (hm u).stronglyMeasurable)
      ((k : ℝ≥0) * τ)] (W k) := fun k ↦
    (measurableSet_natural_firstHit hm τ a k).inter
      ((measurable_natural_of_le hm le_rfl) measurableSet_Iic)
  have hW : ∀ k, MeasurableSet (W k) := fun k ↦
    ((Filtration.natural X (fun u ↦ (hm u).stronglyMeasurable)).le _) _ (hWn k)
  have hWE : ∀ k, W k ⊆ firstHit X τ a k := fun k ↦ Set.inter_subset_left
  -- the bad event
  let Bad : Set Ω := {ω | a ≤ X (((0 : ℕ) : ℝ≥0) * τ) ω}
    ∪ ⋃ j ∈ Finset.range n,
      {ω | δ < X (((j + 1 : ℕ) : ℝ≥0) * τ) ω - X ((j : ℝ≥0) * τ) ω}
  -- (1) `P H = P G₁ + P (H \ G₁)`
  have hdecomp : P {ω | a ≤ X ((n : ℝ≥0) * τ) ω}
      + P ({ω | ∃ k ≤ n, a ≤ X ((k : ℝ≥0) * τ) ω} \ {ω | a ≤ X ((n : ℝ≥0) * τ) ω})
      = P {ω | ∃ k ≤ n, a ≤ X ((k : ℝ≥0) * τ) ω} := by
    have h := measure_inter_add_sdiff
      {ω | ∃ k ≤ n, a ≤ X ((k : ℝ≥0) * τ) ω} (μ := P) hG₁
    rwa [Set.inter_eq_right.2 fun ω hω ↦ ⟨n, le_rfl, hω⟩] at h
  -- (2) reflected pieces fit inside `H \ G₁`
  have hRefl : ∑ k ∈ Finset.range (n + 1),
        P (W k ∩ {ω | X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω < -δ})
      ≤ P ({ω | ∃ k ≤ n, a ≤ X ((k : ℝ≥0) * τ) ω} \ {ω | a ≤ X ((n : ℝ≥0) * τ) ω}) := by
    refine (measure_biUnion_firstHit (f := fun k ↦
        W k ∩ {ω | X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω < -δ})
      (fun k ↦ Set.inter_subset_left.trans (hWE k))
      (fun k ↦ (hW k).inter
        (measurableSet_lt ((hm _).sub (hm _)) measurable_const)) n).symm.trans_le ?_
    refine measure_mono (Set.iUnion₂_subset fun k hk ↦ ?_)
    rintro ω ⟨⟨hE, hle⟩, hZ⟩
    have hE' := mem_firstHit.1 hE
    have hle' : X ((k : ℝ≥0) * τ) ω ≤ a + δ := hle
    have hZ' : X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω < -δ := hZ
    refine ⟨?_, ?_⟩
    · exact ⟨k, Nat.lt_succ_iff.1 (Finset.mem_range.1 hk), hE'.2⟩
    · show ¬ a ≤ X ((n : ℝ≥0) * τ) ω
      intro h
      linarith
  -- (3) the unreflected pieces cover the good part of `G₂`
  have hCover : {ω | a + 2 * δ < X ((n : ℝ≥0) * τ) ω} \ Bad
      ⊆ ⋃ k ∈ Finset.range (n + 1),
        W k ∩ {ω | δ < X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω} := by
    intro ω ⟨hG, hB⟩
    have hG' : a + 2 * δ < X ((n : ℝ≥0) * τ) ω := hG
    have hS0 : X (((0 : ℕ) : ℝ≥0) * τ) ω < a := by
      by_contra h
      exact hB ((Set.mem_union _ _ _).2 (Or.inl (not_lt.1 h)))
    have hinc : ∀ j < n, X (((j + 1 : ℕ) : ℝ≥0) * τ) ω - X ((j : ℝ≥0) * τ) ω ≤ δ := by
      intro j hj
      by_contra h
      exact hB (Set.mem_union_right _ (Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hj, not_le.1 h⟩))
    have hex : ∃ k : ℕ, a ≤ X ((k : ℝ≥0) * τ) ω := ⟨n, by linarith⟩
    obtain ⟨k, hk_spec, hk_min, hkn⟩ : ∃ k : ℕ, a ≤ X ((k : ℝ≥0) * τ) ω
        ∧ (∀ j < k, X ((j : ℝ≥0) * τ) ω < a) ∧ k ≤ n :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj ↦ not_le.1 (Nat.find_min hex hj),
        Nat.find_min' hex (by linarith)⟩
    rcases k with _ | j
    · exact absurd hk_spec (not_le.2 hS0)
    · have hSj := hk_min j (Nat.lt_succ_self j)
      have hincj := hinc j (Nat.lt_of_succ_le hkn)
      refine Set.mem_iUnion₂.2 ⟨j + 1, Finset.mem_range.2 (Nat.lt_succ_of_le hkn),
        ⟨⟨mem_firstHit.2 ⟨hk_min, hk_spec⟩, ?_⟩, ?_⟩⟩
      · show X (((j + 1 : ℕ) : ℝ≥0) * τ) ω ≤ a + δ
        linarith
      · show δ < X ((n : ℝ≥0) * τ) ω - X (((j + 1 : ℕ) : ℝ≥0) * τ) ω
        linarith
  -- (4) assemble
  have hG₂ : P {ω | a + 2 * δ < X ((n : ℝ≥0) * τ) ω}
      ≤ P Bad + P ({ω | ∃ k ≤ n, a ≤ X ((k : ℝ≥0) * τ) ω}
        \ {ω | a ≤ X ((n : ℝ≥0) * τ) ω}) := by
    calc P {ω | a + 2 * δ < X ((n : ℝ≥0) * τ) ω}
        ≤ P Bad + P ({ω | a + 2 * δ < X ((n : ℝ≥0) * τ) ω} \ Bad) := by
          refine (measure_mono (t := Bad ∪ ({ω | a + 2 * δ < X ((n : ℝ≥0) * τ) ω} \ Bad))
            ?_).trans (measure_union_le _ _)
          intro ω hω
          by_cases hb : ω ∈ Bad
          · exact Or.inl hb
          · exact Or.inr ⟨hω, hb⟩
      _ ≤ P Bad + ∑ k ∈ Finset.range (n + 1),
            P (W k ∩ {ω | δ < X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω}) := by
          refine add_le_add le_rfl ?_
          refine (measure_mono hCover).trans ?_
          exact (measure_biUnion_firstHit (f := fun k ↦
              W k ∩ {ω | δ < X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω})
            (fun k ↦ Set.inter_subset_left.trans (hWE k))
            (fun k ↦ (hW k).inter (measurableSet_lt measurable_const ((hm _).sub (hm _)))) n).le
      _ = P Bad + ∑ k ∈ Finset.range (n + 1),
            P (W k ∩ {ω | X ((n : ℝ≥0) * τ) ω - X ((k : ℝ≥0) * τ) ω < -δ}) := by
          congr 1
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          exact (reflect_grid hX hm τ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) (hWn k) δ).symm
      _ ≤ _ := add_le_add le_rfl hRefl
  calc P {ω | a ≤ X ((n : ℝ≥0) * τ) ω} + P {ω | a + 2 * δ < X ((n : ℝ≥0) * τ) ω}
      ≤ P {ω | a ≤ X ((n : ℝ≥0) * τ) ω} + (P Bad + P ({ω | ∃ k ≤ n, a ≤ X ((k : ℝ≥0) * τ) ω}
        \ {ω | a ≤ X ((n : ℝ≥0) * τ) ω})) := add_le_add le_rfl hG₂
    _ = P {ω | ∃ k ≤ n, a ≤ X ((k : ℝ≥0) * τ) ω} + P Bad := by
        rw [add_left_comm, hdecomp, add_comm]
    _ ≤ _ := add_le_add le_rfl (measure_bad_le hX τ n ha hδ)

end Discrete

section Limit

/-- **A grid point near `s`.** Every `s ≤ nτ` is within `τ` of a grid point `kτ`, `k ≤ n`. -/
private lemma exists_grid_near {τ s : ℝ≥0} {n : ℕ} (hs : s ≤ (n : ℝ≥0) * τ) :
    ∃ k ≤ n, dist ((k : ℝ≥0) * τ) s ≤ τ := by
  rcases eq_or_ne τ 0 with rfl | hτ
  · have hs0 : s = 0 := le_antisymm (by simpa using hs) zero_le
    exact ⟨0, Nat.zero_le _, by simp [hs0]⟩
  · have hτ0 : (0 : ℝ) < τ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hτ)
    have hs' : (s : ℝ) ≤ n * τ := by exact_mod_cast hs
    have hs0 : (0 : ℝ) ≤ s / τ := div_nonneg s.2 hτ0.le
    have hk1 : (⌊(s : ℝ) / τ⌋₊ : ℝ) ≤ s / τ := Nat.floor_le hs0
    have hk2 : (s : ℝ) / τ < ⌊(s : ℝ) / τ⌋₊ + 1 := Nat.lt_floor_add_one _
    have a1 : (⌊(s : ℝ) / τ⌋₊ : ℝ) * τ ≤ s := (le_div_iff₀ hτ0).1 hk1
    have a2 : (s : ℝ) < (⌊(s : ℝ) / τ⌋₊ + 1) * τ := (div_lt_iff₀ hτ0).1 hk2
    refine ⟨⌊(s : ℝ) / τ⌋₊, Nat.floor_le_of_le ((div_le_iff₀ hτ0).2 hs'), ?_⟩
    rw [NNReal.dist_eq]
    push_cast
    exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **A continuous path above `b` somewhere on `[0, t]` is above `b` on the grid of mesh `t/n`
for all large `n`.** -/
private lemma exists_grid_ge {ω : Ω} (hc : Continuous fun u ↦ X u ω) {t s : ℝ≥0} (hst : s ≤ t)
    {b : ℝ} (hb : b < X s ω) :
    ∃ N : ℕ, ∀ m ≥ N, ∃ k ≤ m + 1, b ≤ X ((k : ℝ≥0) * (t / ((m + 1 : ℕ) : ℝ≥0))) ω := by
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.1
      (hc.continuousAt (x := s)) (X s ω - b) (sub_pos.2 hb)
  obtain ⟨N, hN⟩ := exists_nat_gt ((t : ℝ) / η)
  refine ⟨N, fun m hm ↦ ?_⟩
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs : s ≤ ((m + 1 : ℕ) : ℝ≥0) * (t / ((m + 1 : ℕ) : ℝ≥0)) := by
    rw [mul_div_cancel₀ t (Nat.cast_ne_zero.2 (Nat.succ_ne_zero m))]
    exact hst
  obtain ⟨k, hk, hdist⟩ := exists_grid_near hs
  refine ⟨k, hk, ?_⟩
  have hτη : ((t / ((m + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < η := by
    push_cast
    rw [div_lt_iff₀ hm1]
    have h1 : (t : ℝ) / η < (m : ℝ) + 1 :=
      hN.trans_le ((Nat.cast_le.2 hm).trans (le_add_of_nonneg_right zero_le_one))
    have h2 := (div_lt_iff₀ hη).1 h1
    linarith
  have hd := hcont (x := (k : ℝ≥0) * (t / ((m + 1 : ℕ) : ℝ≥0))) (hdist.trans_lt hτη)
  rw [Real.dist_eq] at hd
  have := (abs_lt.1 hd).1
  linarith

/-- The probability that a pre-Brownian motion sits at exactly `a > 0` at time `t` is zero. -/
private lemma measure_eval_eq_zero (hX : IsPreBrownianReal X P) (t : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P {ω | X t ω = a} = 0 := by
  by_cases ht : t = 0
  · subst ht
    refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.1 hX.eval_zero_ae_eq_zero)
    show ¬ X 0 ω = 0
    intro h
    have hω' : X 0 ω = a := hω
    linarith
  · haveI := nullSingletonClass_gaussianReal (μ := 0) ht
    exact ((hX.hasLaw_eval t).measure_eq (p := fun x ↦ x = a) (measurableSet_singleton a)).trans
      (measure_singleton a)

/-- **Upper bound for the maximum over `[0, t]`.** For a Brownian motion with measurable sections,
`P(∃ s ≤ t, b < B_s) ≤ 2 P(b ≤ B_t)`. -/
private lemma measure_exists_gt_le (hB : IsBrownianReal X P) (hm : ∀ t, Measurable (X t))
    (t : ℝ≥0) (b : ℝ) :
    P {ω | ∃ s : ℝ≥0, s ≤ t ∧ b < X s ω} ≤ 2 * P {ω | b ≤ X t ω} := by
  let H : ℕ → Set Ω := fun m ↦ {ω | ∃ k ≤ m + 1, b ≤ X ((k : ℝ≥0) * (t / ((m + 1 : ℕ) : ℝ≥0))) ω}
  let F : ℕ → Set Ω := fun N ↦ ⋂ m ≥ N, H m
  have hH : ∀ m, P (H m) ≤ 2 * P {ω | b ≤ X t ω} := by
    intro m
    have hn : ((m + 1 : ℕ) : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)
    have h := measure_exists_grid_le hB.toIsPreBrownianReal hm (t / ((m + 1 : ℕ) : ℝ≥0)) (m + 1) b
    rw [mul_div_cancel₀ t hn] at h
    refine h.trans ?_
    rw [two_mul]
    exact add_le_add le_rfl (measure_mono fun ω hω ↦ (show b < X t ω from hω).le)
  have hmono : Monotone F := fun N N' hNN' ω hω ↦ by
    simp only [F, Set.mem_iInter] at hω ⊢
    exact fun m hm ↦ hω m (hNN'.trans hm)
  have hL : P (⋃ N, F N) ≤ 2 * P {ω | b ≤ X t ω} := by
    rw [hmono.measure_iUnion]
    exact iSup_le fun N ↦ (measure_mono (Set.iInter₂_subset N le_rfl)).trans (hH N)
  refine (measure_mono_ae ?_).trans hL
  filter_upwards [hB.cont] with ω hω ⟨s, hst, hb⟩
  obtain ⟨N, hN⟩ := exists_grid_ge hω hst hb
  exact Set.mem_iUnion.2 ⟨N, Set.mem_iInter₂.2 fun m hm ↦ hN m hm⟩

/-- **Lower bound for the maximum over `[0, t]`.** For a pre-Brownian motion with measurable
sections and `a > 0`, `P(a ≤ B_t) + P(a < B_t) ≤ P(∃ s ≤ t, a ≤ B_s)`. -/
private lemma measure_add_le_exists (hX : IsPreBrownianReal X P) (hm : ∀ t, Measurable (X t))
    (t : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P {ω | a ≤ X t ω} + P {ω | a < X t ω} ≤ P {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ X s ω} := by
  -- first, for each `δ > 0`, the grid inequality in the limit `n → ∞`
  have hδ : ∀ δ : ℝ, 0 < δ →
      P {ω | a ≤ X t ω} + P {ω | a + 2 * δ < X t ω} ≤ P {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ X s ω} := by
    intro δ hδ
    have hbound : ∀ m : ℕ, P {ω | a ≤ X t ω} + P {ω | a + 2 * δ < X t ω}
        ≤ P {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ X s ω}
          + ENNReal.ofReal (3 * (t : ℝ) ^ 2 / δ ^ 4 * (1 / ((m : ℝ) + 1))) := by
      intro m
      have hn : ((m + 1 : ℕ) : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)
      have h := measure_ge_add_le hX hm (t / ((m + 1 : ℕ) : ℝ≥0)) (m + 1) ha hδ
      rw [mul_div_cancel₀ t hn] at h
      refine h.trans (add_le_add ?_ ?_)
      · exact measure_mono fun ω ⟨k, hk, hak⟩ ↦
          ⟨(k : ℝ≥0) * (t / ((m + 1 : ℕ) : ℝ≥0)), by
            calc (k : ℝ≥0) * (t / ((m + 1 : ℕ) : ℝ≥0))
                ≤ ((m + 1 : ℕ) : ℝ≥0) * (t / ((m + 1 : ℕ) : ℝ≥0)) :=
                  mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) zero_le
              _ = t := mul_div_cancel₀ t hn, hak⟩
      · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        push_cast
        have : ((m : ℝ) + 1) ≠ 0 := by positivity
        field_simp <;> ring
    have h0 : Tendsto (fun m : ℕ ↦ 3 * (t : ℝ) ^ 2 / δ ^ 4 * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (3 * (t : ℝ) ^ 2 / δ ^ 4)
    have h1 := ENNReal.tendsto_ofReal h0
    rw [ENNReal.ofReal_zero] at h1
    have h2 : Tendsto (fun m : ℕ ↦ P {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ X s ω}
        + ENNReal.ofReal (3 * (t : ℝ) ^ 2 / δ ^ 4 * (1 / ((m : ℝ) + 1)))) atTop
        (𝓝 (P {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ X s ω} + 0)) := tendsto_const_nhds.add h1
    rw [add_zero] at h2
    exact ge_of_tendsto' h2 hbound
  -- then `δ ↓ 0`
  let C : ℕ → Set Ω := fun j ↦ {ω | a + 2 * (1 / ((j : ℝ) + 1)) < X t ω}
  have hCmono : Monotone C := fun i j hij ω hω ↦ by
    have : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    exact lt_of_le_of_lt (by linarith) (show a + 2 * (1 / ((i : ℝ) + 1)) < X t ω from hω)
  have hCunion : (⋃ j, C j) = {ω | a < X t ω} := by
    ext ω
    simp only [C, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, hj⟩
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
    · intro hω
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show 0 < (X t ω - a) / 2 by linarith)
      exact ⟨j, by linarith⟩
  have hsup : P {ω | a ≤ X t ω} + P {ω | a < X t ω}
      = ⨆ j, (P {ω | a ≤ X t ω} + P (C j)) := by
    rw [← hCunion, hCmono.measure_iUnion, ENNReal.add_iSup]
  rw [hsup]
  exact iSup_le fun j ↦ hδ _ (by positivity)

end Limit

section Main

/-- **The reflection principle, for sections that are measurable.** -/
private theorem reflection_of_measurable (hB : IsBrownianReal X P)
    (hm : ∀ t, Measurable (X t)) {t : ℝ≥0} {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ X s ω} = 2 * P {ω | a ≤ X t ω} := by
  haveI : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hnull := measure_eval_eq_zero hB.toIsPreBrownianReal t ha
  -- `P(a ≤ B_t) ≤ P(a < B_t)`, since `B_t = a` is null
  have hge : P {ω | a ≤ X t ω} ≤ P {ω | a < X t ω} := by
    calc P {ω | a ≤ X t ω} ≤ P ({ω | a < X t ω} ∪ {ω | X t ω = a}) :=
          measure_mono fun ω hω ↦ (lt_or_eq_of_le (show a ≤ X t ω from hω)).imp id Eq.symm
      _ ≤ P {ω | a < X t ω} + P {ω | X t ω = a} := measure_union_le _ _
      _ = P {ω | a < X t ω} := by rw [hnull, add_zero]
  apply le_antisymm
  · -- upper bound, shifting the level down by `1/(j+1)`
    let D : ℕ → Set Ω := fun j ↦ {ω | a - 1 / ((j : ℝ) + 1) ≤ X t ω}
    have hDanti : Antitone D := fun i j hij ω hω ↦ by
      have : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
      exact le_trans (by linarith) (show a - 1 / ((j : ℝ) + 1) ≤ X t ω from hω)
    have hDinter : (⋂ j, D j) = {ω | a ≤ X t ω} := by
      ext ω
      simp only [D, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h
        by_contra hlt
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show 0 < a - X t ω by linarith [not_le.1 hlt])
        linarith [h j]
      · intro h j
        have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
        linarith
    have hDmeas : ∀ j, NullMeasurableSet (D j) P := fun j ↦
      (measurableSet_le measurable_const (hm t)).nullMeasurableSet
    have hlim := tendsto_measure_iInter_atTop hDmeas hDanti ⟨0, measure_ne_top _ _⟩
    rw [hDinter] at hlim
    have hlim2 := ENNReal.Tendsto.const_mul (a := 2) hlim (Or.inr ENNReal.ofNat_ne_top)
    refine ge_of_tendsto' hlim2 fun j ↦ ?_
    refine le_trans ?_ (measure_exists_gt_le hB hm t (a - 1 / ((j : ℝ) + 1)))
    apply measure_mono
    rintro ω ⟨s, hst, has⟩
    refine ⟨s, hst, ?_⟩
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  · calc 2 * P {ω | a ≤ X t ω} = P {ω | a ≤ X t ω} + P {ω | a ≤ X t ω} := two_mul _
      _ ≤ P {ω | a ≤ X t ω} + P {ω | a < X t ω} := add_le_add le_rfl hge
      _ ≤ _ := measure_add_le_exists hB.toIsPreBrownianReal hm t ha

/-- **The reflection principle** (Saporito, Theorem 5.1.7). For a Brownian motion `B`, a time
`t` and a level `a > 0`,

  `P(B_s ≥ a for some s ∈ [0, t]) = 2 · P(B_t ≥ a)`.

Only the independence and Gaussianity of the increments at fixed times are used, through the
grid argument of `MathFin.measure_exists_grid_le` and `MathFin.measure_ge_add_le`; continuity of
paths passes from the grid to `[0, t]`. -/
theorem _root_.ProbabilityTheory.IsBrownianReal.reflection_principle
    (hB : IsBrownianReal X P) {t : ℝ≥0} {a : ℝ}
    (ha : 0 < a) :
    P {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ X s ω} = 2 * P {ω | a ≤ X t ω} := by
  have hP := hB.toIsPreBrownianReal
  obtain ⟨Y, hYm, hYB, hYX⟩ : ∃ Y : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (Y t)) ∧ IsBrownianReal Y P
      ∧ ∀ᵐ ω ∂P, ∀ t, Y t ω = X t ω :=
    ⟨IsPreBrownianReal.mk X hP, fun t ↦ hP.measurable_mk t, hP.isBrownianReal_mk,
      hB.mk_ae_forall_eq⟩
  have h1 : {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ X s ω} =ᵐ[P] {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ Y s ω} := by
    filter_upwards [hYX] with ω hω
    simp only [Set.mem_setOf_eq, hω]
  have h2 : {ω | a ≤ X t ω} =ᵐ[P] {ω | a ≤ Y t ω} := by
    filter_upwards [hYX] with ω hω
    simp only [Set.mem_setOf_eq, hω]
  rw [measure_congr h1, measure_congr h2]
  exact reflection_of_measurable hYB hYm ha

end Main

end MathFin
