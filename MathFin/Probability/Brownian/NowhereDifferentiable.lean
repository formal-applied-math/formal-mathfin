/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Gaussian.GaussianMoments
public import MathFin.Probability.Gaussian.GaussianSmallBall
public import BrownianMotion.Gaussian.BrownianMotion

/-!
# Brownian paths are nowhere differentiable

Almost surely the path `t ↦ B_t` has no right derivative at any `x ≥ 0`, hence is differentiable
nowhere. The proof is the Paley–Wiener–Zygmund argument and uses nothing about a pre-Brownian
motion `X` beyond its independent Gaussian increments (`IsPreBrownianReal`).

If the path had a right derivative `d` at some `x ≤ N`, then for all large `n` the first grid
point `k/n ≥ x` has the three consecutive increments over `[k/n, (k+3)/n]` at most `M/n` in
absolute value, with `M ≥ 8 (|d| + 1)` (`exists_three_small_increments`, pure real analysis).
The increments over the grid `ℕ/n` are independent with law `N(0, 1/n)`, so by the small-ball
bound (`gaussianReal_abs_le_le_inv_sqrt`) the event `E_{N,M,n}` that some `k ≤ nN` has three
consecutive small increments has probability at most `(nN + 1) (M/√n)³ ≤ (N+1) M² (M/√n)`
(`measure_exists_three_small_le`), which tends to `0`. The bad set sits in
`⋃_{N,M,n₀} ⋂_{n ≥ n₀} E_{N,M,n}`, a countable union of null sets.

## Main results

* `exists_three_small_increments`: a right derivative at `x ∈ [0, N]` forces three consecutive
  grid increments of size at most `M/n` for all large `n`
* `measure_exists_three_small_le`: the probability of that grid event is at most
  `(N+1) M² (M/√n)`
* `ProbabilityTheory.IsPreBrownianReal.ae_not_hasDerivWithinAt_Ici`: almost surely no path has a
  right derivative at any `x ≥ 0`
* `ProbabilityTheory.IsPreBrownianReal.ae_not_differentiableAt`: almost surely no path is
  differentiable at any `x ≥ 0`

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Corollary 5.3.4
* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  §2.9

## Tags

Brownian motion, nowhere differentiable, Paley–Wiener–Zygmund, sample path properties, MSC 60J65
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

section Deterministic

/-- **Three small consecutive increments.** If `g` has a right derivative at `x ∈ [0, N]`, there
are `M` and `n₀` such that for every `n ≥ n₀` some grid index `k ≤ nN` has the three consecutive
increments of `g` over `[k/n, (k+3)/n]` bounded by `M/n`. -/
theorem exists_three_small_increments {g : ℝ → ℝ} {x d : ℝ} (hx : 0 ≤ x) {N : ℕ}
    (hxN : x ≤ N) (hd : HasDerivWithinAt g d (Set.Ici x) x) :
    ∃ M n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ k : ℕ, k ≤ n * N ∧ ∀ m : ℕ, k ≤ m → m < k + 3 →
      |g (((m + 1 : ℕ) : ℝ) / n) - g ((m : ℝ) / n)| ≤ M / n := by
  have h1 := (hasDerivWithinAt_iff_isLittleO.1 hd).def zero_lt_one
  obtain ⟨η, hη, hsub⟩ := Metric.mem_nhdsWithin_iff.1 h1
  have key : ∀ y, x ≤ y → y < x + η → |g y - g x| ≤ (|d| + 1) * (y - x) := by
    intro y hxy hy
    have hmem : y ∈ Metric.ball x η ∩ Set.Ici x := by
      refine ⟨?_, hxy⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hxy)]
      linarith
    have h2 : ‖g y - g x - (y - x) • d‖ ≤ 1 * ‖y - x‖ := hsub hmem
    rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg (sub_nonneg.2 hxy),
      one_mul] at h2
    calc |g y - g x| = |(g y - g x - (y - x) * d) + (y - x) * d| := by congr 1; ring
      _ ≤ |g y - g x - (y - x) * d| + |(y - x) * d| := abs_add_le _ _
      _ ≤ (y - x) + (y - x) * |d| := by
          rw [abs_mul, abs_of_nonneg (sub_nonneg.2 hxy)]
          linarith
      _ = (|d| + 1) * (y - x) := by ring
  obtain ⟨M, hM⟩ := exists_nat_ge (8 * (|d| + 1))
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (4 / η)
  refine ⟨M, n₀, fun n hn ↦ ?_⟩
  have hnη : 4 / η < n := hn₀.trans_le (Nat.cast_le.2 hn)
  have hn0 : (0 : ℝ) < n := lt_trans (by positivity) hnη
  have h4 : 4 < n * η := (div_lt_iff₀ hη).1 hnη
  have he : 4 / (n : ℝ) < η := by
    rw [div_lt_iff₀ hn0]
    linarith
  refine ⟨⌈(n : ℝ) * x⌉₊, ?_, ?_⟩
  · exact Nat.ceil_le.2 (by push_cast; exact mul_le_mul_of_nonneg_left hxN hn0.le)
  · set k := ⌈(n : ℝ) * x⌉₊
    have hk1 : (n : ℝ) * x ≤ k := Nat.le_ceil _
    have hk2 : (k : ℝ) < n * x + 1 := Nat.ceil_lt_add_one (by positivity)
    have hu : ∀ m : ℕ, k ≤ m → m ≤ k + 3 → x ≤ (m : ℝ) / n ∧ (m : ℝ) / n ≤ x + 4 / n := by
      intro m hm1 hm2
      have hm1' : (k : ℝ) ≤ m := Nat.cast_le.2 hm1
      have hm2' : (m : ℝ) ≤ k + 3 := by exact_mod_cast hm2
      refine ⟨(le_div_iff₀ hn0).2 (by linarith), ?_⟩
      have h44 : 4 / (n : ℝ) * n = 4 := by field_simp
      rw [div_le_iff₀ hn0]
      nlinarith [h44]
    have hb : ∀ m : ℕ, k ≤ m → m ≤ k + 3 →
        |g ((m : ℝ) / n) - g x| ≤ (|d| + 1) * (4 / n) := by
      intro m hm1 hm2
      obtain ⟨h5, h6⟩ := hu m hm1 hm2
      exact (key _ h5 (by linarith)).trans
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    intro m hm1 hm2
    have hA := hb (m + 1) (by omega) (by omega)
    have hB := hb m hm1 (by omega)
    calc |g (((m + 1 : ℕ) : ℝ) / n) - g ((m : ℝ) / n)|
        ≤ |g (((m + 1 : ℕ) : ℝ) / n) - g x| + |g x - g ((m : ℝ) / n)| := abs_sub_le _ _ _
      _ ≤ (|d| + 1) * (4 / n) + (|d| + 1) * (4 / n) := by
          rw [abs_sub_comm (g x)]
          exact add_le_add hA hB
      _ = (8 * (|d| + 1)) / n := by ring
      _ ≤ M / n := div_le_div_of_nonneg_right hM hn0.le

end Deterministic

section Probabilistic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

/-- Consecutive grid points of mesh `1/n` are `1/n` apart. -/
private lemma grid_sub {n : ℕ} (i : ℕ) :
    ((i + 1 : ℕ) : ℝ≥0) / n - ((i : ℕ) : ℝ≥0) / n = (n : ℝ≥0)⁻¹ := by
  rw [Nat.cast_succ, add_div, one_div, add_tsub_cancel_left]

/-- An increment of a pre-Brownian motion over a grid step `1/n` has law `N(0, 1/n)`. -/
private lemma hasLaw_grid_increment (hX : IsPreBrownianReal X P) (n i : ℕ) :
    HasLaw (fun ω ↦ X (((i + 1 : ℕ) : ℝ≥0) / n) ω - X (((i : ℕ) : ℝ≥0) / n) ω)
      (gaussianReal 0 (n : ℝ≥0)⁻¹) P := by
  have h := hasLaw_increment hX (s := ((i : ℕ) : ℝ≥0) / n) (t := ((i + 1 : ℕ) : ℝ≥0) / n)
    (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ i) zero_le)
  rw [grid_sub] at h
  exact h

/-- One grid increment lands in the window `[-c/n, c/n]` with probability at most `c/√n`. -/
private lemma measure_grid_increment_le (hX : IsPreBrownianReal X P) {n : ℕ} (hn : 0 < n)
    {c : ℝ} (hc : 0 ≤ c) (i : ℕ) :
    P {ω | |X (((i + 1 : ℕ) : ℝ≥0) / n) ω - X (((i : ℕ) : ℝ≥0) / n) ω| ≤ c / n}
      ≤ ENNReal.ofReal (c / √n) :=
  ((hasLaw_grid_increment hX n i).measure_eq (p := fun x ↦ |x| ≤ c / n)
    (measurableSet_le continuous_abs.measurable measurable_const)).trans_le
    (gaussianReal_abs_le_le_inv_sqrt hn hc)

/-- Three consecutive grid increments are all small with probability at most `(c/√n)³`: the
increments are independent. -/
private lemma measure_three_increments_le (hX : IsPreBrownianReal X P) {n : ℕ} (hn : 0 < n)
    {c : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    P (⋂ m ∈ Finset.Ico k (k + 3),
        {ω | |X (((m + 1 : ℕ) : ℝ≥0) / n) ω - X (((m : ℕ) : ℝ≥0) / n) ω| ≤ c / n})
      ≤ ENNReal.ofReal (c / √n) ^ 3 := by
  have hmono : Monotone (fun i : ℕ ↦ ((i : ℝ≥0) / n)) := fun a b hab ↦
    div_le_div_of_nonneg_right (Nat.cast_le.2 hab) zero_le
  have hind := hX.hasIndepIncrements.nat hmono
  have h := hind.measure_inter_preimage_eq_mul (Finset.Ico k (k + 3))
    (sets := fun _ ↦ {x : ℝ | |x| ≤ c / n})
    (fun _ _ ↦ measurableSet_le continuous_abs.measurable measurable_const)
  refine h.le.trans ?_
  calc ∏ i ∈ Finset.Ico k (k + 3),
        P ((fun ω ↦ X (((i + 1 : ℕ) : ℝ≥0) / n) ω - X (((i : ℕ) : ℝ≥0) / n) ω) ⁻¹'
          {x : ℝ | |x| ≤ c / n})
      ≤ ∏ i ∈ Finset.Ico k (k + 3), ENNReal.ofReal (c / √n) :=
        Finset.prod_le_prod' fun i _ ↦ measure_grid_increment_le hX hn hc i
    _ = ENNReal.ofReal (c / √n) ^ 3 := by simp [Finset.prod_const]

/-- **The grid event.** The probability that some grid index `k ≤ nN` has three consecutive
increments of size at most `c/n` is at most `(N+1) c² (c/√n)`. -/
theorem measure_exists_three_small_le (hX : IsPreBrownianReal X P) {n : ℕ} (hn : 0 < n)
    {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    P (⋃ k ∈ Finset.range (N * n + 1), ⋂ m ∈ Finset.Ico k (k + 3),
        {ω | |X (((m + 1 : ℕ) : ℝ≥0) / n) ω - X (((m : ℕ) : ℝ≥0) / n) ω| ≤ c / n})
      ≤ ENNReal.ofReal ((N + 1) * c ^ 2 * (c / √n)) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hq : 0 ≤ c / √(n : ℝ) := by positivity
  have hreal : ((N * n + 1 : ℕ) : ℝ) * (c / √n) ^ 3 ≤ (N + 1) * c ^ 2 * (c / √n) := by
    have hsq : (c / √(n : ℝ)) ^ 2 = c ^ 2 / n := by
      rw [div_pow, Real.sq_sqrt hn0.le]
    have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
    have hc2 : ((N * n + 1 : ℕ) : ℝ) * (c ^ 2 / n) ≤ (N + 1) * c ^ 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hn0]
      push_cast
      nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.2 hn1)]
    calc ((N * n + 1 : ℕ) : ℝ) * (c / √n) ^ 3
        = (((N * n + 1 : ℕ) : ℝ) * (c ^ 2 / n)) * (c / √n) := by
          rw [show (c / √(n : ℝ)) ^ 3 = (c / √n) ^ 2 * (c / √n) by ring, hsq]
          ring
      _ ≤ ((N + 1) * c ^ 2) * (c / √n) := mul_le_mul_of_nonneg_right hc2 hq
      _ = (N + 1) * c ^ 2 * (c / √n) := rfl
  calc P (⋃ k ∈ Finset.range (N * n + 1), ⋂ m ∈ Finset.Ico k (k + 3),
          {ω | |X (((m + 1 : ℕ) : ℝ≥0) / n) ω - X (((m : ℕ) : ℝ≥0) / n) ω| ≤ c / n})
      ≤ ∑ k ∈ Finset.range (N * n + 1), P (⋂ m ∈ Finset.Ico k (k + 3),
          {ω | |X (((m + 1 : ℕ) : ℝ≥0) / n) ω - X (((m : ℕ) : ℝ≥0) / n) ω| ≤ c / n}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range (N * n + 1), ENNReal.ofReal (c / √n) ^ 3 :=
        Finset.sum_le_sum fun k _ ↦ measure_three_increments_le hX hn hc k
    _ = ((N * n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (c / √n) ^ 3 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ENNReal.ofReal (((N * n + 1 : ℕ) : ℝ) * (c / √n) ^ 3) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_pow hq,
          ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- The grid point `m/n` of the real line, read in `ℝ≥0`. -/
private lemma toNNReal_natCast_div (m n : ℕ) :
    (((m : ℕ) : ℝ) / (n : ℝ)).toNNReal = (m : ℝ≥0) / (n : ℝ≥0) := by
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (by positivity)]
  simp

/-- **Brownian paths have no right derivative.** Almost surely, no path of a pre-Brownian motion
has a right derivative at any `x ≥ 0`: for all `x : ℝ≥0` and `d : ℝ`, the extension
`t ↦ X (max t 0)` has no derivative `d` within `[x, ∞)` at `x`. -/
theorem _root_.ProbabilityTheory.IsPreBrownianReal.ae_not_hasDerivWithinAt_Ici
    (hX : IsPreBrownianReal X P) :
    ∀ᵐ ω ∂P, ∀ (x : ℝ≥0) (d : ℝ),
      ¬ HasDerivWithinAt (fun t : ℝ ↦ X t.toNNReal ω) d (Set.Ici (x : ℝ)) x := by
  rw [ae_iff]
  -- the bad set lies in a countable union of null sets `⋂_{n ≥ n₀} E_{N,M,n}`
  let E : ℕ → ℕ → ℕ → Set Ω := fun N M n ↦
    ⋃ k ∈ Finset.range (N * n + 1), ⋂ m ∈ Finset.Ico k (k + 3),
      {ω | |X (((m + 1 : ℕ) : ℝ≥0) / n) ω - X (((m : ℕ) : ℝ≥0) / n) ω| ≤ (M : ℝ) / n}
  have hnull : ∀ N M n₀ : ℕ, P (⋂ n ≥ n₀, E N M n) = 0 := by
    intro N M n₀
    have h0 : Tendsto (fun n : ℕ ↦ (M : ℝ) / √(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h1 := h0.const_mul (((N : ℝ) + 1) * (M : ℝ) ^ 2)
    rw [mul_zero] at h1
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_zero] at h2
    refine nonpos_iff_eq_zero.1 (ge_of_tendsto h2 (eventually_atTop.2 ⟨max n₀ 1, fun n hn ↦ ?_⟩))
    exact (measure_mono (Set.iInter₂_subset n (le_trans (le_max_left _ _) hn))).trans
      (measure_exists_three_small_le hX (lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hn))
        (Nat.cast_nonneg M) N)
  refine measure_mono_null (t := ⋃ N : ℕ, ⋃ M : ℕ, ⋃ n₀ : ℕ, ⋂ n ≥ n₀, E N M n) ?_ ?_
  · intro ω hω
    simp only [Set.mem_setOf_eq, not_forall, not_not] at hω
    obtain ⟨x, d, hd⟩ := hω
    obtain ⟨N, hN⟩ := exists_nat_ge (x : ℝ)
    obtain ⟨M, n₀, h⟩ := exists_three_small_increments (NNReal.coe_nonneg x) hN hd
    simp only [Set.mem_iUnion, Set.mem_iInter]
    refine ⟨N, M, n₀, fun n hn ↦ ?_⟩
    obtain ⟨k, hk, hm⟩ := h n hn
    simp only [E, Set.mem_iUnion, Set.mem_iInter, Finset.mem_range, Finset.mem_Ico]
    refine ⟨k, by rw [mul_comm]; exact Nat.lt_succ_of_le hk, fun m ⟨hm1, hm2⟩ ↦ ?_⟩
    have := hm m hm1 hm2
    simpa only [Set.mem_setOf_eq, toNNReal_natCast_div] using this
  · simp only [measure_iUnion_null_iff]
    exact fun N M n₀ ↦ hnull N M n₀

/-- **Brownian paths are nowhere differentiable** (Saporito, Corollary 5.3.4). Almost surely, no
path of a pre-Brownian motion is differentiable at any `x ≥ 0`, for the extension
`t ↦ X (max t 0)` to the real line. -/
theorem _root_.ProbabilityTheory.IsPreBrownianReal.ae_not_differentiableAt
    (hX : IsPreBrownianReal X P) :
    ∀ᵐ ω ∂P, ∀ x : ℝ≥0, ¬ DifferentiableAt ℝ (fun t : ℝ ↦ X t.toNNReal ω) x := by
  filter_upwards [hX.ae_not_hasDerivWithinAt_Ici] with ω hω x hdiff
  exact hω x _ hdiff.hasDerivAt.hasDerivWithinAt

end Probabilistic

end MathFin
