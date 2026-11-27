/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Discrete.FiniteMarkovChain
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The ergodic theorem for finite Markov chains, in mean square

For an irreducible aperiodic chain on a finite state space with stationary distribution `π`, the
time average `(1/n) ∑_{k<n} f(X_k)` of any function `f` converges to `∑ⱼ πⱼ f(j)` in `L²`, under
the law `chainLaw K i` of the chain started at any state `i` (Saporito Theorem 1.4.32, finite state
space, mean-square form).

The proof is a variance computation. By the Markov property at a fixed time
(`markovPathMeasure_inter_shift`), the covariance of `g(X_j)` and `g(X_{j+m})` for `g = f - ∑ πf`
is `∑ₓ ℙ_i(X_j = x) g(x) (Pᵐ g)(x)` (`integral_mul_shift`), and `(Pᵐ g)(x) → ∑ πg = 0` for every
`x` by the convergence theorem (`tendsto_pow_of_isStationary`). A recursion on the double sum of
covariances (`sum_sum_le_of_abs_le`) bounds the variance of the sum by `3 G n ∑_{m<n} εₘ` with
`εₘ → 0`, and the Cesàro mean of a null sequence is null (`Filter.Tendsto.cesaro`).

## Main results

* `MathFin.FiniteMarkov.integral_mul_shift`: `E_i[φ(X_j) ψ(X_{j+m})] = ∑ₓ (Pʲ) i x φ(x) (Pᵐ ψ)(x)`.
* `MathFin.FiniteMarkov.tendsto_integral_sq_timeAverage`: the mean-square ergodic theorem,
  `E_i[((1/n) ∑_{k<n} f(X_k) - ∑ⱼ πⱼ f(j))²] → 0`.
* `MathFin.FiniteMarkov.tendsto_integral_sq_occupation`: the fraction of time spent in the state `j`
  converges to `π j` in mean square.

## Implementation notes

This is the mean-square form, not the almost-sure form of the textbook, and it assumes
aperiodicity, which the almost-sure theorem does not need (the proof goes through the convergence
theorem `P ^ n i j → π j`, which is false for a periodic chain). The state space is finite, so
positive recurrence is automatic. Mean-square convergence implies convergence in probability
(Chebyshev), not almost-sure convergence.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 1.4.32

## Tags

Markov chain, ergodic theorem, time average, stationary distribution, mean-square convergence,
Cesàro mean, MSC 60J10, MSC 37A25
-/

@[expose] public section

namespace MathFin.FiniteMarkov

open MeasureTheory Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
  (K : S → PMF S) (i : S)

/-! ### The Markov property for pairs of times -/

/-- The joint law of `X_j` and `X_{j+m}` under the chain started at `i`: the Markov property at the
fixed time `j`. -/
lemma chainLaw_pair_toReal (j m : ℕ) (x y : S) :
    (chainLaw K i ({ω | ω j = x} ∩ {ω | ω (j + m) = y})).toReal
      = (transitionMatrix K ^ j) i x * (transitionMatrix K ^ m) x y := by
  have h := markovPathMeasure_inter_shift (PMF.pure i) K j (j := x)
    {h | h ⟨j, Finset.mem_Iic.2 le_rfl⟩ = x} (fun h hh ↦ hh) (measurableSet_visit y m)
  have h' : chainLaw K i ({ω | ω j = x} ∩ {ω | ω (j + m) = y})
      = chainLaw K i {ω | ω j = x} * chainLaw K x {ω | ω m = y} := h
  rw [h', ENNReal.toReal_mul, chainLaw_visit_toReal_eq_pow, chainLaw_visit_toReal_eq_pow]

/-- A function of two coordinates of a trajectory is integrable against a finite measure: it takes
finitely many values. -/
lemma integrable_pair (μ : Measure (ℕ → S)) [IsFiniteMeasure μ] (φ : S → S → ℝ) (j k : ℕ) :
    Integrable (fun ω : ℕ → S ↦ φ (ω j) (ω k)) μ := by
  refine Integrable.of_bound ?_ (∑ p : S × S, ‖φ p.1 p.2‖) (ae_of_all _ fun ω ↦ ?_)
  · exact ((measurable_of_countable (fun p : S × S ↦ φ p.1 p.2)).comp
      ((measurable_pi_apply j).prodMk (measurable_pi_apply k))).aestronglyMeasurable
  · exact Finset.single_le_sum (f := fun p : S × S ↦ ‖φ p.1 p.2‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ (ω j, ω k))

/-- The expectation of a function of two coordinates of a trajectory, as a double sum over the
values of the two coordinates. -/
lemma integral_pair (μ : Measure (ℕ → S)) [IsFiniteMeasure μ] (j k : ℕ) (φ : S → S → ℝ) :
    ∫ ω, φ (ω j) (ω k) ∂μ
      = ∑ x, ∑ y, μ.real ({ω | ω j = x} ∩ {ω | ω k = y}) * φ x y := by
  have hm : Measurable (fun ω : ℕ → S ↦ (ω j, ω k)) :=
    (measurable_pi_apply j).prodMk (measurable_pi_apply k)
  have hφ : Measurable (fun p : S × S ↦ φ p.1 p.2) := measurable_of_countable _
  have hint : Integrable (fun p : S × S ↦ φ p.1 p.2) (μ.map fun ω : ℕ → S ↦ (ω j, ω k)) :=
    Integrable.of_finite
  have h2 : ∫ ω, φ (ω j) (ω k) ∂μ
      = ∫ p, φ p.1 p.2 ∂(μ.map fun ω : ℕ → S ↦ (ω j, ω k)) :=
    (integral_map hm.aemeasurable hφ.aestronglyMeasurable).symm
  rw [h2, integral_fintype hint, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  have hpre : (fun ω : ℕ → S ↦ (ω j, ω k)) ⁻¹' {(x, y)}
      = {ω | ω j = x} ∩ {ω | ω k = y} := by
    ext ω
    simp [Prod.ext_iff]
  rw [map_measureReal_apply hm (measurableSet_singleton (x, y)), hpre]
  try simp only [smul_eq_mul]

/-- **The Markov property for pairs of times**: `E_i[φ(X_j) ψ(X_{j+m})]` is
`∑ₓ (Pʲ) i x · φ(x) · (Pᵐ ψ)(x)`. -/
lemma integral_mul_shift (φ ψ : S → ℝ) (j m : ℕ) :
    ∫ ω, φ (ω j) * ψ (ω (j + m)) ∂chainLaw K i
      = ∑ x, (transitionMatrix K ^ j) i x
          * (φ x * ∑ y, (transitionMatrix K ^ m) x y * ψ y) := by
  rw [integral_pair (chainLaw K i) j (j + m) (fun x y ↦ φ x * ψ y)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [measureReal_def, chainLaw_pair_toReal K i j m x y]
  ring

/-! ### The covariance bound -/

/-- The covariance of `g(X_j)` and `g(X_{j+m})` is at most `(∑ |g|) · ∑ₓ |(Pᵐ g)(x)|`. -/
lemma abs_integral_mul_shift_le (g : S → ℝ) (j m : ℕ) :
    |∫ ω, g (ω j) * g (ω (j + m)) ∂chainLaw K i|
      ≤ (∑ x, |g x|) * ∑ x, |∑ y, (transitionMatrix K ^ m) x y * g y| := by
  rw [integral_mul_shift K i g g j m]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  have hM := pow_mem (transitionMatrix_mem_rowStochastic K) j
  have hp0 : 0 ≤ (transitionMatrix K ^ j) i x := nonneg_of_mem_rowStochastic hM
  have hp1 : (transitionMatrix K ^ j) i x ≤ 1 := le_one_of_mem_rowStochastic hM
  have hgx : |g x| ≤ ∑ y, |g y| :=
    Finset.single_le_sum (f := fun y ↦ |g y|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ x)
  rw [abs_mul, abs_of_nonneg hp0, abs_mul]
  exact (mul_le_mul hp1 (mul_le_mul_of_nonneg_right hgx (abs_nonneg _))
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one).trans_eq (one_mul _)

/-- The rows of `Pᵐ` applied to a `π`-centred function tend to zero: `∑ₓ |(Pᵐ g)(x)| → 0` when
`∑ πg = 0`. -/
lemma tendsto_sum_abs_pow_mul (hirr : IsIrreducible (transitionMatrix K))
    (hap : IsAperiodic (transitionMatrix K)) {π : Convexity.StdSimplex ℝ S}
    (hπ : IsStationary (transitionMatrix K) π) {g : S → ℝ} (hg : ∑ y, π.weights y * g y = 0) :
    Tendsto (fun m : ℕ ↦ ∑ x, |∑ y, (transitionMatrix K ^ m) x y * g y|) atTop (𝓝 0) := by
  have hP := transitionMatrix_mem_rowStochastic K
  have hx : ∀ x, Tendsto (fun m : ℕ ↦ |∑ y, (transitionMatrix K ^ m) x y * g y|) atTop
      (𝓝 0) := fun x ↦ by
    have h1 : Tendsto (fun m : ℕ ↦ ∑ y, (transitionMatrix K ^ m) x y * g y) atTop
        (𝓝 (∑ y, π.weights y * g y)) :=
      tendsto_finsetSum _ fun y _ ↦ (tendsto_pow_of_isStationary hP hirr hap hπ x y).mul_const _
    rw [hg] at h1
    have h2 := h1.abs
    rwa [abs_zero] at h2
  have h3 := tendsto_finsetSum Finset.univ fun x _ ↦ hx x
  rwa [Finset.sum_const_zero] at h3

/-! ### A recursion for the double sum of covariances -/

lemma sum_sum_le_of_abs_le (E : ℕ → ℕ → ℝ) (hsymm : ∀ j k, E j k = E k j) (ε : ℕ → ℝ)
    (hε : ∀ m, 0 ≤ ε m) {G : ℝ} (hG : 0 ≤ G) (hE : ∀ j m, |E j (j + m)| ≤ G * ε m) (n : ℕ) :
    ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, E j k
      ≤ 3 * G * n * ∑ m ∈ Finset.range n, ε m := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrow : ∑ k ∈ Finset.range n, E n k = ∑ j ∈ Finset.range n, E j n :=
      Finset.sum_congr rfl fun k _ ↦ hsymm n k
    have hstep : ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1), E j k
        = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, E j k
          + 2 * ∑ j ∈ Finset.range (n + 1), E j n - E n n := by
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
      linarith [hrow]
    have hrefl : ∑ j ∈ Finset.range (n + 1), ε (n - j) = ∑ m ∈ Finset.range (n + 1), ε m := by
      rw [← Finset.sum_range_reflect ε (n + 1)]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [Nat.add_sub_cancel]
    have hT : |∑ j ∈ Finset.range (n + 1), E j n| ≤ G * ∑ m ∈ Finset.range (n + 1), ε m := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j ∈ Finset.range (n + 1), |E j n|
          ≤ ∑ j ∈ Finset.range (n + 1), G * ε (n - j) :=
            Finset.sum_le_sum fun j hj ↦ by
              have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
              have h := hE j (n - j)
              rwa [Nat.add_sub_of_le hjn] at h
        _ = G * ∑ m ∈ Finset.range (n + 1), ε m := by rw [← Finset.mul_sum, hrefl]
    have h0 : |E n n| ≤ G * ε 0 := by
      have h := hE n 0
      simpa only [add_zero] using h
    have hε0 : ε 0 ≤ ∑ m ∈ Finset.range (n + 1), ε m :=
      Finset.single_le_sum (f := ε) (fun m _ ↦ hε m) (Finset.mem_range.2 (Nat.succ_pos n))
    have hmono : ∑ m ∈ Finset.range n, ε m ≤ ∑ m ∈ Finset.range (n + 1), ε m := by
      rw [Finset.sum_range_succ]
      linarith [hε n]
    have h1 : 2 * ∑ j ∈ Finset.range (n + 1), E j n
        ≤ 2 * (G * ∑ m ∈ Finset.range (n + 1), ε m) := by
      linarith [(le_abs_self _).trans hT]
    have h2 : -E n n ≤ G * ∑ m ∈ Finset.range (n + 1), ε m :=
      (neg_le_abs _).trans (h0.trans (mul_le_mul_of_nonneg_left hε0 hG))
    have h3 : 3 * G * n * ∑ m ∈ Finset.range n, ε m
        ≤ 3 * G * n * ∑ m ∈ Finset.range (n + 1), ε m :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    rw [hstep]
    push_cast
    linarith

/-! ### The mean-square ergodic theorem -/

/-- **Mean-square ergodic theorem for a centred function.** If `∑ πg = 0`, the time average of
`g` along the chain tends to `0` in mean square. -/
theorem tendsto_integral_sq_avg (hirr : IsIrreducible (transitionMatrix K))
    (hap : IsAperiodic (transitionMatrix K)) {π : Convexity.StdSimplex ℝ S}
    (hπ : IsStationary (transitionMatrix K) π) {g : S → ℝ} (hg : ∑ y, π.weights y * g y = 0) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (ω k)) ^ 2 ∂chainLaw K i)
      atTop (𝓝 0) := by
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℕ → ℝ,
      ∀ j k, E j k = ∫ ω, g (ω j) * g (ω k) ∂chainLaw K i := ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ,
      ∀ m, ε m = ∑ x, |∑ y, (transitionMatrix K ^ m) x y * g y| := ⟨_, fun _ ↦ rfl⟩
  have hsymm : ∀ j k, E j k = E k j := fun j k ↦ by
    rw [hE, hE]
    congr 1
    funext ω
    exact mul_comm _ _
  have hε0 : ∀ m, 0 ≤ ε m := fun m ↦ by
    rw [hεdef]
    exact Finset.sum_nonneg fun x _ ↦ abs_nonneg _
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    rw [show ε = fun m ↦ ∑ x, |∑ y, (transitionMatrix K ^ m) x y * g y| from funext hεdef]
    exact tendsto_sum_abs_pow_mul K hirr hap hπ hg
  have hG : 0 ≤ ∑ x, |g x| := Finset.sum_nonneg fun x _ ↦ abs_nonneg _
  have hbound : ∀ j m, |E j (j + m)| ≤ (∑ x, |g x|) * ε m := fun j m ↦ by
    rw [hE, hεdef]
    exact abs_integral_mul_shift_le K i g j m
  have hint : ∀ j k, Integrable (fun ω : ℕ → S ↦ g (ω j) * g (ω k)) (chainLaw K i) :=
    fun j k ↦ integrable_pair (chainLaw K i) (fun x y ↦ g x * g y) j k
  have hV : ∀ n : ℕ, ∫ ω, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (ω k)) ^ 2 ∂chainLaw K i
      = ((n : ℝ)⁻¹) ^ 2 * ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, E j k := fun n ↦ by
    have h1 : (fun ω : ℕ → S ↦ ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (ω k)) ^ 2)
        = fun ω ↦ ((n : ℝ)⁻¹) ^ 2
          * ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, g (ω j) * g (ω k) :=
      funext fun ω ↦ by rw [mul_pow, sq (∑ k ∈ Finset.range n, g (ω k)), Finset.sum_mul_sum]
    rw [h1, integral_const_mul, integral_finsetSum (Finset.range n) fun j _ ↦
      integrable_finsetSum (Finset.range n) fun k _ ↦ hint j k]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_finsetSum (Finset.range n) fun k _ ↦ hint j k]
    exact Finset.sum_congr rfl fun k _ ↦ (hE j k).symm
  have hup : Tendsto (fun n : ℕ ↦ 3 * (∑ x, |g x|) * ((n : ℝ)⁻¹ * ∑ m ∈ Finset.range n, ε m))
      atTop (𝓝 0) := by
    have h := hεlim.cesaro.const_mul (3 * ∑ x, |g x|)
    rwa [mul_zero] at h
  have key : ∀ n : ℕ, ∫ ω, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (ω k)) ^ 2 ∂chainLaw K i
      ≤ 3 * (∑ x, |g x|) * ((n : ℝ)⁻¹ * ∑ m ∈ Finset.range n, ε m) := fun n ↦ by
    rw [hV]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have hinv : (n : ℝ)⁻¹ * n = 1 := inv_mul_cancel₀ hn'
      refine (mul_le_mul_of_nonneg_left
        (sum_sum_le_of_abs_le E hsymm ε hε0 hG hbound n) (sq_nonneg _)).trans_eq ?_
      linear_combination
        (3 * (∑ x, |g x|) * (∑ m ∈ Finset.range n, ε m) * (n : ℝ)⁻¹) * hinv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n ↦ integral_nonneg fun ω ↦ sq_nonneg _) key

/-- **The ergodic theorem for finite Markov chains, in mean square** (Saporito Theorem 1.4.32,
finite state space): for an irreducible aperiodic chain with stationary distribution `π`, started
at any state `i`, the time average `(1/n) ∑_{k<n} f(X_k)` converges to `∑ⱼ πⱼ f(j)` in `L²`. -/
theorem tendsto_integral_sq_timeAverage (hirr : IsIrreducible (transitionMatrix K))
    (hap : IsAperiodic (transitionMatrix K)) {π : Convexity.StdSimplex ℝ S}
    (hπ : IsStationary (transitionMatrix K) π) (f : S → ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (ω k)
        - ∑ j, π.weights j * f j) ^ 2 ∂chainLaw K i) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∑ j, π.weights j * f j := ⟨_, rfl⟩
  rw [← hc]
  have hg : ∑ y, π.weights y * (f y - c) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, π.total_of_fintype, one_mul,
      ← hc, sub_self]
  refine (tendsto_integral_sq_avg K i hirr hap hπ hg).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  congr 1
  funext ω
  have hsum : ∑ k ∈ Finset.range n, (f (ω k) - c) = ∑ k ∈ Finset.range n, f (ω k) - n * c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum, mul_sub, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]

/-- **Occupation frequencies**: the fraction of time `(1/n) #{k < n : X_k = j}` that the chain
spends in the state `j` converges to `π j` in mean square. -/
theorem tendsto_integral_sq_occupation (hirr : IsIrreducible (transitionMatrix K))
    (hap : IsAperiodic (transitionMatrix K)) {π : Convexity.StdSimplex ℝ S}
    (hπ : IsStationary (transitionMatrix K) π) (j : S) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (if ω k = j then (1 : ℝ) else 0)
        - π.weights j) ^ 2 ∂chainLaw K i) atTop (𝓝 0) := by
  simpa using
    tendsto_integral_sq_timeAverage K i hirr hap hπ (fun x ↦ if x = j then (1 : ℝ) else 0)

end MathFin.FiniteMarkov
