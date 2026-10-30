/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Binomial.SnellEnvelope
public import MathFin.Foundations.MarkovPathMeasure

/-!
# The binomial price as an expectation over coin-flip paths

`binomialPrice u d r g N S₀` (`Binomial/Model.lean`) is the backward-induction price of the
`N`-step CRR tree, and `Binomial/SnellEnvelope.lean` works on coin-flip paths `ω : ℕ → Bool`
with the spot `spotPath S₀ u d N ω = S₀ · ∏_{i<N} (u if ωᵢ else d)`, without a measure on paths.
Here the paths get one: `coinFlipMeasure q`, the infinite product of Mathlib's
`bernoulliMeasure` on `Bool` (the law of i.i.d. `Bernoulli(q)` flips). With `q = crrUpProb u d r`
the backward recursion is an expectation over whole paths under i.i.d. `Bernoulli(crrUpProb)`
flips (risk-neutral under `BinomialNoArb`, `crrUpProb_mul_up_add`, which is not assumed here):

  `binomialPrice u d r g N S₀ = e^{−rN} · ∫ g(spotPath S₀ u d N ω) d(coinFlipMeasure q)(ω)`.

The cylinder probabilities `q^{#up}(1 − q)^{#down}` are not assumed: they come from
`Measure.infinitePi_pi`, the product-measure formula. The
library's other probabilistic form of the price, `binomialPrice_eq_integral_convPow`
(`Binomial/CRRCharFun.lean`), integrates over the law of the terminal log-return instead.

## Main results

* `coinFlipMeasure_cylinder` — the first `n + 1` flips of a path have probability
  `∏_{k ≤ n} Bernoulli(q)(path k)`.
* `integral_comp_flips` — the integral of a function of the first `N` flips is the finite sum
  over the `2^N` flip sequences weighted by their probabilities.
* `binomialPrice_eq_sum` — the backward recursion unrolled into that finite sum.
* `binomialPrice_eq_integral_coinFlipMeasure` — the price as an expectation over paths.
* `measurable_spotPath`, `abs_spotPath_le` — the spot after `k` flips is a measurable, bounded
  function of the path.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

/-- The law of one `Bernoulli(q)` flip on `Bool`: `true` with probability `q`, `false` with
probability `1 − q` (Mathlib's `bernoulliMeasure`). -/
noncomputable def coinMeasure (q : ℝ≥0) (hq : q ≤ 1) : Measure Bool :=
  bernoulliMeasure true false ⟨q, q.2, by exact_mod_cast hq⟩

instance (q : ℝ≥0) (hq : q ≤ 1) : IsProbabilityMeasure (coinMeasure q hq) := by
  unfold coinMeasure bernoulliMeasure
  refine ⟨?_⟩
  simp only [measure_univ]

lemma coinMeasure_singleton (q : ℝ≥0) (hq : q ≤ 1) (b : Bool) :
    coinMeasure q hq {b} = if b then (q : ℝ≥0∞) else 1 - q := by
  cases b
  · rw [coinMeasure, bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton _)
      (by simp) (by simp)]
    rw [← ENNReal.coe_one, ← ENNReal.coe_sub]
    congr 1
    ext
    simp [NNReal.coe_sub hq]
  · rw [coinMeasure, bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _)
      (by simp) (by simp)]
    rfl

/-- The law of i.i.d. `Bernoulli(q)` coin flips on `ℕ → Bool`: the infinite product of
`Bernoulli(q)` measures. -/
noncomputable def coinFlipMeasure (q : ℝ≥0) (hq : q ≤ 1) : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ ↦ coinMeasure q hq

instance (q : ℝ≥0) (hq : q ≤ 1) : IsProbabilityMeasure (coinFlipMeasure q hq) := by
  unfold coinFlipMeasure
  infer_instance

/-- **Cylinder probabilities of the coin-flip measure.** The event that a path agrees with
`path` up to time `n` has probability `∏_{k ≤ n} Bernoulli(q)(path k)`: the product-measure
formula `infinitePi_pi` on the box `∏_{k ≤ n} {path k}`. -/
theorem coinFlipMeasure_cylinder (q : ℝ≥0) (hq : q ≤ 1) (path : ℕ → Bool) (n : ℕ) :
    coinFlipMeasure q hq (pathCylinder path n)
      = ∏ k ∈ range (n + 1), if path k then (q : ℝ≥0∞) else 1 - q := by
  have : pathCylinder path n = Set.pi (range (n + 1) : Finset ℕ) fun k ↦ {path k} := by
    ext ω
    simp [pathCylinder]
  rw [this, coinFlipMeasure, Measure.infinitePi_pi _ fun _ _ ↦ measurableSet_singleton _]
  exact prod_congr rfl fun k _ ↦ coinMeasure_singleton q hq _

/-- The first `N` flips of a path. -/
def flips (N : ℕ) (ω : ℕ → Bool) : Fin N → Bool := fun i ↦ ω i

lemma measurable_flips (N : ℕ) : Measurable (flips N) :=
  measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i : ℕ)

lemma flips_preimage_singleton (n : ℕ) (x : Fin (n + 1) → Bool) :
    flips (n + 1) ⁻¹' {x} = pathCylinder (fun k ↦ if h : k < n + 1 then x ⟨k, h⟩ else false) n := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, flips, pathCylinder,
    Set.mem_ofPred_eq]
  constructor
  · intro h k hk
    rw [dif_pos (Nat.lt_succ_of_le hk)]
    exact h ⟨k, Nat.lt_succ_of_le hk⟩
  · intro h i
    have hi := h i (Nat.le_of_lt_succ i.isLt)
    rwa [dif_pos i.isLt] at hi

/-- The probability that the first `N` flips are `x` is `∏ᵢ Bernoulli(q)(xᵢ)`. -/
theorem coinFlipMeasure_flips_preimage (q : ℝ≥0) (hq : q ≤ 1) (N : ℕ) (x : Fin N → Bool) :
    coinFlipMeasure q hq (flips N ⁻¹' {x}) = ∏ i, if x i then (q : ℝ≥0∞) else 1 - q := by
  cases N with
  | zero =>
    have huniv : flips 0 ⁻¹' {x} = Set.univ :=
      Set.eq_univ_of_forall fun ω ↦ Subsingleton.elim (flips 0 ω) x
    rw [huniv, measure_univ, Finset.univ_eq_empty, prod_empty]
  | succ n =>
    rw [flips_preimage_singleton, coinFlipMeasure_cylinder, ← Fin.prod_univ_eq_prod_range]
    exact prod_congr rfl fun i _ ↦ by simp [i.isLt]

/-- **Integrals of functions of finitely many flips are finite sums.** For any
`F : (Fin N → Bool) → ℝ`, the expectation of `F` of the first `N` flips is the sum over the
`2^N` flip sequences `x` of `F x` weighted by `∏ᵢ Bernoulli(q)(xᵢ)`. -/
theorem integral_comp_flips (q : ℝ≥0) (hq : q ≤ 1) (N : ℕ) (F : (Fin N → Bool) → ℝ) :
    ∫ ω, F (flips N ω) ∂coinFlipMeasure q hq
      = ∑ x, (∏ i, if x i then (q : ℝ) else 1 - q) * F x := by
  rw [← integral_map (measurable_flips N).aemeasurable
      (measurable_of_countable F).aestronglyMeasurable, integral_fintype Integrable.of_finite]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [smul_eq_mul, measureReal_def, Measure.map_apply (measurable_flips N)
    (measurableSet_singleton x), coinFlipMeasure_flips_preimage, ENNReal.toReal_prod]
  congr 1
  refine prod_congr rfl fun i _ ↦ ?_
  cases x i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ENNReal.toReal_sub_of_le (ENNReal.coe_le_one_iff.mpr hq) ENNReal.one_ne_top]
    simp
  | true => simp

/-- **The backward recursion unrolled.** For `q = crrUpProb u d r`, the `N`-step binomial
price is `e^{−rN}` times the sum over the `2^N` up/down sequences `x` of
`(∏ᵢ (q if xᵢ else 1 − q)) · g(S · ∏ᵢ (u if xᵢ else d))`. -/
theorem binomialPrice_eq_sum (u d r q : ℝ) (hq : crrUpProb u d r = q) (g : ℝ → ℝ) (N : ℕ)
    (S : ℝ) :
    binomialPrice u d r g N S = Real.exp (-(r * N)) *
      ∑ x : Fin N → Bool, (∏ i, if x i then q else 1 - q) * g (S * ∏ i, if x i then u else d) := by
  induction N generalizing S with
  | zero => simp
  | succ n ih =>
    have hsplit : ∑ x : Fin (n + 1) → Bool,
          (∏ i, if x i then q else 1 - q) * g (S * ∏ i, if x i then u else d)
        = q * ∑ y : Fin n → Bool,
            (∏ i, if y i then q else 1 - q) * g (S * u * ∏ i, if y i then u else d)
          + (1 - q) * ∑ y : Fin n → Bool,
            (∏ i, if y i then q else 1 - q) * g (S * d * ∏ i, if y i then u else d) := by
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) ↦ Bool).sum_comp, Fintype.sum_prod_type,
          Fintype.sum_bool,
        mul_sum, mul_sum]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ, Bool.false_eq_true, ↓reduceIte, mul_assoc]
    rw [binomialPrice_succ, hq, ih, ih, hsplit,
      show -(r * ((n + 1 : ℕ) : ℝ)) = -r + -(r * n) by push_cast; ring, Real.exp_add]
    ring

/-- **The binomial price is an expectation over coin-flip paths.** If the CRR
risk-neutral up-probability `crrUpProb u d r` is `q ∈ [0, 1]`, then for every payoff `g`,
horizon `N` and spot `S₀`,

  `binomialPrice u d r g N S₀ = e^{−rN} · ∫ g(spotPath S₀ u d N ω) d(coinFlipMeasure q)(ω)`,

where `coinFlipMeasure q` is the infinite product measure of i.i.d. `Bernoulli(q)` flips
on `ℕ → Bool`. -/
theorem binomialPrice_eq_integral_coinFlipMeasure (u d r : ℝ) (g : ℝ → ℝ) {q : ℝ≥0}
    (hq : q ≤ 1) (hqcrr : crrUpProb u d r = q) (N : ℕ) (S₀ : ℝ) :
    binomialPrice u d r g N S₀
      = Real.exp (-(r * N)) * ∫ ω, g (spotPath S₀ u d N ω) ∂coinFlipMeasure q hq := by
  have hspot (ω : ℕ → Bool) :
      g (spotPath S₀ u d N ω) = g (S₀ * ∏ i, if flips N ω i then u else d) := by
    rw [spotPath, ← Fin.prod_univ_eq_prod_range]
    rfl
  rw [binomialPrice_eq_sum u d r (q : ℝ) hqcrr g N S₀]
  congr 1
  rw [integral_congr_ae (ae_of_all _ hspot), integral_comp_flips q hq N
    fun x ↦ g (S₀ * ∏ i, if x i then u else d)]

/-- The spot after `k` flips is a measurable function of the path. -/
theorem measurable_spotPath (S₀ u d : ℝ) (k : ℕ) : Measurable (spotPath S₀ u d k) :=
  measurable_const.mul (Finset.measurable_prod _ fun i _ ↦
    (measurable_of_countable fun b : Bool ↦ if b then u else d).comp (measurable_pi_apply i))

/-- The spot after `k` flips is at most `|S₀| · max(|u|, |d|)ᵏ` in absolute value, along every
path. -/
theorem abs_spotPath_le (S₀ u d : ℝ) (k : ℕ) (ω : ℕ → Bool) :
    |spotPath S₀ u d k ω| ≤ |S₀| * max |u| |d| ^ k := by
  rw [spotPath, abs_mul, abs_prod]
  gcongr
  calc ∏ i ∈ range k, |if ω i then u else d| ≤ ∏ _i ∈ range k, max |u| |d| :=
        prod_le_prod (fun _ _ ↦ abs_nonneg _) fun i _ ↦ by split_ifs <;> simp
    _ = max |u| |d| ^ k := by simp

end MathFin
