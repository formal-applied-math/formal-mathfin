/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun, Raphael Coelho
-/
module

public import MathFin.Choice.Portfolio.RegressionBeta
public import MathFin.Choice.Portfolio.SingleIndexModel
public import MathFin.Probability.Laws.FiniteWeights

/-!
# Bühlmann credibility as a single-index model

A risk with latent parameter `Θ` (prior weights `p`) produces `n` observations that are iid given
`Θ` with law `w Θ` on a finite alphabet (the finite mixture `mixtureLaw`). Write the observations
as `Xᵢ = m(Θ) + εᵢ`: the hypothetical mean `m(Θ)` is the common factor with loading `1` and
`εᵢ = Xᵢ - m(Θ)` are the idiosyncratic shocks. This is Sharpe's single-index model, with the
hypothetical mean as the "market": the shocks are uncorrelated with it and with one another
(`covariance_latentMean_shock`, `covariance_shock_shock`), and each has variance `s² = E[σ²(Θ)]`
(`variance_shock`). Then

* the variance of the sample mean is the equal-weight portfolio variance of the single-index model,
  `Var X̄ = a + s²/n` with `a = Var m(Θ)` (`variance_sampleMean`,
  `MathFin.variance_singleIndex_portfolio`);
* the covariance of the factor with the sample mean is `a` (`covariance_latentMean_sampleMean`);
* the credibility factor is the regression coefficient (CAPM beta) of the factor on the sample
  mean, `Z = Cov(m, X̄)/Var X̄ = n/(n + κ)` with `κ = s²/a` (`beta_latentMean_sampleMean`);
* the credibility premium `μ + Z (X̄ - μ)` minimizes the mean squared error of predicting `m(Θ)`
  among affine functions of `X̄` (`buhlmann_mse_le`), by the least-squares property of the beta
  (`MathFin.integral_sq_affine_le`).

As `n → ∞` the idiosyncratic term `s²/n` diversifies away and `Z → 1`
(`tendsto_credibilityFactor`).

## Main definitions

* `MathFin.IsLatentModel`: `p` and each `w θ` are probability weights.
* `MathFin.mixtureLaw`: the law on `Θ × (Fin n → Ξ)` with weight `p θ * ∏ i, w θ (x i)`.
* `MathFin.condMean`, `MathFin.condVar`: the mean and variance of `v` under the weights `w θ`.
* `MathFin.collectiveMean`, `MathFin.varianceHypotheticalMean`,
  `MathFin.expectedProcessVariance`, `MathFin.credibilityConstant`: `μ`, `a`, `s²`, `κ = s²/a`.

## Main results

* `MathFin.variance_sampleMean`: `Var X̄ = a + s²/n`.
* `MathFin.covariance_latentMean_sampleMean`: `Cov(m(Θ), X̄) = a`.
* `MathFin.beta_latentMean_sampleMean`: `beta Cov(m, X̄) Var X̄ = n/(n + κ)`.
* `MathFin.buhlmann_mse_le`: `μ + n/(n + κ) (X̄ - μ)` is the best affine predictor of `m(Θ)`.
* `MathFin.credibilityFactor_mem_Icc` and `MathFin.tendsto_credibilityFactor`: `0 ≤ Z ≤ 1` and
  `Z → 1`.

## References

* [H. Bühlmann and A. Gisler, *A Course in Credibility Theory and its
  Applications*][BuhlmannGisler2005], §3.1
* [Sharpe, *A simplified model for portfolio analysis*][Sharpe1963]

## Tags

credibility, Bühlmann model, single-index model, latent mixture, best affine predictor,
MSC 62P05, JEL G22
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace MathFin

section Sums

variable {Ξ : Type*} [Fintype Ξ] {n : ℕ} {q : Ξ → ℝ}

/-- Under the product weight `∏ᵢ q(xᵢ)` on `Fin n → Ξ`, the sum of a product of functions of the
coordinates factorizes into the product of their sums against `q`. -/
lemma sum_pi_weight_mul_prod (f : Fin n → Ξ → ℝ) :
    ∑ x : Fin n → Ξ, (∏ i, q (x i)) * ∏ i, f i (x i) = ∏ i, ∑ ξ, q ξ * f i ξ := by
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun i ξ ↦ q ξ * f i ξ).symm

/-- One coordinate of an iid vector has the law `q`: under the product weight `∏ᵢ q(xᵢ)` of a
probability vector `q`, the sum of `g (x j)` is `∑ ξ, q ξ · g ξ`. -/
lemma sum_pi_weight_mul_apply (hq : ∑ ξ, q ξ = 1) (g : Ξ → ℝ) (j : Fin n) :
    ∑ x : Fin n → Ξ, (∏ i, q (x i)) * g (x j) = ∑ ξ, q ξ * g ξ := by
  have h := sum_pi_weight_mul_prod (q := q) fun i ξ ↦ if i = j then g ξ else 1
  simp only [Fintype.prod_ite_eq'] at h
  rw [h, Fintype.prod_eq_single j fun i hi ↦ by simp [hi, hq]]
  simp

/-- Two distinct coordinates of an iid vector are independent: under the product weight
`∏ₖ q(xₖ)` of a probability vector `q`, the sum of `g (x i) · h (x j)`, `i ≠ j`, is the product of
the two sums against `q`. -/
lemma sum_pi_weight_mul_apply_mul_apply (hq : ∑ ξ, q ξ = 1) (g h : Ξ → ℝ) {i j : Fin n}
    (hij : i ≠ j) :
    ∑ x : Fin n → Ξ, (∏ k, q (x k)) * (g (x i) * h (x j))
      = (∑ ξ, q ξ * g ξ) * ∑ ξ, q ξ * h ξ := by
  have h' := sum_pi_weight_mul_prod (q := q)
    fun k ξ ↦ if k = i then g ξ else if k = j then h ξ else 1
  have e (x : Fin n → Ξ) : (∏ k, if k = i then g (x k) else if k = j then h (x k) else 1)
      = g (x i) * h (x j) := by
    rw [Fintype.prod_eq_mul i j hij fun k hk ↦ by simp [hk.1, hk.2]]
    simp [hij.symm]
  have e' : (∏ k : Fin n, ∑ ξ, q ξ * if k = i then g ξ else if k = j then h ξ else 1)
      = (∑ ξ, q ξ * g ξ) * ∑ ξ, q ξ * h ξ := by
    rw [Fintype.prod_eq_mul i j hij fun k hk ↦ by simp [hk.1, hk.2, hq]]
    simp [hij.symm]
  simp only [e] at h'
  rw [h', e']

end Sums

variable {Θ Ξ : Type*} [Fintype Θ] [Fintype Ξ] [MeasurableSpace Θ] [MeasurableSpace Ξ]
  [MeasurableSingletonClass Θ] [MeasurableSingletonClass Ξ]

/-- A latent model: `p` are the prior weights on the risk parameter and `w θ` the weights of an
observation given `θ`. -/
structure IsLatentModel (p : Θ → ℝ) (w : Θ → Ξ → ℝ) : Prop where
  p_nonneg : ∀ θ, 0 ≤ p θ
  p_sum : ∑ θ, p θ = 1
  w_nonneg : ∀ θ ξ, 0 ≤ w θ ξ
  w_sum : ∀ θ, ∑ ξ, w θ ξ = 1

/-- **The finite latent mixture**: the law on `Θ × (Fin n → Ξ)` with weight
`p θ * ∏ i, w θ (x i)`, so the `n` observations are iid with law `w θ` given the parameter `θ`. -/
noncomputable def mixtureLaw (n : ℕ) (p : Θ → ℝ) (w : Θ → Ξ → ℝ) : Measure (Θ × (Fin n → Ξ)) :=
  Measure.ofWeights Finset.univ fun ω ↦ p ω.1 * ∏ i, w ω.1 (ω.2 i)

/-- The mean `∫ v` under the weights `w`: the hypothetical mean `m(θ)` for `w = w θ`. -/
noncomputable def condMean (w : Ξ → ℝ) (v : Ξ → ℝ) : ℝ :=
  ∫ ξ, v ξ ∂Measure.ofWeights Finset.univ w

/-- The variance of `v` under the weights `w`: the process variance `σ²(θ)` for `w = w θ`. -/
noncomputable def condVar (w : Ξ → ℝ) (v : Ξ → ℝ) : ℝ :=
  variance v (Measure.ofWeights Finset.univ w)

/-- The collective mean `μ = E[m(Θ)]`. -/
noncomputable def collectiveMean (p : Θ → ℝ) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ) : ℝ :=
  ∫ θ, condMean (w θ) v ∂Measure.ofWeights Finset.univ p

/-- The variance of the hypothetical means `a = Var m(Θ)`. -/
noncomputable def varianceHypotheticalMean (p : Θ → ℝ) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ) : ℝ :=
  variance (fun θ ↦ condMean (w θ) v) (Measure.ofWeights Finset.univ p)

/-- The expected process variance `s² = E[σ²(Θ)]`. -/
noncomputable def expectedProcessVariance (p : Θ → ℝ) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ) : ℝ :=
  ∫ θ, condVar (w θ) v ∂Measure.ofWeights Finset.univ p

/-- The credibility constant `κ = s²/a`. -/
noncomputable def credibilityConstant (p : Θ → ℝ) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ) : ℝ :=
  expectedProcessVariance p w v / varianceHypotheticalMean p w v

/-- The hypothetical mean `m(Θ)` as a random variable on the mixture. -/
noncomputable def latentMean (n : ℕ) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ) (ω : Θ × (Fin n → Ξ)) : ℝ :=
  condMean (w ω.1) v

/-- The sample mean `X̄ = n⁻¹ ∑ᵢ Xᵢ`. -/
noncomputable def sampleMean (n : ℕ) (v : Ξ → ℝ) (ω : Θ × (Fin n → Ξ)) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, v (ω.2 i)

/-- The idiosyncratic shock `εᵢ = Xᵢ - m(Θ)`. -/
noncomputable def shock (n : ℕ) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ) (i : Fin n)
    (ω : Θ × (Fin n → Ξ)) : ℝ :=
  v (ω.2 i) - condMean (w ω.1) v


variable {n : ℕ} {p : Θ → ℝ} {w : Θ → Ξ → ℝ} {v : Ξ → ℝ}

private lemma integral_mixtureLaw (hm : IsLatentModel p w) (f : Θ × (Fin n → Ξ) → ℝ) :
    ∫ ω, f ω ∂mixtureLaw n p w
      = ∑ θ, p θ * ∑ x : Fin n → Ξ, (∏ i, w θ (x i)) * f (θ, x) := by
  rw [mixtureLaw, Measure.integral_ofWeights _ fun ω _ ↦
    mul_nonneg (hm.p_nonneg _) (Finset.prod_nonneg fun i _ ↦ hm.w_nonneg _ _),
    Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_assoc]

omit [MeasurableSingletonClass Θ] [MeasurableSingletonClass Ξ] in
theorem isProbabilityMeasure_mixtureLaw (hm : IsLatentModel p w) :
    IsProbabilityMeasure (mixtureLaw n p w) :=
  Measure.isProbabilityMeasure_ofWeights
    (fun ω _ ↦ mul_nonneg (hm.p_nonneg _) (Finset.prod_nonneg fun i _ ↦ hm.w_nonneg _ _))
    (by simp [Fintype.sum_prod_type, ← Finset.mul_sum, ← Fintype.prod_sum, hm.w_sum, hm.p_sum])

/-- Expectation of a function of the parameter alone. -/
private lemma integral_comp_fst (hm : IsLatentModel p w) (F : Θ → ℝ) :
    ∫ ω, F ω.1 ∂mixtureLaw n p w = ∫ θ, F θ ∂Measure.ofWeights Finset.univ p := by
  rw [integral_mixtureLaw hm, Measure.integral_ofWeights _ fun θ _ ↦ hm.p_nonneg θ]
  refine Finset.sum_congr rfl fun θ _ ↦ ?_
  simp [← Finset.sum_mul, ← Fintype.prod_sum, hm.w_sum θ]

private lemma variance_comp_fst (hm : IsLatentModel p w) (F : Θ → ℝ) :
    Var[fun ω : Θ × (Fin n → Ξ) ↦ F ω.1; mixtureLaw n p w]
      = Var[F; Measure.ofWeights Finset.univ p] := by
  have hF : AEMeasurable F (Measure.ofWeights Finset.univ p) :=
    (measurable_of_finite F).aemeasurable
  have hF' : AEMeasurable (fun ω : Θ × (Fin n → Ξ) ↦ F ω.1) (mixtureLaw n p w) :=
    ((measurable_of_finite F).comp measurable_fst).aemeasurable
  rw [variance_eq_integral hF, variance_eq_integral hF',
    integral_comp_fst hm (fun θ ↦ (F θ - _) ^ 2), integral_comp_fst hm F]

omit [MeasurableSpace Θ] [MeasurableSingletonClass Θ] in
private lemma condMean_eq (hm : IsLatentModel p w) (θ : Θ) :
    condMean (w θ) v = ∑ ξ, w θ ξ * v ξ :=
  Measure.integral_ofWeights _ (fun ξ _ ↦ hm.w_nonneg θ ξ) v

omit [MeasurableSpace Θ] [MeasurableSingletonClass Θ] in
private lemma condVar_eq (hm : IsLatentModel p w) (θ : Θ) :
    condVar (w θ) v = ∑ ξ, w θ ξ * (v ξ - condMean (w θ) v) ^ 2 := by
  rw [condVar, variance_eq_integral (measurable_of_finite v).aemeasurable]
  exact Measure.integral_ofWeights _ (fun ξ _ ↦ hm.w_nonneg θ ξ)
    fun ξ ↦ (v ξ - condMean (w θ) v) ^ 2

omit [MeasurableSpace Θ] [MeasurableSingletonClass Θ] in
private lemma sum_weight_mul_sub_condMean (hm : IsLatentModel p w) (θ : Θ) :
    ∑ ξ, w θ ξ * (v ξ - condMean (w θ) v) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← condMean_eq hm θ, ← Finset.sum_mul, hm.w_sum θ, one_mul, sub_self]

private lemma memLp_mixtureLaw (hm : IsLatentModel p w) (f : Θ × (Fin n → Ξ) → ℝ) :
    MemLp f 2 (mixtureLaw n p w) := by
  have := isProbabilityMeasure_mixtureLaw (n := n) hm
  exact MemLp.of_discrete

/-! ### The single-index structure -/

private lemma integral_shock (hm : IsLatentModel p w) (i : Fin n) :
    ∫ ω, shock n w v i ω ∂mixtureLaw n p w = 0 := by
  rw [integral_mixtureLaw hm]
  refine Finset.sum_eq_zero fun θ _ ↦ ?_
  simp only [shock]
  rw [sum_pi_weight_mul_apply (hm.w_sum θ) (fun ξ ↦ v ξ - condMean (w θ) v) i,
    sum_weight_mul_sub_condMean hm θ, mul_zero]

/-- The idiosyncratic shocks are uncorrelated with the factor `m(Θ)`. -/
theorem covariance_latentMean_shock (hm : IsLatentModel p w) (i : Fin n) :
    cov[latentMean n w v, shock n w v i; mixtureLaw n p w] = 0 := by
  have := isProbabilityMeasure_mixtureLaw (n := n) hm
  rw [covariance_eq_sub (memLp_mixtureLaw hm _) (memLp_mixtureLaw hm _), integral_shock hm,
    mul_zero, sub_zero, integral_mixtureLaw hm]
  refine Finset.sum_eq_zero fun θ _ ↦ ?_
  simp only [latentMean, shock, Pi.mul_apply]
  rw [sum_pi_weight_mul_apply (hm.w_sum θ) (fun ξ ↦ condMean (w θ) v * (v ξ - condMean (w θ) v)) i]
  have h0 : ∑ ξ, w θ ξ * (condMean (w θ) v * (v ξ - condMean (w θ) v)) = 0 := by
    simp_rw [mul_left_comm (w θ _)]
    rw [← Finset.mul_sum, sum_weight_mul_sub_condMean hm θ, mul_zero]
  rw [h0, mul_zero]

/-- Distinct idiosyncratic shocks are uncorrelated: the observations are conditionally
independent given `Θ`. -/
theorem covariance_shock_shock (hm : IsLatentModel p w) {i j : Fin n} (hij : i ≠ j) :
    cov[shock n w v i, shock n w v j; mixtureLaw n p w] = 0 := by
  have := isProbabilityMeasure_mixtureLaw (n := n) hm
  rw [covariance_eq_sub (memLp_mixtureLaw hm _) (memLp_mixtureLaw hm _), integral_shock hm i,
    integral_shock hm j, mul_zero, sub_zero, integral_mixtureLaw hm]
  refine Finset.sum_eq_zero fun θ _ ↦ ?_
  simp only [shock, Pi.mul_apply]
  rw [sum_pi_weight_mul_apply_mul_apply (hm.w_sum θ) (fun ξ ↦ v ξ - condMean (w θ) v)
    (fun ξ ↦ v ξ - condMean (w θ) v) hij, sum_weight_mul_sub_condMean hm θ]
  simp

/-- Each idiosyncratic shock has variance `s² = E[σ²(Θ)]`, the expected process variance. -/
theorem variance_shock (hm : IsLatentModel p w) (i : Fin n) :
    Var[shock n w v i; mixtureLaw n p w] = expectedProcessVariance p w v := by
  have := isProbabilityMeasure_mixtureLaw (n := n) hm
  rw [variance_eq_sub (memLp_mixtureLaw hm _), integral_shock hm, expectedProcessVariance,
    Measure.integral_ofWeights _ fun θ _ ↦ hm.p_nonneg θ, integral_mixtureLaw hm]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, Pi.pow_apply]
  refine Finset.sum_congr rfl fun θ _ ↦ ?_
  simp only [shock]
  rw [sum_pi_weight_mul_apply (hm.w_sum θ) (fun ξ ↦ (v ξ - condMean (w θ) v) ^ 2) i,
    condVar_eq hm θ]

theorem variance_latentMean (hm : IsLatentModel p w) :
    Var[latentMean n w v; mixtureLaw n p w] = varianceHypotheticalMean p w v :=
  variance_comp_fst hm fun θ ↦ condMean (w θ) v

omit [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  [MeasurableSingletonClass Ξ] in
private lemma sampleMean_eq :
    sampleMean n v = ∑ i : Fin n, ((1 : ℝ) / n) • ((1 : ℝ) • latentMean n w v + shock n w v i) := by
  funext ω
  simp only [sampleMean, latentMean, shock, Finset.sum_apply, Pi.smul_apply, Pi.add_apply,
    one_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

private lemma integral_sampleMean (hm : IsLatentModel p w) (hn : 0 < n) :
    ∫ ω, sampleMean n v ω ∂mixtureLaw n p w = collectiveMean p w v := by
  have := isProbabilityMeasure_mixtureLaw (n := n) hm
  have h : sampleMean n v = fun ω ↦ latentMean n w v ω + (n : ℝ)⁻¹ * ∑ i, shock n w v i ω := by
    funext ω
    have hn' : (n : ℝ) ≠ 0 := by positivity
    simp only [sampleMean, latentMean, shock, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hint (f : Θ × (Fin n → Ξ) → ℝ) : Integrable f (mixtureLaw n p w) :=
    (memLp_mixtureLaw hm f).integrable one_le_two
  have hl : ∫ ω, latentMean n w v ω ∂mixtureLaw n p w = collectiveMean p w v :=
    integral_comp_fst hm fun θ ↦ condMean (w θ) v
  rw [h, integral_add (hint _) ((hint _).const_mul _), integral_const_mul, hl,
    integral_finsetSum _ fun i _ ↦ hint _]
  simp [integral_shock hm]

omit [MeasurableSingletonClass Θ] [MeasurableSingletonClass Ξ] in
private lemma variance_sampleMean_pos (hn : 0 < n)
    (ha : varianceHypotheticalMean p w v ≠ 0) :
    0 < varianceHypotheticalMean p w v + expectedProcessVariance p w v / n := by
  have ha' : 0 < varianceHypotheticalMean p w v :=
    lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm ha)
  have hs : 0 ≤ expectedProcessVariance p w v :=
    integral_nonneg fun _ ↦ variance_nonneg _ _
  positivity

/-- **The sample-mean variance is the single-index portfolio variance**:
`Var X̄ = a + s²/n`, where `a = Var m(Θ)` and `s² = E[σ²(Θ)]`. The sample mean is the equal-weight
portfolio `∑ (1/n) (1 · m(Θ) + εᵢ)` of the single-index model with the hypothetical mean as the
factor, so this is `variance_singleIndex_portfolio`. -/
theorem variance_sampleMean (hm : IsLatentModel p w) (hn : 0 < n) :
    Var[sampleMean n v; mixtureLaw n p w]
      = varianceHypotheticalMean p w v + expectedProcessVariance p w v / n := by
  have := isProbabilityMeasure_mixtureLaw (n := n) hm
  have h := variance_singleIndex_portfolio (P := mixtureLaw n p w) (RM := latentMean n w v)
    (ε := shock n w v) Finset.univ (fun _ : Fin n ↦ (1 : ℝ) / n) (fun _ ↦ 1)
    (√Var[latentMean n w v; mixtureLaw n p w]) (memLp_mixtureLaw hm _)
    (fun _ ↦ memLp_mixtureLaw hm _) (covariance_latentMean_shock hm)
    (fun _ _ ↦ covariance_shock_shock hm) (Real.sq_sqrt (variance_nonneg _ _)).symm
  refine (congrArg (fun f ↦ Var[f; mixtureLaw n p w]) (sampleMean_eq (w := w) (v := v))).trans
    (h.trans ?_)
  have ha : 0 ≤ varianceHypotheticalMean p w v := variance_nonneg _ _
  simp only [variance_shock hm, variance_latentMean hm, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Real.sq_sqrt ha]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- The covariance of the factor with the sample mean is the factor variance:
`Cov(m(Θ), X̄) = a`. -/
theorem covariance_latentMean_sampleMean (hm : IsLatentModel p w) (hn : 0 < n) :
    cov[latentMean n w v, sampleMean n v; mixtureLaw n p w] = varianceHypotheticalMean p w v := by
  have := isProbabilityMeasure_mixtureLaw (n := n) hm
  have hmm := memLp_mixtureLaw hm (latentMean n w v)
  have hX (i : Fin n) : MemLp (((1 : ℝ) / n) • ((1 : ℝ) • latentMean n w v + shock n w v i)) 2
      (mixtureLaw n p w) := memLp_mixtureLaw hm _
  rw [sampleMean_eq (w := w) (v := v), covariance_sum_right (fun i ↦ hX i) hmm]
  simp only [covariance_smul_right, one_smul, covariance_add_right hmm hmm (memLp_mixtureLaw hm _),
    covariance_latentMean_shock hm, add_zero, covariance_self hmm.aemeasurable,
    variance_latentMean hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The credibility factor is a regression coefficient**: the CAPM beta of the factor `m(Θ)`
against the sample mean, `Cov(m, X̄)/Var X̄`, is `n/(n + κ)` with `κ = s²/a`. -/
theorem beta_latentMean_sampleMean (hm : IsLatentModel p w) (hn : 0 < n)
    (ha : varianceHypotheticalMean p w v ≠ 0) :
    beta cov[latentMean n w v, sampleMean n v; mixtureLaw n p w]
        Var[sampleMean n v; mixtureLaw n p w] = n / (n + credibilityConstant p w v) := by
  have hpos := variance_sampleMean_pos hn ha
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [beta, covariance_latentMean_sampleMean hm hn, variance_sampleMean hm hn, credibilityConstant]
  field_simp

/-- **Bühlmann's credibility premium is the best affine predictor**: among all affine functions
`c + b X̄` of the sample mean, the credibility premium `μ + n/(n + κ) (X̄ - μ)` has the least
mean squared error as a predictor of the hypothetical mean `m(Θ)`. -/
theorem buhlmann_mse_le (hm : IsLatentModel p w) (hn : 0 < n)
    (ha : varianceHypotheticalMean p w v ≠ 0) (c b : ℝ) :
    ∫ ω, (latentMean n w v ω - (collectiveMean p w v
        + n / (n + credibilityConstant p w v) * (sampleMean n v ω - collectiveMean p w v))) ^ 2
        ∂mixtureLaw n p w
      ≤ ∫ ω, (latentMean n w v ω - (c + b * sampleMean n v ω)) ^ 2 ∂mixtureLaw n p w := by
  have := isProbabilityMeasure_mixtureLaw (n := n) hm
  have hvar : Var[sampleMean n v; mixtureLaw n p w] ≠ 0 := by
    rw [variance_sampleMean hm hn]; exact (variance_sampleMean_pos hn ha).ne'
  have h := integral_sq_affine_le (memLp_mixtureLaw hm (latentMean n w v))
    (memLp_mixtureLaw hm (sampleMean n v)) hvar c b
  rwa [beta_latentMean_sampleMean hm hn ha, integral_sampleMean hm hn,
    show ∫ ω, latentMean n w v ω ∂mixtureLaw n p w = collectiveMean p w v from
      integral_comp_fst hm fun θ ↦ condMean (w θ) v] at h

omit [MeasurableSingletonClass Θ] [MeasurableSingletonClass Ξ] in
theorem credibilityConstant_nonneg (p : Θ → ℝ) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ) :
    0 ≤ credibilityConstant p w v :=
  div_nonneg (integral_nonneg fun _ ↦ variance_nonneg _ _) (variance_nonneg _ _)

omit [MeasurableSingletonClass Θ] [MeasurableSingletonClass Ξ] in
/-- The credibility factor `n/(n + κ)` lies in `[0, 1]`. -/
theorem credibilityFactor_mem_Icc (p : Θ → ℝ) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ) (n : ℕ) :
    (n : ℝ) / (n + credibilityConstant p w v) ∈ Set.Icc (0 : ℝ) 1 := by
  have hκ := credibilityConstant_nonneg p w v
  exact ⟨by positivity, div_le_one_of_le₀ (le_add_of_nonneg_right hκ) (by positivity)⟩

/-- As the number of observations grows the credibility factor tends to `1`: the idiosyncratic
term `s²/n` of the sample-mean variance diversifies away. -/
theorem tendsto_credibilityFactor (κ : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / (n + κ)) atTop (𝓝 1) :=
  tendsto_natCast_div_add_atTop κ

end MathFin
