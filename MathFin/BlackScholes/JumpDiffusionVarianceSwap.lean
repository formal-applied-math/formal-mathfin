/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.JumpDiffusionMoments
public import MathFin.BlackScholes.VarianceSwap
public import MathFin.BlackScholes.JumpDiffusionMerton
public import MathFin.BlackScholes.JumpDiffusionBrownian

/-!
# Variance swaps with jumps: the log contract against the variance

In the Black–Scholes model two functionals of the price give the variance swap's fair strike
`σ²`: the log contract of Demeterfi, Derman, Kamal and Zou, `(2/τ)·𝔼[log(F/S_τ) + (S_τ − F)/F]`
with the forward `F = Se^{rτ}` (`varianceSwap_fairStrike`), and the expected realized variance
(`tendsto_expected_bsLogPrice_equipartition_sum`); `VarianceSwapEquivalence.lean` records that
they agree. With jumps they differ by the jump bias `2Λ𝔼[e^J − 1 − J − J²/2]`, which vanishes
without jumps and, for downward jumps, is `≤ 0`, and `< 0` once `Λ > 0` and `ν{J < 0} ≠ 0`.

At the compensated drift `b = r − σ²/2 − Λ(𝔼[e^J] − 1)`, for a jump law whose moment-generating
function is finite near `0` and at `1`, `S > 0` and `τ > 0`:

* `jumpDiffusion_logContract`: the log contract's expected payoff, scaled as a variance rate, is
  `σ² + 2Λ𝔼[e^J − 1 − J]`. It is `(2/τ)(rτ − 𝔼[Y])` (`integral_logContract_of_integral_exp`) with
  the mean of `JumpDiffusionMoments.lean`; in Black–Scholes `rτ − 𝔼[Y]` is half the variance, and
  with jumps it differs from half the variance by `Λτ𝔼[e^J − 1 − J − J²/2]`;
* `jumpDiffusion_logContract_sub_variance`: the log contract minus the variance of the log-return
  per unit time, `σ² + Λ𝔼[J²]`, is the jump bias;
* `integral_jumpBias_nonpos`, `integral_jumpBias_neg`: the sign of the bias is a fact about the
  jump law: `≤ 0` for jumps `≤ 0`, as `e^x ≤ 1 + x + x²/2` for `x ≤ 0`, and `< 0` if moreover the
  jumps are negative with positive probability, as the inequality is strict for `x < 0`
  (`Real.exp_le_quadratic_of_nonpos`, `Real.exp_lt_quadratic_of_neg`);
* `jumpDiffusion_logContract_le_variance`, `jumpDiffusion_logContract_lt_variance`: so for jumps
  `≤ 0` the log contract is at most the variance, and strictly below it if `Λ > 0` and the jumps
  are negative with positive probability;
* `mertonJump_logContract_variance`: with Merton's log-jumps `N(log(1 + k) − δ²/2, δ²)`, the log
  contract is `σ² + 2Λ(k − log(1 + k) + δ²/2)` and the variance per unit time is
  `σ² + Λ((log(1 + k) − δ²/2)² + δ²)`.

On a jump-diffusion process `X` (`JumpDiffusionProcess`, a hypothesis structure whose existence with
jumps is not proved), both functionals are taken under one measure `P`:

* `integral_sum_comp_increment_equipartition`: for any process whose increments have laws that
  depend only on their length, `𝔼[∑ f(ΔX)]` along `n + 1` equal steps is `n + 1` times the mean of
  `f` under the law of one step;
* `JumpDiffusionProcess.integral_sum_sq_increment_equipartition`,
  `JumpDiffusionProcess.tendsto_integral_sum_sq_increment_equipartition`: so the expected realized
  variance is `(σ² + Λ𝔼[J²])T + (b + Λ𝔼[J])²T²/(n + 1)`, which tends to `(σ² + Λ𝔼[J²])T` whatever
  the drift, as in Black–Scholes (`expected_bsLogPrice_equipartition_sum`,
  `tendsto_expected_bsLogPrice_equipartition_sum`);
* `JumpDiffusionProcess.integral_logContract_of_martingale`: if the discounted price
  `e^{−rt}Se^{X_t}` is a `P`-martingale, the log contract on `S_T = Se^{X_T}` has expected payoff
  `σ² + 2Λ𝔼[e^J − 1 − J]` under `P` (the martingale forces the compensated drift,
  `JumpDiffusionProcess.martingale_iff`, and `X_T` has the log-return law,
  `JumpDiffusionProcess.hasLaw`);
* `JumpDiffusionProcess.logContract_sub_realizedVariance_of_martingale`: then at every sampling
  frequency the log contract minus the expected realized variance per unit time is
  `2Λ𝔼[e^J − 1 − J − J²/2] − (b + Λ𝔼[J])²T/(n + 1)`, the jump bias less a discrete-sampling term;
* `JumpDiffusionProcess.tendsto_logContract_sub_realizedVariance_of_martingale`: so the difference
  tends to the jump bias;
* `JumpDiffusionProcess.logContract_le_realizedVariance_of_martingale` and
  `JumpDiffusionProcess.logContract_lt_realizedVariance_of_martingale`: for jumps `≤ 0` the log
  contract is at most the expected realized variance per unit time at every sampling frequency,
  strictly if `Λ > 0` and the jumps are negative with positive probability;
* `IsFilteredPreBrownian.logContract_realizedVariance`: without jumps, for Brownian motion with
  the risk-neutral drift, the log contract is `σ²` and the difference is `−(r − σ²/2)²T/(n + 1)`.

The expectations are under the measure `P` that makes the discounted price a martingale and keeps
the characteristics `σ`, `Λ` and `ν` of `X`. A change of measure that moves `Λ` or `ν`, such as the
Esscher transform, is not covered.
-/
@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped NNReal Topology

/-- `eˣ < 1 + x + x²/2` for `x < 0`, the strict reverse of Mathlib's
`Real.quadratic_le_exp_of_nonneg`: `eˣ − (1 + x + x²/2)` is strictly increasing on `(−∞, 0]`, its
derivative `eˣ − (1 + x)` being positive off `0` (`Real.add_one_lt_exp`), and it vanishes at `0`. -/
theorem Real.exp_lt_quadratic_of_neg {x : ℝ} (hx : x < 0) : rexp x < 1 + x + x ^ 2 / 2 := by
  have hsq (y : ℝ) : HasDerivAt (fun y : ℝ ↦ y ^ 2 / 2) y y := by
    simpa using (hasDerivAt_pow 2 y).div_const 2
  have hd (y : ℝ) : HasDerivAt (fun y ↦ rexp y - (1 + y + y ^ 2 / 2)) (rexp y - (1 + y)) y :=
    (Real.hasDerivAt_exp y).fun_sub (((hasDerivAt_id' y).const_add 1).fun_add (hsq y))
  have hmono : StrictMonoOn (fun y ↦ rexp y - (1 + y + y ^ 2 / 2)) (Iic 0) :=
    strictMonoOn_of_deriv_pos (convex_Iic 0) (fun y _ ↦ (hd y).continuousAt.continuousWithinAt)
      fun y hy ↦ by
        rw [interior_Iic] at hy
        rw [(hd y).deriv]
        linarith [Real.add_one_lt_exp (mem_Iio.1 hy).ne]
  simpa using hmono (mem_Iic.2 hx.le) (mem_Iic.2 le_rfl) hx

/-- `eˣ ≤ 1 + x + x²/2` for `x ≤ 0`, the reverse of Mathlib's `Real.quadratic_le_exp_of_nonneg`
(`Real.exp_lt_quadratic_of_neg`, with equality at `0`). -/
theorem Real.exp_le_quadratic_of_nonpos {x : ℝ} (hx : x ≤ 0) : rexp x ≤ 1 + x + x ^ 2 / 2 := by
  rcases hx.lt_or_eq with hx | rfl
  · exact (Real.exp_lt_quadratic_of_neg hx).le
  · simp

namespace MathFin

/-- With jumps `≤ 0` almost surely, `e^J ≤ 1`, so the jump law has a finite exponential moment. -/
lemma integrable_exp_of_ae_nonpos {ν : Measure ℝ} [IsFiniteMeasure ν] (hJ : ∀ᵐ x ∂ν, x ≤ 0) :
    Integrable rexp ν :=
  .of_bound measurable_exp.aestronglyMeasurable 1 (hJ.mono fun x hx ↦ by
    rwa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x), Real.exp_le_one_iff])

/-- **The jump bias is `≤ 0` for downward jumps**: if `J ≤ 0` almost surely,
`𝔼[e^J − 1 − J − J²/2] ≤ 0`, since `e^x ≤ 1 + x + x²/2` for `x ≤ 0`
(`Real.exp_le_quadratic_of_nonpos`). -/
lemma integral_jumpBias_nonpos {ν : Measure ℝ} (hJ : ∀ᵐ x ∂ν, x ≤ 0) :
    ∫ x, (rexp x - 1 - x - x ^ 2 / 2) ∂ν ≤ 0 := by
  have hle : ∀ᵐ x ∂ν, rexp x - 1 - x - x ^ 2 / 2 ≤ 0 :=
    hJ.mono fun x hx ↦ by linarith [Real.exp_le_quadratic_of_nonpos hx]
  exact integral_nonpos_of_ae hle

/-- **The jump bias is `< 0` for crash jumps**: if moreover the jumps are negative with positive
probability, for a jump law with exponential moments near `0` (so that `J` and `J²` are
integrable), `𝔼[e^J − 1 − J − J²/2] < 0`: the integrand is `< 0` where `J < 0`
(`Real.exp_lt_quadratic_of_neg`). -/
lemma integral_jumpBias_neg {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : 0 ∈ interior (integrableExpSet id ν)) (hJ : ∀ᵐ x ∂ν, x ≤ 0) (hJ' : ν {x | x < 0} ≠ 0) :
    ∫ x, (rexp x - 1 - x - x ^ 2 / 2) ∂ν < 0 := by
  have hJ1 : Integrable (fun x ↦ x) ν := integrable_of_mem_interior_integrableExpSet hν
  have hJ2 : Integrable (fun x ↦ x ^ 2) ν := integrable_pow_of_mem_interior_integrableExpSet hν 2
  have hg : Integrable (fun x ↦ -(rexp x - 1 - x - x ^ 2 / 2)) ν :=
    ((((integrable_exp_of_ae_nonpos hJ).sub (integrable_const 1)).sub hJ1).sub
      (hJ2.div_const 2)).neg
  have hle : ∀ᵐ x ∂ν, 0 ≤ -(rexp x - 1 - x - x ^ 2 / 2) :=
    hJ.mono fun x hx ↦ by linarith [Real.exp_le_quadratic_of_nonpos hx]
  -- the negated integrand is positive where the jumps are negative
  have hpos : 0 < ∫ x, -(rexp x - 1 - x - x ^ 2 / 2) ∂ν := by
    refine (integral_pos_iff_support_of_nonneg_ae hle hg).2 (pos_iff_ne_zero.2 fun h0 ↦
      hJ' (measure_mono_null (fun x (hx : x < 0) ↦ ?_) h0))
    exact Function.mem_support.2 (ne_of_gt (by linarith [Real.exp_lt_quadratic_of_neg hx]))
  rwa [integral_neg, neg_pos] at hpos

/-! ### The log contract -/

/-- **The log contract with jumps.** At the compensated drift `b = r − σ²/2 − Λ(𝔼[e^J] − 1)`, for a
jump law with `𝔼[e^J] < ∞` and exponential moments near `0`, `S > 0` and `τ > 0`, the
Demeterfi–Derman–Kamal–Zou log contract on the forward `F = Se^{rτ}` has, scaled as a variance
rate, the expected payoff `(2/τ)·𝔼[log(F/S_τ) + (S_τ − F)/F] = σ² + 2Λ𝔼[e^J − 1 − J]`. The forward
is the mean of `S_τ` (`integral_exp_jumpDiffusionIncrementLaw_of_compensated`), so its expected
payoff is `(2/τ)(rτ − 𝔼[Y])` (`integral_logContract_of_integral_exp`), and `𝔼[Y] = (b + Λ𝔼[J])τ`
(`integral_id_jumpDiffusionIncrementLaw`). Without jumps it is `σ²`, the Black–Scholes value
(`varianceSwap_fairStrike`). -/
theorem jumpDiffusion_logContract {S r b σ : ℝ} (hS : 0 < S) {Λ : ℝ≥0} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (hν1 : Integrable rexp ν) (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {τ : ℝ≥0}
    (hτ : 0 < τ) :
    2 / τ * ∫ y, (Real.log (S * rexp (r * τ) / (S * rexp y))
        + (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ)))
      ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      = σ ^ 2 + 2 * Λ * ∫ x, (rexp x - 1 - x) ∂ν := by
  have hJ : Integrable (fun x ↦ x) ν := integrable_of_mem_interior_integrableExpSet hν
  have hE1 : Integrable (fun x ↦ rexp x - 1) ν := hν1.sub (integrable_const 1)
  rw [integral_logContract_of_integral_exp hS r τ (integrable_of_mem_interior_integrableExpSet
      (zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw b σ Λ hν τ))
      (integral_exp_jumpDiffusionIncrementLaw_of_compensated hν1 hb τ),
    integral_id_jumpDiffusionIncrementLaw b σ Λ hν τ, hb, integral_sub hE1 hJ,
    integral_sub hν1 (integrable_const 1), integral_const, probReal_univ, one_smul,
    div_mul_eq_mul_div, div_eq_iff (NNReal.coe_ne_zero.2 hτ.ne')]
  ring

/-- **The jump bias of the log contract.** Under the hypotheses of `jumpDiffusion_logContract`,
the log contract minus the variance of the log-return per unit time, `Var[Y]/τ = σ² + Λ𝔼[J²]`
(`variance_id_jumpDiffusionIncrementLaw`), is `2Λ𝔼[e^J − 1 − J − J²/2]`, whose integrand vanishes
to third order at `0`. Without jumps (`Λ = 0`) the two agree. -/
theorem jumpDiffusion_logContract_sub_variance {S r b σ : ℝ} (hS : 0 < S) {Λ : ℝ≥0}
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (hν1 : Integrable rexp ν) (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {τ : ℝ≥0}
    (hτ : 0 < τ) :
    2 / τ * ∫ y, (Real.log (S * rexp (r * τ) / (S * rexp y))
        + (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ)))
      ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      - Var[id; jumpDiffusionIncrementLaw b σ Λ ν τ] / τ
      = 2 * Λ * ∫ x, (rexp x - 1 - x - x ^ 2 / 2) ∂ν := by
  have hJ : Integrable (fun x ↦ x) ν := integrable_of_mem_interior_integrableExpSet hν
  have hJ2 : Integrable (fun x ↦ x ^ 2) ν := integrable_pow_of_mem_interior_integrableExpSet hν 2
  have hE1 : Integrable (fun x ↦ rexp x - 1 - x) ν := (hν1.sub (integrable_const 1)).sub hJ
  rw [jumpDiffusion_logContract hS hν hν1 hb hτ, variance_id_jumpDiffusionIncrementLaw b σ Λ hν τ,
    mul_div_cancel_right₀ _ (NNReal.coe_ne_zero.2 hτ.ne'), integral_sub hE1 (hJ2.div_const 2),
    integral_div]
  ring

/-- **With downward jumps the log contract is at most the variance.** If the jumps are
nonpositive (`J ≤ 0` `ν`-a.e.; then `𝔼[e^J] ≤ 1` is finite, `integrable_exp_of_ae_nonpos`), at the
compensated drift, for a jump law with exponential moments near `0`, `S > 0` and `τ > 0`, the log
contract is at most the variance of the log-return per unit time: the jump bias
(`jumpDiffusion_logContract_sub_variance`) is `≤ 0` (`integral_jumpBias_nonpos`). -/
theorem jumpDiffusion_logContract_le_variance {S r b σ : ℝ} (hS : 0 < S) {Λ : ℝ≥0}
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (hJ : ∀ᵐ x ∂ν, x ≤ 0) (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {τ : ℝ≥0}
    (hτ : 0 < τ) :
    2 / τ * ∫ y, (Real.log (S * rexp (r * τ) / (S * rexp y))
        + (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ)))
      ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      ≤ Var[id; jumpDiffusionIncrementLaw b σ Λ ν τ] / τ := by
  rw [← sub_nonpos,
    jumpDiffusion_logContract_sub_variance hS hν (integrable_exp_of_ae_nonpos hJ) hb hτ]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (integral_jumpBias_nonpos hJ)

/-- **With crash jumps the log contract is strictly below the variance.** If moreover `Λ > 0` and
the jumps are negative with positive probability (`ν {J < 0} ≠ 0`), the inequality of
`jumpDiffusion_logContract_le_variance` is strict: the jump bias is negative
(`integral_jumpBias_neg`). -/
theorem jumpDiffusion_logContract_lt_variance {S r b σ : ℝ} (hS : 0 < S) {Λ : ℝ≥0} (hΛ : 0 < Λ)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (hJ : ∀ᵐ x ∂ν, x ≤ 0) (hJ' : ν {x | x < 0} ≠ 0)
    (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {τ : ℝ≥0} (hτ : 0 < τ) :
    2 / τ * ∫ y, (Real.log (S * rexp (r * τ) / (S * rexp y))
        + (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ)))
      ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      < Var[id; jumpDiffusionIncrementLaw b σ Λ ν τ] / τ := by
  rw [← sub_neg,
    jumpDiffusion_logContract_sub_variance hS hν (integrable_exp_of_ae_nonpos hJ) hb hτ]
  exact mul_neg_of_pos_of_neg (mul_pos two_pos (NNReal.coe_pos.2 hΛ))
    (integral_jumpBias_neg hν hJ hJ')

/-- **Merton's model: the log contract against the variance.** With Merton's log-jumps
`N(log(1 + k) − δ²/2, δ²)` (`k > −1`) at the compensated drift `b = r − σ²/2 − Λk`
(`mertonJump_compensated`), `S > 0` and `τ > 0`, the log contract is
`σ² + 2Λ(k − log(1 + k) + δ²/2)` and the variance of the log-return per unit time is
`σ² + Λ((log(1 + k) − δ²/2)² + δ²)`: the jump multipliers have mean `1 + k`
(`integral_exp_mertonJump`), and the log-jumps mean `log(1 + k) − δ²/2` and variance `δ²` (Mathlib's
`integral_id_gaussianReal`, `variance_id_gaussianReal`). The jump bias, their difference, is
`2Λ(k − log(1 + k)) − Λ(log(1 + k) − δ²/2)²`. -/
theorem mertonJump_logContract_variance {S r b σ k δ : ℝ} (hS : 0 < S) (hk : -1 < k) {Λ : ℝ≥0}
    (hb : b = r - σ ^ 2 / 2 - Λ * k) {τ : ℝ≥0} (hτ : 0 < τ) :
    2 / τ * ∫ y, (Real.log (S * rexp (r * τ) / (S * rexp y))
        + (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ)))
      ∂(jumpDiffusionIncrementLaw b σ Λ
        (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) τ)
      = σ ^ 2 + 2 * Λ * (k - Real.log (1 + k) + δ ^ 2 / 2) ∧
    Var[id; jumpDiffusionIncrementLaw b σ Λ
        (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) τ] / τ
      = σ ^ 2 + Λ * ((Real.log (1 + k) - δ ^ 2 / 2) ^ 2 + δ ^ 2) := by
  have hν : 0 ∈ interior
      (integrableExpSet id (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal)) := by
    rw [integrableExpSet_id_gaussianReal, interior_univ]
    exact mem_univ 0
  have hE : Integrable rexp (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) :=
    integrable_exp_gaussianReal _ _
  have hE1 : Integrable (fun x ↦ rexp x - 1)
      (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) :=
    hE.sub (integrable_const 1)
  have hJ : Integrable (fun x ↦ x)
      (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) :=
    integrable_of_mem_interior_integrableExpSet hν
  -- the second moment of the log-jumps: the variance plus the squared mean
  have h2 : ∫ x, x ^ 2 ∂(gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal)
      = (Real.log (1 + k) - δ ^ 2 / 2) ^ 2 + δ ^ 2 := by
    have h := variance_eq_sub (memLp_of_mem_interior_integrableExpSet hν 2)
    rw [variance_id_gaussianReal, Real.coe_toNNReal _ (sq_nonneg δ)] at h
    simp only [Pi.pow_apply, id_eq] at h
    rw [integral_id_gaussianReal] at h
    linarith
  refine ⟨?_, ?_⟩
  · rw [jumpDiffusion_logContract hS hν hE (mertonJump_compensated hk δ hb) hτ,
      integral_sub hE1 hJ, integral_sub hE (integrable_const 1), integral_exp_mertonJump hk δ,
      integral_const, probReal_univ, one_smul, integral_id_gaussianReal]
    ring
  · rw [variance_id_jumpDiffusionIncrementLaw b σ Λ hν τ,
      mul_div_cancel_right₀ _ (NNReal.coe_ne_zero.2 hτ.ne'), h2]

/-! ### The realized variance of the process -/

/-- **The expected sum of a function of the increments along an equipartition.** If each increment
`X_t − X_s` (`s ≤ t`) has a law `μ (t − s)` that depends only on `t − s`, then along `n + 1` equal
steps of `[0, T]`, `𝔼[∑ₖ f(X_{(k+1)T/(n+1)} − X_{kT/(n+1)})] = (n + 1)·∫ f dμ(T/(n + 1))`, for any
`f` integrable under every `μ τ` (Mathlib's `HasLaw.integral_comp`). -/
theorem integral_sum_comp_increment_equipartition {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {μ : ℝ≥0 → Measure ℝ}
    (hX : ∀ s t, s ≤ t → HasLaw (fun ω ↦ X t ω - X s ω) (μ (t - s)) P) {f : ℝ → ℝ}
    (hf : ∀ τ, Integrable f (μ τ)) (T : ℝ≥0) (n : ℕ) :
    ∫ ω, ∑ k ∈ Finset.range (n + 1), f (X ((k + 1) * T / (n + 1)) ω - X (k * T / (n + 1)) ω) ∂P
      = (n + 1) * ∫ y, f y ∂(μ (T / (n + 1))) := by
  have hstep (k : ℕ) : ((k + 1) * T / (n + 1) : ℝ≥0) = k * T / (n + 1) + T / (n + 1) := by
    rw [add_mul, one_mul, add_div]
  have hle (k : ℕ) : (k * T / (n + 1) : ℝ≥0) ≤ (k + 1) * T / (n + 1) := by
    rw [hstep k]
    exact le_self_add
  have hlen (k : ℕ) : ((k + 1) * T / (n + 1) - k * T / (n + 1) : ℝ≥0) = T / (n + 1) := by
    rw [hstep k, add_tsub_cancel_left]
  have hlaw (k : ℕ) : HasLaw (fun ω ↦ X ((k + 1) * T / (n + 1)) ω - X (k * T / (n + 1)) ω)
      (μ (T / (n + 1))) P := by
    rw [← hlen k]
    exact hX _ _ (hle k)
  have hint (k : ℕ) :
      Integrable (fun ω ↦ f (X ((k + 1) * T / (n + 1)) ω - X (k * T / (n + 1)) ω)) P := by
    refine Integrable.comp_aemeasurable (g := f) ?_ (hlaw k).aemeasurable
    rw [(hlaw k).map_eq]
    exact hf _
  have h_each : ∀ k ∈ Finset.range (n + 1),
      ∫ ω, f (X ((k + 1) * T / (n + 1)) ω - X (k * T / (n + 1)) ω) ∂P
        = ∫ y, f y ∂(μ (T / (n + 1))) :=
    fun k _ ↦ (hlaw k).integral_comp (hf _).aestronglyMeasurable
  rw [integral_finsetSum _ fun k _ ↦ hint k, Finset.sum_congr rfl h_each, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, Nat.cast_add_one]

namespace JumpDiffusionProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b σ : ℝ} {Λ : ℝ≥0} {ν : Measure ℝ}

/-- **The expected realized variance of a jump-diffusion along an equipartition**: over `n + 1`
equal steps of `[0, T]`,
`𝔼[∑ₖ (X_{(k+1)T/(n+1)} − X_{kT/(n+1)})²] = (σ² + Λ𝔼[J²])T + (b + Λ𝔼[J])²T²/(n + 1)`, `n + 1` times
the second moment of the log-return over one step (`integral_sum_comp_increment_equipartition`,
`integral_sq_jumpDiffusionIncrementLaw`). The Black–Scholes form is
`expected_bsLogPrice_equipartition_sum`. -/
theorem integral_sum_sq_increment_equipartition (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν)
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν)) (T : ℝ≥0) (n : ℕ) :
    ∫ ω, ∑ k ∈ Finset.range (n + 1),
        (X ((k + 1) * T / (n + 1)) ω - X (k * T / (n + 1)) ω) ^ 2 ∂P
      = (σ ^ 2 + Λ * ∫ x, x ^ 2 ∂ν) * T + (b + Λ * ∫ x, x ∂ν) ^ 2 * T ^ 2 / (n + 1) := by
  rw [integral_sum_comp_increment_equipartition (μ := jumpDiffusionIncrementLaw b σ Λ ν) h.law
      (f := fun y ↦ y ^ 2) (fun τ ↦ integrable_pow_of_mem_interior_integrableExpSet
        (zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw b σ Λ hν τ) 2) T n,
    integral_sq_jumpDiffusionIncrementLaw b σ Λ hν]
  push_cast
  field_simp

/-- **The expected realized variance of a jump-diffusion tends to `(σ² + Λ𝔼[J²])T`** as the
equipartition of `[0, T]` refines: the drift term `(b + Λ𝔼[J])²T²/(n + 1)` vanishes, so the limit
is the variance of the log-return over `T` (`variance_id_jumpDiffusionIncrementLaw`), whatever the
drift. The Black–Scholes form is `tendsto_expected_bsLogPrice_equipartition_sum`. -/
theorem tendsto_integral_sum_sq_increment_equipartition (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν)
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν)) (T : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ∑ k ∈ Finset.range (n + 1),
        (X ((k + 1) * T / (n + 1)) ω - X (k * T / (n + 1)) ω) ^ 2 ∂P)
      atTop (𝓝 ((σ ^ 2 + Λ * ∫ x, x ^ 2 ∂ν) * T)) := by
  simp only [h.integral_sum_sq_increment_equipartition hν T]
  have h0 : Tendsto (fun n : ℕ ↦ (b + Λ * ∫ x, x ∂ν) ^ 2 * (T : ℝ) ^ 2 / ((n : ℝ) + 1)) atTop
      (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((b + Λ * ∫ x, x ∂ν) ^ 2 * (T : ℝ) ^ 2)
  simpa only [add_zero] using h0.const_add ((σ ^ 2 + Λ * ∫ x, x ^ 2 ∂ν) * (T : ℝ))

/-! ### The log contract on the process -/

/-- **The log contract on the process.** If the discounted price `e^{−rt}Se^{X_t}` is a
`P`-martingale, with `S > 0`, `T > 0` and a jump law whose moment-generating function is finite near
`0` and at `1`, the log contract on `S_T = Se^{X_T}` with the forward `F = Se^{rT}` has, under `P`,
the expected payoff `(2/T)·𝔼_P[log(F/S_T) + (S_T − F)/F] = σ² + 2Λ𝔼[e^J − 1 − J]`: the martingale
property forces the compensated drift (`martingale_iff`), `X_T` has the log-return law over `T`
(`hasLaw`), and the law gives `jumpDiffusion_logContract`. -/
theorem integral_logContract_of_martingale (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν)
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (hν1 : Integrable rexp ν) {S r : ℝ} (hS : 0 < S)
    (hM : Martingale (fun (t : ℝ≥0) ω ↦ rexp (-r * t) * (S * rexp (X t ω))) 𝓕 P) {T : ℝ≥0}
    (hT : 0 < T) :
    2 / T * ∫ ω, (Real.log (S * rexp (r * T) / (S * rexp (X T ω)))
        + (S * rexp (X T ω) - S * rexp (r * T)) / (S * rexp (r * T))) ∂P
      = σ ^ 2 + 2 * Λ * ∫ x, (rexp x - 1 - x) ∂ν := by
  rw [← jumpDiffusion_logContract hS hν hν1 ((h.martingale_iff hν1 hS.ne' r).1 hM) hT]
  congr 1
  exact (h.hasLaw T).integral_comp (f := fun y ↦ Real.log (S * rexp (r * T) / (S * rexp y))
    + (S * rexp y - S * rexp (r * T)) / (S * rexp (r * T))) (Measurable.aestronglyMeasurable
      (by fun_prop))

/-- **The log contract against the discretely sampled variance swap.** Under the hypotheses of
`integral_logContract_of_martingale`, along `n + 1` equal steps of `[0, T]` the log contract minus
the expected realized variance of `X` per unit time is
`2Λ𝔼[e^J − 1 − J − J²/2] − (b + Λ𝔼[J])²T/(n + 1)`: the jump bias, less a discrete-sampling term
that is `≥ 0` and vanishes as `n → ∞` (`integral_sum_sq_increment_equipartition`). The drift `b` is
the compensated drift, which the martingale property forces. -/
theorem logContract_sub_realizedVariance_of_martingale (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν)
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (hν1 : Integrable rexp ν) {S r : ℝ} (hS : 0 < S)
    (hM : Martingale (fun (t : ℝ≥0) ω ↦ rexp (-r * t) * (S * rexp (X t ω))) 𝓕 P) {T : ℝ≥0}
    (hT : 0 < T) (n : ℕ) :
    2 / T * ∫ ω, (Real.log (S * rexp (r * T) / (S * rexp (X T ω)))
        + (S * rexp (X T ω) - S * rexp (r * T)) / (S * rexp (r * T))) ∂P
      - (∫ ω, ∑ k ∈ Finset.range (n + 1),
          (X ((k + 1) * T / (n + 1)) ω - X (k * T / (n + 1)) ω) ^ 2 ∂P) / T
      = 2 * Λ * ∫ x, (rexp x - 1 - x - x ^ 2 / 2) ∂ν - (b + Λ * ∫ x, x ∂ν) ^ 2 * T / (n + 1) := by
  have hJ : Integrable (fun x ↦ x) ν := integrable_of_mem_interior_integrableExpSet hν
  have hJ2 : Integrable (fun x ↦ x ^ 2) ν := integrable_pow_of_mem_interior_integrableExpSet hν 2
  have hE1 : Integrable (fun x ↦ rexp x - 1 - x) ν := (hν1.sub (integrable_const 1)).sub hJ
  have hT' : (T : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hT.ne'
  rw [h.integral_logContract_of_martingale hν hν1 hS hM hT,
    h.integral_sum_sq_increment_equipartition hν T n, integral_sub hE1 (hJ2.div_const 2),
    integral_div]
  field_simp
  ring

/-- **With jumps the log contract misses the variance swap by the jump bias.** Under the
hypotheses of `integral_logContract_of_martingale`, the log contract minus the expected realized
variance of `X` per unit time along equipartitions of `[0, T]` tends to the jump bias
`2Λ𝔼[e^J − 1 − J − J²/2]`: the discrete-sampling term of
`logContract_sub_realizedVariance_of_martingale` vanishes. In Black–Scholes the limit is `0`
(`varianceSwap_log_eq_QV_limit_value`, `IsFilteredPreBrownian.logContract_realizedVariance`). -/
theorem tendsto_logContract_sub_realizedVariance_of_martingale
    (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure ν]
    (hν : 0 ∈ interior (integrableExpSet id ν)) (hν1 : Integrable rexp ν) {S r : ℝ} (hS : 0 < S)
    (hM : Martingale (fun (t : ℝ≥0) ω ↦ rexp (-r * t) * (S * rexp (X t ω))) 𝓕 P) {T : ℝ≥0}
    (hT : 0 < T) :
    Tendsto (fun n : ℕ ↦
        2 / T * ∫ ω, (Real.log (S * rexp (r * T) / (S * rexp (X T ω)))
            + (S * rexp (X T ω) - S * rexp (r * T)) / (S * rexp (r * T))) ∂P
        - (∫ ω, ∑ k ∈ Finset.range (n + 1),
            (X ((k + 1) * T / (n + 1)) ω - X (k * T / (n + 1)) ω) ^ 2 ∂P) / T)
      atTop (𝓝 (2 * Λ * ∫ x, (rexp x - 1 - x - x ^ 2 / 2) ∂ν)) := by
  simp only [h.logContract_sub_realizedVariance_of_martingale hν hν1 hS hM hT]
  have h0 : Tendsto (fun n : ℕ ↦ (b + Λ * ∫ x, x ∂ν) ^ 2 * (T : ℝ) / ((n : ℝ) + 1)) atTop
      (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((b + Λ * ∫ x, x ∂ν) ^ 2 * (T : ℝ))
  simpa only [sub_zero] using h0.const_sub (2 * Λ * ∫ x, (rexp x - 1 - x - x ^ 2 / 2) ∂ν : ℝ)

/-- **With downward jumps the log contract is below the variance swap at every sampling
frequency.** Under the hypotheses of `integral_logContract_of_martingale`, except finiteness of
`𝔼[e^J]`, which follows, if the jumps are `≤ 0` then along `n + 1` equal steps of `[0, T]` the log
contract is at most the expected realized variance of `X` per unit time, for every `n`: the jump
bias is `≤ 0` (`integral_jumpBias_nonpos`) and the discrete-sampling term `≥ 0`
(`logContract_sub_realizedVariance_of_martingale`). -/
theorem logContract_le_realizedVariance_of_martingale (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν)
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν)) (hJ : ∀ᵐ x ∂ν, x ≤ 0)
    {S r : ℝ} (hS : 0 < S)
    (hM : Martingale (fun (t : ℝ≥0) ω ↦ rexp (-r * t) * (S * rexp (X t ω))) 𝓕 P) {T : ℝ≥0}
    (hT : 0 < T) (n : ℕ) :
    2 / T * ∫ ω, (Real.log (S * rexp (r * T) / (S * rexp (X T ω)))
        + (S * rexp (X T ω) - S * rexp (r * T)) / (S * rexp (r * T))) ∂P
      ≤ (∫ ω, ∑ k ∈ Finset.range (n + 1),
          (X ((k + 1) * T / (n + 1)) ω - X (k * T / (n + 1)) ω) ^ 2 ∂P) / T := by
  have hdisc : 0 ≤ (b + Λ * ∫ x, x ∂ν) ^ 2 * T / (n + 1) := by positivity
  rw [← sub_nonpos, h.logContract_sub_realizedVariance_of_martingale hν
    (integrable_exp_of_ae_nonpos hJ) hS hM hT n]
  linarith [mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 2 * Λ)
    (integral_jumpBias_nonpos hJ)]

/-- **With crash jumps the log contract is strictly below the variance swap at every sampling
frequency.** If moreover `Λ > 0` and the jumps are negative with positive probability, the
inequality of `logContract_le_realizedVariance_of_martingale` is strict for every `n`: the jump
bias is `< 0` (`integral_jumpBias_neg`). -/
theorem logContract_lt_realizedVariance_of_martingale (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν)
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν)) (hΛ : 0 < Λ)
    (hJ : ∀ᵐ x ∂ν, x ≤ 0) (hJ' : ν {x | x < 0} ≠ 0) {S r : ℝ} (hS : 0 < S)
    (hM : Martingale (fun (t : ℝ≥0) ω ↦ rexp (-r * t) * (S * rexp (X t ω))) 𝓕 P) {T : ℝ≥0}
    (hT : 0 < T) (n : ℕ) :
    2 / T * ∫ ω, (Real.log (S * rexp (r * T) / (S * rexp (X T ω)))
        + (S * rexp (X T ω) - S * rexp (r * T)) / (S * rexp (r * T))) ∂P
      < (∫ ω, ∑ k ∈ Finset.range (n + 1),
          (X ((k + 1) * T / (n + 1)) ω - X (k * T / (n + 1)) ω) ^ 2 ∂P) / T := by
  have hdisc : 0 ≤ (b + Λ * ∫ x, x ∂ν) ^ 2 * T / (n + 1) := by positivity
  rw [← sub_neg, h.logContract_sub_realizedVariance_of_martingale hν
    (integrable_exp_of_ae_nonpos hJ) hS hM hT n]
  linarith [mul_neg_of_pos_of_neg (mul_pos two_pos (NNReal.coe_pos.2 hΛ))
    (integral_jumpBias_neg hν hJ hJ')]

end JumpDiffusionProcess

end MathFin

namespace ProbabilityTheory.IsFilteredPreBrownian

open MeasureTheory MathFin Real
open scoped NNReal

/-- **Black–Scholes: the log contract against the discretely sampled variance swap.** For a
pre-Brownian motion `B` for a filtration `𝓕`, the price `S_t = Se^{(r − σ²/2)t + σB_t}` with
`S > 0` and `T > 0`: the log contract on `S_T` has expected payoff `σ²` per unit time, and minus
the expected realized variance per unit time along `n + 1` equal steps of `[0, T]` it is
`−(r − σ²/2)²T/(n + 1)`: no jump bias, only the discrete-sampling term, which vanishes as
`n → ∞`. The filtration is explicit, since the statement does not mention it. It is the case
`Λ = 0` of `JumpDiffusionProcess.integral_logContract_of_martingale` and
`JumpDiffusionProcess.logContract_sub_realizedVariance_of_martingale`, through
`IsFilteredPreBrownian.jumpDiffusionProcess`, and the expected realized variance
`σ²T + (r − σ²/2)²T²/(n + 1)` it implies is the form on `ℝ≥0` of
`expected_bsLogPrice_equipartition_sum`. -/
theorem logContract_realizedVariance {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (𝓕 : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ} [hB : IsFilteredPreBrownian B 𝓕 P] {S r σ : ℝ}
    (hS : 0 < S) {T : ℝ≥0} (hT : 0 < T) :
    2 / T * ∫ ω, (Real.log (S * rexp (r * T) / (S * rexp ((r - σ ^ 2 / 2) * T + σ * B T ω)))
        + (S * rexp ((r - σ ^ 2 / 2) * T + σ * B T ω) - S * rexp (r * T)) / (S * rexp (r * T)))
          ∂P = σ ^ 2 ∧
    ∀ n : ℕ, 2 / T * ∫ ω, (Real.log (S * rexp (r * T) / (S * rexp ((r - σ ^ 2 / 2) * T
          + σ * B T ω)))
        + (S * rexp ((r - σ ^ 2 / 2) * T + σ * B T ω) - S * rexp (r * T)) / (S * rexp (r * T)))
          ∂P
      - (∫ ω, ∑ k ∈ Finset.range (n + 1),
          ((r - σ ^ 2 / 2) * ((k + 1) * T / (n + 1) : ℝ≥0) + σ * B ((k + 1) * T / (n + 1)) ω
            - ((r - σ ^ 2 / 2) * (k * T / (n + 1) : ℝ≥0) + σ * B (k * T / (n + 1)) ω)) ^ 2 ∂P)
          / T
      = -((r - σ ^ 2 / 2) ^ 2 * T / (n + 1)) := by
  have h := hB.jumpDiffusionProcess (r - σ ^ 2 / 2) σ (gaussianReal 0 1)
  have hν : 0 ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
    rw [integrableExpSet_id_gaussianReal, interior_univ]
    exact Set.mem_univ 0
  have hM := (h.martingale_iff (integrable_exp_gaussianReal 0 1) hS.ne' r).2
    (by rw [NNReal.coe_zero, zero_mul, sub_zero])
  refine ⟨?_, fun n ↦ ?_⟩
  · have h1 := h.integral_logContract_of_martingale hν (integrable_exp_gaussianReal 0 1) hS hM hT
    simp only [NNReal.coe_zero, mul_zero, zero_mul, add_zero] at h1
    exact h1
  · have h2 := h.logContract_sub_realizedVariance_of_martingale hν (integrable_exp_gaussianReal 0 1)
      hS hM hT n
    simp only [NNReal.coe_zero, mul_zero, zero_mul, add_zero, zero_sub] at h2
    exact h2

end ProbabilityTheory.IsFilteredPreBrownian
