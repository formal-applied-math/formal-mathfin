/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.JumpDiffusionMoments
public import MathFin.BlackScholes.VarianceSwap

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
* `jumpDiffusion_logContract_le_variance` and `jumpDiffusion_logContract_lt_variance`: for jumps
  `≤ 0` the log contract is at most the variance, and strictly below it if `Λ > 0` and the jumps
  are negative with positive probability: `e^x ≤ 1 + x + x²/2` for `x ≤ 0`, strictly for `x < 0`
  (`Real.exp_le_quadratic_of_nonpos`, `Real.exp_lt_quadratic_of_neg`).

For a jump-diffusion process `X` (`JumpDiffusionProcess`, a hypothesis structure whose existence
with jumps is not proved), the expected realized variance along equipartitions of `[0, T]` tends to
the variance of the log-return over `T`, whatever the drift, as in Black–Scholes
(`expected_bsLogPrice_equipartition_sum`, `tendsto_expected_bsLogPrice_equipartition_sum`):

* `integral_sum_comp_increment_equipartition`: for any process whose increments have laws that
  depend only on their length, `𝔼[∑ f(ΔX)]` along `n + 1` equal steps is `n + 1` times the mean of
  `f` under the law of one step;
* `JumpDiffusionProcess.integral_sum_sq_increment_equipartition`: so the expected realized variance
  is `(σ² + Λ𝔼[J²])T + (b + Λ𝔼[J])²T²/(n + 1)`;
* `JumpDiffusionProcess.tendsto_integral_sum_sq_increment_equipartition`: it tends to
  `(σ² + Λ𝔼[J²])T`;
* `JumpDiffusionProcess.tendsto_logContract_sub_realizedVariance`: so the log contract minus the
  expected realized variance per unit time tends to the jump bias, where Black–Scholes has `0`
  (`varianceSwap_log_eq_QV_limit_value`).

The limit per unit time is the swap's fair strike when `σ`, `Λ` and `ν` are the characteristics
under a pricing measure: the drift of `X` drops out of the limit, but a change of measure that
moves `Λ` or `ν`, such as the Esscher transform, is not covered.
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
(`jumpDiffusion_logContract_sub_variance`) is `≤ 0`, as `e^x ≤ 1 + x + x²/2` for `x ≤ 0`
(`Real.exp_le_quadratic_of_nonpos`). -/
theorem jumpDiffusion_logContract_le_variance {S r b σ : ℝ} (hS : 0 < S) {Λ : ℝ≥0}
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (hJ : ∀ᵐ x ∂ν, x ≤ 0) (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {τ : ℝ≥0}
    (hτ : 0 < τ) :
    2 / τ * ∫ y, (Real.log (S * rexp (r * τ) / (S * rexp y))
        + (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ)))
      ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      ≤ Var[id; jumpDiffusionIncrementLaw b σ Λ ν τ] / τ := by
  have hle : ∀ᵐ x ∂ν, rexp x - 1 - x - x ^ 2 / 2 ≤ 0 :=
    hJ.mono fun x hx ↦ by linarith [Real.exp_le_quadratic_of_nonpos hx]
  rw [← sub_nonpos,
    jumpDiffusion_logContract_sub_variance hS hν (integrable_exp_of_ae_nonpos hJ) hb hτ]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (integral_nonpos_of_ae hle)

/-- **With crash jumps the log contract is strictly below the variance.** If moreover `Λ > 0` and
the jumps are negative with positive probability (`ν {J < 0} ≠ 0`), the inequality of
`jumpDiffusion_logContract_le_variance` is strict: `e^x < 1 + x + x²/2` for `x < 0`
(`Real.exp_lt_quadratic_of_neg`), so the jump bias is negative. -/
theorem jumpDiffusion_logContract_lt_variance {S r b σ : ℝ} (hS : 0 < S) {Λ : ℝ≥0} (hΛ : 0 < Λ)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (hJ : ∀ᵐ x ∂ν, x ≤ 0) (hJ' : ν {x | x < 0} ≠ 0)
    (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {τ : ℝ≥0} (hτ : 0 < τ) :
    2 / τ * ∫ y, (Real.log (S * rexp (r * τ) / (S * rexp y))
        + (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ)))
      ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      < Var[id; jumpDiffusionIncrementLaw b σ Λ ν τ] / τ := by
  have hν1 := integrable_exp_of_ae_nonpos hJ
  have hJ1 : Integrable (fun x ↦ x) ν := integrable_of_mem_interior_integrableExpSet hν
  have hJ2 : Integrable (fun x ↦ x ^ 2) ν := integrable_pow_of_mem_interior_integrableExpSet hν 2
  have hg : Integrable (fun x ↦ -(rexp x - 1 - x - x ^ 2 / 2)) ν :=
    (((hν1.sub (integrable_const 1)).sub hJ1).sub (hJ2.div_const 2)).neg
  have hle : ∀ᵐ x ∂ν, 0 ≤ -(rexp x - 1 - x - x ^ 2 / 2) :=
    hJ.mono fun x hx ↦ by linarith [Real.exp_le_quadratic_of_nonpos hx]
  -- the negated bias integrand is positive where the jumps are negative
  have hpos : 0 < ∫ x, -(rexp x - 1 - x - x ^ 2 / 2) ∂ν := by
    refine (integral_pos_iff_support_of_nonneg_ae hle hg).2 (pos_iff_ne_zero.2 fun h0 ↦
      hJ' (measure_mono_null (fun x (hx : x < 0) ↦ ?_) h0))
    exact Function.mem_support.2 (ne_of_gt (by linarith [Real.exp_lt_quadratic_of_neg hx]))
  rw [integral_neg, neg_pos] at hpos
  rw [← sub_neg, jumpDiffusion_logContract_sub_variance hS hν hν1 hb hτ]
  exact mul_neg_of_pos_of_neg (mul_pos two_pos (NNReal.coe_pos.2 hΛ)) hpos

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

/-- **With jumps the log contract misses the variance swap by the jump bias.** For a jump-diffusion
process `X` with a jump law whose moment-generating function is finite near `0` and at `1`, a spot
`S > 0` and `T > 0`, the log contract over `T` at the compensated drift `c` minus the expected
realized variance of `X` per unit time along equipartitions of `[0, T]` tends to the jump bias
`2Λ𝔼[e^J − 1 − J − J²/2]`: the expected realized variance tends to the variance of the log-return
over `T` (`tendsto_integral_sum_sq_increment_equipartition`), and the log contract differs from
that by the bias (`jumpDiffusion_logContract_sub_variance`). The log contract is stated for the law
of the log-return at the compensated drift, which is the law of `X_T` when `X` has that drift, that
is, when the discounted price is a martingale (`JumpDiffusionProcess.martingale_iff`); the limit of
the expected realized variance does not depend on the drift `b` of `X`. In Black–Scholes the limit
is `0` (`varianceSwap_log_eq_QV_limit_value`). -/
theorem tendsto_logContract_sub_realizedVariance (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν)
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (hν1 : Integrable rexp ν) {S r c : ℝ} (hS : 0 < S)
    (hc : c = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ ↦
        2 / T * ∫ y, (Real.log (S * rexp (r * T) / (S * rexp y))
            + (S * rexp y - S * rexp (r * T)) / (S * rexp (r * T)))
          ∂(jumpDiffusionIncrementLaw c σ Λ ν T)
        - (∫ ω, ∑ k ∈ Finset.range (n + 1),
            (X ((k + 1) * T / (n + 1)) ω - X (k * T / (n + 1)) ω) ^ 2 ∂P) / T)
      atTop (𝓝 (2 * Λ * ∫ x, (rexp x - 1 - x - x ^ 2 / 2) ∂ν)) := by
  have h1 : Tendsto (fun n : ℕ ↦ (∫ ω, ∑ k ∈ Finset.range (n + 1),
        (X ((k + 1) * T / (n + 1)) ω - X (k * T / (n + 1)) ω) ^ 2 ∂P) / T) atTop
      (𝓝 (Var[id; jumpDiffusionIncrementLaw c σ Λ ν T] / T)) := by
    rw [variance_id_jumpDiffusionIncrementLaw c σ Λ hν T]
    exact (h.tendsto_integral_sum_sq_increment_equipartition hν T).div_const _
  rw [← jumpDiffusion_logContract_sub_variance hS hν hν1 hc hT]
  exact h1.const_sub _

end JumpDiffusionProcess

end MathFin
