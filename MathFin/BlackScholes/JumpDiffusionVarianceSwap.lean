/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.JumpDiffusionProcess
public import MathFin.BlackScholes.VarianceSwap

/-!
# Variance swaps with jumps: the log contract no longer prices the variance

In the Black–Scholes model two functionals of the price give the variance swap's fair strike
`σ²`: the log contract of Demeterfi, Derman, Kamal and Zou, `(2/τ)·𝔼[log(F/S_τ) + (S_τ − F)/F]`
with the forward `F = Se^{rτ}` (`varianceSwap_fairStrike`), and the expected realized variance
(`tendsto_expected_bsLogPrice_equipartition_sum`); `VarianceSwapEquivalence.lean` records that
they agree. With jumps they do not.

The moments of the jump-diffusion log-return `Y` over `τ` are the derivatives at `0` of its
cumulant generating function `κ(θ)τ` (`cgf_id_jumpDiffusionIncrementLaw`), for a jump law with
exponential moments near `0` (Mathlib's `deriv_cgf_zero`, `iteratedDeriv_two_cgf` and
`iteratedDeriv_two_cgf_eq_integral`):

* `integral_id_jumpDiffusionIncrementLaw`: `𝔼[Y] = (b + Λ𝔼[J])τ`;
* `variance_id_jumpDiffusionIncrementLaw`: `Var[Y] = (σ² + Λ𝔼[J²])τ`, the jump-diffusion form of
  Mathlib's `variance_id_gaussianReal`;
* `integral_sq_jumpDiffusionIncrementLaw`: `𝔼[Y²] = (σ² + Λ𝔼[J²])τ + ((b + Λ𝔼[J])τ)²`.

At the compensated drift `b = r − σ²/2 − Λ(𝔼[e^J] − 1)`, with `𝔼[e^J] < ∞`:

* `jumpDiffusion_logContract`: the log contract is worth `σ² + 2Λ𝔼[e^J − 1 − J]`: it prices the
  gap `log F − 𝔼[log S_τ]` (`integral_logContract`), which with jumps is not half the variance;
* `jumpDiffusion_logContract_sub_variance`: it exceeds the variance of the log-return per unit
  time, `σ² + Λ𝔼[J²]`, by `2Λ𝔼[e^J − 1 − J − J²/2]`; without jumps they agree;
* `jumpDiffusion_logContract_le_variance`: with downward jumps (`J ≤ 0`) the log contract is at
  most the variance, since `e^x ≤ 1 + x + x²/2` for `x ≤ 0` (`Real.exp_le_quadratic_of_nonpos`).

The variance of the log-return is the expected realized variance of the log-price over `[0, τ]`
only in the limit of fine partitions; that limit is not taken here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped NNReal Topology

/-- `eˣ ≤ 1 + x + x²/2` for `x ≤ 0`, the reverse of Mathlib's `Real.quadratic_le_exp_of_nonneg`:
`eˣ − (1 + x + x²/2)` is nondecreasing, its derivative `eˣ − (1 + x)` being nonnegative
(`Real.add_one_le_exp`), and vanishes at `0`. -/
theorem Real.exp_le_quadratic_of_nonpos {x : ℝ} (hx : x ≤ 0) : rexp x ≤ 1 + x + x ^ 2 / 2 := by
  have hsq (y : ℝ) : HasDerivAt (fun y : ℝ ↦ y ^ 2 / 2) y y := by
    have h := (hasDerivAt_pow 2 y).div_const 2
    norm_num at h
    exact h
  have hd (y : ℝ) : HasDerivAt (fun y ↦ rexp y - (1 + y + y ^ 2 / 2)) (rexp y - (1 + y)) y :=
    (Real.hasDerivAt_exp y).fun_sub (((hasDerivAt_id' y).const_add 1).fun_add (hsq y))
  have hmono : Monotone fun y ↦ rexp y - (1 + y + y ^ 2 / 2) :=
    monotone_of_deriv_nonneg (fun y ↦ (hd y).differentiableAt) fun y ↦ by
      rw [(hd y).deriv]
      linarith [Real.add_one_le_exp y]
  have h : rexp x - (1 + x + x ^ 2 / 2) ≤ rexp 0 - (1 + 0 + 0 ^ 2 / 2) := hmono hx
  norm_num at h
  linarith

namespace MathFin

/-! ### The moments of the log-return -/

/-- **The log-return inherits the exponential moments of the jumps**: where `∫ e^{θx} dν < ∞`,
`∫ e^{θy}` is finite under the log-return law (`integrable_exp_mul_jumpDiffusionIncrementLaw`). -/
lemma zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (τ : ℝ≥0) : 0 ∈ interior (integrableExpSet id (jumpDiffusionIncrementLaw b σ Λ ν τ)) := by
  have hD : ∀ᶠ θ in 𝓝 (0 : ℝ), Integrable (fun x ↦ rexp (θ * x)) ν :=
    eventually_mem_set.2 (mem_interior_iff_mem_nhds.1 hν)
  have hint : ∀ᶠ θ in 𝓝 (0 : ℝ),
      Integrable (fun y ↦ rexp (θ * y)) (jumpDiffusionIncrementLaw b σ Λ ν τ) :=
    hD.mono fun θ hθ ↦ integrable_exp_mul_jumpDiffusionIncrementLaw b σ Λ hθ τ
  exact mem_interior_iff_mem_nhds.2 hint

/-- **Near `0` the cumulant generating function of the log-return is `κ(θ)τ`**
(`cgf_id_jumpDiffusionIncrementLaw` at every `θ` where the jump law has an exponential moment). -/
lemma cgf_id_jumpDiffusionIncrementLaw_eventuallyEq (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν)) (τ : ℝ≥0) :
    cgf id (jumpDiffusionIncrementLaw b σ Λ ν τ) =ᶠ[𝓝 0]
      fun θ ↦ jumpDiffusionExponent b σ Λ ν θ * τ := by
  have hD : ∀ᶠ θ in 𝓝 (0 : ℝ), Integrable (fun x ↦ rexp (θ * x)) ν :=
    eventually_mem_set.2 (mem_interior_iff_mem_nhds.1 hν)
  exact hD.mono fun θ hθ ↦ cgf_id_jumpDiffusionIncrementLaw b σ Λ hθ τ

/-- **The derivative of the Laplace exponent**: where the jump law has exponential moments,
`κ'(θ) = b + σ²θ + ΛM'(θ)`, with `M` the moment-generating function of the jump law. -/
lemma hasDerivAt_jumpDiffusionExponent (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ} {θ : ℝ}
    (hθ : θ ∈ interior (integrableExpSet id ν)) :
    HasDerivAt (jumpDiffusionExponent b σ Λ ν) (b + σ ^ 2 * θ + Λ * deriv (mgf id ν) θ) θ := by
  have hsq : HasDerivAt (fun θ : ℝ ↦ θ ^ 2) (2 * θ) θ := by simpa using hasDerivAt_pow 2 θ
  exact ((((hasDerivAt_id' θ).const_mul b).fun_add ((hsq.const_mul (σ ^ 2)).div_const 2)).fun_add
    (((differentiableAt_mgf hθ).hasDerivAt.sub_const 1).const_mul (Λ : ℝ))).congr_deriv (by ring)

/-- The second derivative at `0` of `θ ↦ κ(θ)τ` is `(σ² + Λ𝔼[J²])τ`: `κ''(0) = σ² + ΛM''(0)`
and `M''(0) = 𝔼[J²]` (Mathlib's `hasDerivAt_iteratedDeriv_mgf`). -/
lemma iteratedDeriv_two_jumpDiffusionExponent_mul (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    (hν : 0 ∈ interior (integrableExpSet id ν)) (τ : ℝ≥0) :
    iteratedDeriv 2 (fun θ ↦ jumpDiffusionExponent b σ Λ ν θ * τ) 0
      = (σ ^ 2 + Λ * ∫ x, x ^ 2 ∂ν) * τ := by
  have h2 := hasDerivAt_iteratedDeriv_mgf hν 1
  rw [iteratedDeriv_one] at h2
  have hd : deriv (fun θ ↦ jumpDiffusionExponent b σ Λ ν θ * τ) =ᶠ[𝓝 0]
      fun θ ↦ (b + σ ^ 2 * θ + Λ * deriv (mgf id ν) θ) * τ :=
    eventuallyEq_of_mem (isOpen_interior.mem_nhds hν) fun θ hθ ↦
      ((hasDerivAt_jumpDiffusionExponent b σ Λ hθ).mul_const (τ : ℝ)).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq,
    ((((hasDerivAt_id' (0 : ℝ)).const_mul (σ ^ 2)).const_add b).fun_add
      (h2.const_mul (Λ : ℝ))).mul_const (τ : ℝ)).deriv]
  simp

/-- **The mean of the jump-diffusion log-return**: `𝔼[Y] = (b + Λ𝔼[J])τ` for a jump law with
exponential moments near `0`. It is the derivative at `0` of the cumulant generating function
`κ(θ)τ` (Mathlib's `deriv_cgf_zero`), and `κ'(0) = b + Λ𝔼[J]` (`deriv_mgf_zero`). Without jumps
it is `bτ`, the mean of the Gaussian law `N(bτ, σ²τ)` (Mathlib's `integral_id_gaussianReal`). -/
theorem integral_id_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν)) (τ : ℝ≥0) :
    ∫ y, y ∂(jumpDiffusionIncrementLaw b σ Λ ν τ) = (b + Λ * ∫ x, x ∂ν) * τ := by
  have h := deriv_cgf_zero
    (zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw b σ Λ hν τ)
  rw [(cgf_id_jumpDiffusionIncrementLaw_eventuallyEq b σ Λ hν τ).deriv_eq,
    ((hasDerivAt_jumpDiffusionExponent b σ Λ hν).mul_const (τ : ℝ)).deriv,
    deriv_mgf_zero hν] at h
  simpa using h.symm

/-- **The variance of the jump-diffusion log-return**: `Var[Y] = (σ² + Λ𝔼[J²])τ` for a jump law
with exponential moments near `0`. It is the second derivative at `0` of the cumulant generating
function `κ(θ)τ` (Mathlib's `iteratedDeriv_two_cgf_eq_integral`). The Gaussian part contributes
`σ²τ`, the variance of `N(bτ, σ²τ)` (Mathlib's `variance_id_gaussianReal`), and the jumps
`Λ𝔼[J²]τ`. -/
theorem variance_id_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν)) (τ : ℝ≥0) :
    Var[id; jumpDiffusionIncrementLaw b σ Λ ν τ] = (σ ^ 2 + Λ * ∫ x, x ^ 2 ∂ν) * τ := by
  have hμ := zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw b σ Λ hν τ
  have h := iteratedDeriv_two_cgf_eq_integral hμ
  rw [(cgf_id_jumpDiffusionIncrementLaw_eventuallyEq b σ Λ hν τ).iteratedDeriv_eq 2,
    iteratedDeriv_two_jumpDiffusionExponent_mul b σ Λ hν τ, deriv_cgf_zero hμ, mgf_zero] at h
  rw [variance_eq_integral measurable_id.aemeasurable]
  simpa using h.symm

/-- **The second moment of the jump-diffusion log-return**:
`𝔼[Y²] = (σ² + Λ𝔼[J²])τ + ((b + Λ𝔼[J])τ)²`, the variance plus the squared mean (Mathlib's
`iteratedDeriv_two_cgf`). -/
theorem integral_sq_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν)) (τ : ℝ≥0) :
    ∫ y, y ^ 2 ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      = (σ ^ 2 + Λ * ∫ x, x ^ 2 ∂ν) * τ + ((b + Λ * ∫ x, x ∂ν) * τ) ^ 2 := by
  have hμ := zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw b σ Λ hν τ
  have h := iteratedDeriv_two_cgf hμ
  rw [(cgf_id_jumpDiffusionIncrementLaw_eventuallyEq b σ Λ hν τ).iteratedDeriv_eq 2,
    iteratedDeriv_two_jumpDiffusionExponent_mul b σ Λ hν τ, deriv_cgf_zero hμ, mgf_zero] at h
  rw [← integral_id_jumpDiffusionIncrementLaw b σ Λ hν τ]
  simp only [id_eq, zero_mul, Real.exp_zero, mul_one, div_one, probReal_univ] at h
  linarith

/-! ### The log contract -/

/-- **The log contract with jumps.** At the compensated drift `b = r − σ²/2 − Λ(𝔼[e^J] − 1)`, for a
jump law with `𝔼[e^J] < ∞` and exponential moments near `0`, `S > 0` and `τ > 0`, the
Demeterfi–Derman–Kamal–Zou log contract on the forward `F = Se^{rτ}` is worth
`(2/τ)·𝔼[log(F/S_τ) + (S_τ − F)/F] = σ² + 2Λ𝔼[e^J − 1 − J]`. It prices `(2/τ)(rτ − 𝔼[Y])`
(`integral_logContract`), the forward being the mean of `S_τ`
(`integral_exp_jumpDiffusionIncrementLaw`), and `𝔼[Y] = (b + Λ𝔼[J])τ`
(`integral_id_jumpDiffusionIncrementLaw`). Without jumps it is `σ²`, the Black–Scholes value
(`varianceSwap_fairStrike`). -/
theorem jumpDiffusion_logContract {S r σ : ℝ} (hS : 0 < S) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (hν1 : Integrable rexp ν) {τ : ℝ≥0} (hτ : 0 < τ) :
    2 / τ * ∫ y, (Real.log (S * rexp (r * τ) / (S * rexp y))
        + (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ)))
      ∂(jumpDiffusionIncrementLaw (r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) σ Λ ν τ)
      = σ ^ 2 + 2 * Λ * ∫ x, (rexp x - 1 - x) ∂ν := by
  have hF : ∫ y, rexp y
      ∂(jumpDiffusionIncrementLaw (r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) σ Λ ν τ)
      = rexp (r * τ) := by
    rw [integral_exp_jumpDiffusionIncrementLaw _ σ Λ hν1 τ]
    congr 1
    ring
  have hJ : Integrable (fun x ↦ x) ν := integrable_of_mem_interior_integrableExpSet hν
  have hE1 : Integrable (fun x ↦ rexp x - 1) ν := hν1.sub (integrable_const 1)
  rw [integral_logContract hS r τ (integrable_of_mem_interior_integrableExpSet
      (zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw _ σ Λ hν τ))
      (integrable_exp_jumpDiffusionIncrementLaw _ σ Λ hν1 τ), hF, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, integral_id_jumpDiffusionIncrementLaw _ σ Λ hν τ,
    integral_sub hE1 hJ, integral_sub hν1 (integrable_const 1), integral_const, probReal_univ,
    one_smul, div_mul_eq_mul_div, div_eq_iff (NNReal.coe_ne_zero.2 hτ.ne')]
  ring

/-- **The jump bias of the log contract.** Under the hypotheses of `jumpDiffusion_logContract`,
the log contract exceeds the variance of the log-return per unit time, `Var[Y]/τ = σ² + Λ𝔼[J²]`
(`variance_id_jumpDiffusionIncrementLaw`), by `2Λ𝔼[e^J − 1 − J − J²/2]`, a third-order term in the
jumps. Without jumps (`Λ = 0`) the two agree. -/
theorem jumpDiffusion_logContract_sub_variance {S r σ : ℝ} (hS : 0 < S) (Λ : ℝ≥0)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (hν1 : Integrable rexp ν) {τ : ℝ≥0} (hτ : 0 < τ) :
    2 / τ * ∫ y, (Real.log (S * rexp (r * τ) / (S * rexp y))
        + (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ)))
      ∂(jumpDiffusionIncrementLaw (r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) σ Λ ν τ)
      - Var[id; jumpDiffusionIncrementLaw (r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) σ Λ ν τ]
        / τ
      = 2 * Λ * ∫ x, (rexp x - 1 - x - x ^ 2 / 2) ∂ν := by
  have hJ : Integrable (fun x ↦ x) ν := integrable_of_mem_interior_integrableExpSet hν
  have hJ2 : Integrable (fun x ↦ x ^ 2) ν := integrable_pow_of_mem_interior_integrableExpSet hν 2
  have hE1 : Integrable (fun x ↦ rexp x - 1 - x) ν := (hν1.sub (integrable_const 1)).sub hJ
  rw [jumpDiffusion_logContract hS Λ hν hν1 hτ, variance_id_jumpDiffusionIncrementLaw _ σ Λ hν τ,
    mul_div_cancel_right₀ _ (NNReal.coe_ne_zero.2 hτ.ne'), integral_sub hE1 (hJ2.div_const 2),
    integral_div]
  ring

/-- **With downward jumps the log contract is at most the variance.** If the jumps are
nonpositive (`J ≤ 0` `ν`-a.e.), then under the hypotheses of `jumpDiffusion_logContract` the log
contract is at most the variance of the log-return per unit time: the jump bias
`2Λ𝔼[e^J − 1 − J − J²/2]` (`jumpDiffusion_logContract_sub_variance`) is `≤ 0`, as
`e^x ≤ 1 + x + x²/2` for `x ≤ 0` (`Real.exp_le_quadratic_of_nonpos`). -/
theorem jumpDiffusion_logContract_le_variance {S r σ : ℝ} (hS : 0 < S) (Λ : ℝ≥0)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (hν1 : Integrable rexp ν) (hJ : ∀ᵐ x ∂ν, x ≤ 0) {τ : ℝ≥0} (hτ : 0 < τ) :
    2 / τ * ∫ y, (Real.log (S * rexp (r * τ) / (S * rexp y))
        + (S * rexp y - S * rexp (r * τ)) / (S * rexp (r * τ)))
      ∂(jumpDiffusionIncrementLaw (r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) σ Λ ν τ)
      ≤ Var[id; jumpDiffusionIncrementLaw (r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) σ Λ ν τ]
        / τ := by
  have h := jumpDiffusion_logContract_sub_variance (r := r) (σ := σ) hS Λ hν hν1 hτ
  have hle : ∀ᵐ x ∂ν, rexp x - 1 - x - x ^ 2 / 2 ≤ 0 :=
    hJ.mono fun x hx ↦ by linarith [Real.exp_le_quadratic_of_nonpos hx]
  have hbias := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 2 * Λ)
    (integral_nonpos_of_ae hle)
  linarith

end MathFin
