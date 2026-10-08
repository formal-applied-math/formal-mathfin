/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.JumpDiffusionMerton
public import MathFin.BlackScholes.JumpDiffusionBrownian
public import MathFin.Foundations.Esscher

/-!
# The Esscher transform of a jump-diffusion

The Esscher transform with parameter `θ` reweights a law by `e^{θy}` and renormalizes it
(`Foundations/Esscher.lean`, on Mathlib's `Measure.tilted`). Here it acts on the log-return law
over `τ` of a jump-diffusion with drift `b`, volatility coefficient `σ`, jump rate `Λ` and jump
law `ν` (`jumpDiffusionIncrementLaw`), whose Laplace exponent is `κ` (`jumpDiffusionExponent`).

* `jumpDiffusionIncrementLaw_tilted`: when `ν` has exponential moments of every order, the tilted
  law is again a jump-diffusion log-return law. The drift becomes `b + θσ²`, `σ` is unchanged, the
  rate becomes `Λ·m(θ)` with `m(θ) = ∫ e^{θx} dν` (`jumpMoment`), and the jump law is tilted the
  same way. The proof compares moment-generating functions (`measure_eq_of_mgf_id_eq`): both laws
  have the moment-generating function `u ↦ e^{(κ(u + θ) − κ(θ))τ}`, since `κ(u + θ) − κ(θ)` is the
  Laplace exponent of the tilted characteristics (`jumpDiffusionExponent_tilted`).
* `compensated_tilted_iff`: the tilted characteristics are at their compensated drift exactly
  when `κ(θ + 1) − κ(θ) = r`, the Esscher condition.
* `integral_call_tilted_eq_merton`: at such a `θ`, the call integrated against the tilted law is
  Merton's formula for the tilted jump law (`jumpDiffusionCallPrice_eq_merton`).
* `integral_call_tilted_eq_mertonCallPrice`: tilting keeps Merton's lognormal jumps lognormal
  (`mertonJump_tilted`), so in Merton's model the same integral is Merton's 1976 series with a
  shifted jump mean.
* `integral_call_tilted_zero_eq_bsV`: with no jumps the log-return law is Gaussian, and its
  Esscher transform is the Gaussian tilt that also gives the static Girsanov theorem
  (`gaussianReal_tilted_const_mul`, behind `gaussianReal_withDensity_esscher`). The Esscher
  parameter is `θ = (r − b − σ²/2)/σ²` (`jumpDiffusionExponent_zero_esscher`), and the price is the
  Black–Scholes formula.

The statements are about the law at one date, not about the process under a changed measure. With
jumps (`Λ > 0`) the market is in general incomplete (not formalized here), and the Esscher law is
then one pricing law among others. The existence of an Esscher parameter is proved only without
jumps.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- The exponential moment `m(θ) = ∫ e^{θx} dν` of a jump law, as a nonnegative real (the Bochner
integral, so `0` where the moment is infinite). -/
noncomputable def jumpMoment (ν : Measure ℝ) (θ : ℝ) : ℝ≥0 :=
  ⟨∫ x, rexp (θ * x) ∂ν, integral_nonneg fun _ ↦ (Real.exp_pos _).le⟩

/-- **The Laplace exponent of the Esscher-tilted characteristics.** Tilting turns the
characteristics `(b, σ, Λ, ν)` into `(b + θσ², σ, Λ·m(θ), ν.tilted (θ * ·))`, whose
`jumpDiffusionExponent` at every `u` is `κ(u + θ) − κ(θ)`. It is their Laplace exponent at `u`
where `∫ e^{(u + θ)x} dν < ∞`. -/
lemma jumpDiffusionExponent_tilted (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : Integrable (fun x ↦ rexp (θ * x)) ν) (u : ℝ) :
    jumpDiffusionExponent (b + θ * σ ^ 2) σ (Λ * jumpMoment ν θ) (ν.tilted (θ * ·)) u
      = jumpDiffusionExponent b σ Λ ν (u + θ) - jumpDiffusionExponent b σ Λ ν θ := by
  have hm : (∫ x, rexp (θ * x) ∂ν) ≠ 0 := (integral_exp_pos hθ).ne'
  have hΛm : ((Λ * jumpMoment ν θ : ℝ≥0) : ℝ) = Λ * ∫ x, rexp (θ * x) ∂ν := rfl
  simp only [jumpDiffusionExponent, integral_exp_mul_tilted_const_mul, hΛm]
  field_simp
  ring

/-- **The Esscher transform of a jump-diffusion log-return law.** When the jump law has
exponential moments of every order, tilting the log-return law over `τ` by `e^{θy}` gives the
log-return law with drift `b + θσ²`, the same volatility coefficient, the rate `Λ·m(θ)` and the
tilted jump law `ν.tilted (θ * ·)`. -/
theorem jumpDiffusionIncrementLaw_tilted (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : ∀ u, Integrable (fun x ↦ rexp (u * x)) ν) (θ : ℝ) (τ : ℝ≥0) :
    (jumpDiffusionIncrementLaw b σ Λ ν τ).tilted (θ * ·)
      = jumpDiffusionIncrementLaw (b + θ * σ ^ 2) σ (Λ * jumpMoment ν θ) (ν.tilted (θ * ·)) τ := by
  have hμ (u : ℝ) := integrable_exp_mul_jumpDiffusionIncrementLaw b σ Λ (hν u) τ
  have : IsProbabilityMeasure ((jumpDiffusionIncrementLaw b σ Λ ν τ).tilted (θ * ·)) :=
    isProbabilityMeasure_tilted (hμ θ)
  have : IsProbabilityMeasure (ν.tilted (θ * ·)) := isProbabilityMeasure_tilted (hν θ)
  refine measure_eq_of_mgf_id_eq (integrable_exp_mul_tilted_const_mul hμ θ) (funext fun u ↦ ?_)
  rw [mgf_id_jumpDiffusionIncrementLaw _ _ _ (integrable_exp_mul_tilted_const_mul hν θ u),
    jumpDiffusionExponent_tilted b σ Λ (hν θ) u]
  simp only [mgf, id_eq]
  rw [integral_exp_mul_tilted_const_mul,
    integral_exp_const_mul_jumpDiffusionIncrementLaw b σ Λ (hν (u + θ)),
    integral_exp_const_mul_jumpDiffusionIncrementLaw b σ Λ (hν θ), ← Real.exp_sub, sub_mul]

/-- **The Esscher condition.** The tilted characteristics are at their compensated drift,
`b + θσ² = r − σ²/2 − Λm(θ)(∫ eˣ d(ν tilted) − 1)`, exactly when `κ(θ + 1) − κ(θ) = r`. -/
lemma compensated_tilted_iff (b σ r : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : Integrable (fun x ↦ rexp (θ * x)) ν) :
    b + θ * σ ^ 2 = r - σ ^ 2 / 2
        - (Λ * jumpMoment ν θ : ℝ≥0) * (∫ x, rexp x ∂(ν.tilted (θ * ·)) - 1)
      ↔ jumpDiffusionExponent b σ Λ ν (1 + θ) - jumpDiffusionExponent b σ Λ ν θ = r := by
  rw [← jumpDiffusionExponent_tilted b σ Λ hθ 1, jumpDiffusionExponent]
  simp only [one_mul, mul_one, one_pow]
  constructor <;> intro h <;> linarith

/-- **Esscher pricing of the call.** At an Esscher parameter, `κ(θ + 1) − κ(θ) = r`, the
discounted call payoff integrated against the Esscher-tilted log-return law is Merton's formula
for the tilted characteristics: the `Poisson(Λm(θ)τ)` mixture of Black–Scholes prices over jumps
of law `ν.tilted (θ * ·)` (`jumpDiffusionCallPrice_eq_merton`). -/
theorem integral_call_tilted_eq_merton {S K r b σ : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ)
    {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∀ u, Integrable (fun x ↦ rexp (u * x)) ν) {θ : ℝ}
    (hθ : jumpDiffusionExponent b σ Λ ν (1 + θ) - jumpDiffusionExponent b σ Λ ν θ = r)
    {τ : ℝ≥0} (hτ : 0 < τ) :
    ∫ y, rexp (-r * τ) * max (S * rexp y - K) 0
        ∂((jumpDiffusionIncrementLaw b σ Λ ν τ).tilted (θ * ·))
      = ∫ n, ∫ j, bsV K r σ (S * rexp (-((Λ * jumpMoment ν θ : ℝ≥0) * τ
          * (∫ x, rexp x ∂(ν.tilted (θ * ·)) - 1)) + ∑ i ∈ Finset.range n, j i)) τ
          ∂(Measure.infinitePi fun _ : ℕ ↦ ν.tilted (θ * ·))
          ∂(poissonMeasure (Λ * jumpMoment ν θ * τ)) := by
  have : IsProbabilityMeasure (ν.tilted (θ * ·)) := isProbabilityMeasure_tilted (hν θ)
  rw [jumpDiffusionIncrementLaw_tilted b σ Λ hν θ τ]
  exact jumpDiffusionCallPrice_eq_merton hS hK hσ
    (by simpa only [one_mul] using integrable_exp_mul_tilted_const_mul hν θ 1)
    ((compensated_tilted_iff b σ r Λ (hν θ)).2 hθ) hτ

/-- **Tilting keeps Merton's jumps lognormal**: Merton's log-jump law `N(log(1 + k) − δ²/2, δ²)`
tilted by `e^{θx}` is Merton's log-jump law with the jump mean `(1 + k)e^{θδ²} − 1`
(`gaussianReal_tilted_const_mul`). -/
lemma mertonJump_tilted {k : ℝ} (hk : -1 < k) (δ θ : ℝ) :
    (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal).tilted (θ * ·)
      = gaussianReal (Real.log (1 + ((1 + k) * rexp (θ * δ ^ 2) - 1)) - δ ^ 2 / 2)
          (δ ^ 2).toNNReal := by
  rw [gaussianReal_tilted_const_mul, Real.coe_toNNReal _ (sq_nonneg δ), add_sub_cancel,
    Real.log_mul (show (0 : ℝ) < 1 + k by linarith).ne' (Real.exp_pos _).ne', Real.log_exp]
  congr 1
  ring

/-- **Esscher pricing in Merton's model.** With Merton's log-jumps `N(log(1 + k) − δ²/2, δ²)`, at
an Esscher parameter the call integrated against the tilted log-return law is Merton's 1976 series
with the jump mean `k' = (1 + k)e^{θδ²} − 1` and the expected jump count `Λm(θ)τ`: the tilted jumps
are Merton's with jump mean `k'` (`mertonJump_tilted`), and
`jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice` applies. -/
theorem integral_call_tilted_eq_mertonCallPrice {S K r b σ k δ : ℝ} (hS : 0 < S) (hK : 0 < K)
    (hσ : 0 < σ) (hk : -1 < k) {Λ : ℝ≥0} {θ : ℝ}
    (hθ : jumpDiffusionExponent b σ Λ
        (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) (1 + θ)
      - jumpDiffusionExponent b σ Λ
        (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) θ = r)
    {τ : ℝ≥0} (hτ : 0 < τ) :
    ∫ y, rexp (-r * τ) * max (S * rexp y - K) 0
        ∂((jumpDiffusionIncrementLaw b σ Λ
          (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) τ).tilted (θ * ·))
      = mertonCallPrice S K r σ τ ((1 + k) * rexp (θ * δ ^ 2) - 1) δ
          (Λ * jumpMoment (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) θ
            * τ) := by
  have hν (u : ℝ) : Integrable (fun x ↦ rexp (u * x))
      (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) :=
    integrable_exp_mul_gaussianReal u
  have hk' : -1 < (1 + k) * rexp (θ * δ ^ 2) - 1 := by
    linarith [mul_pos (show (0 : ℝ) < 1 + k by linarith) (Real.exp_pos (θ * δ ^ 2))]
  -- the Esscher condition is the compensated drift of the tilted Merton model
  have hb := (compensated_tilted_iff b σ r Λ (hν θ)).2 hθ
  rw [mertonJump_tilted hk δ θ, integral_exp_mertonJump hk' δ] at hb
  rw [jumpDiffusionIncrementLaw_tilted b σ Λ hν θ τ, mertonJump_tilted hk δ θ]
  exact jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice hS hK hσ hk'
    (by linear_combination hb) hτ

/-- **With no jumps the Esscher transform shifts the drift**: the log-return law `N(bτ, σ²τ)`
tilted by `e^{θy}` is `N((b + θσ²)τ, σ²τ)`, the log-return law with drift `b + θσ²`. It is the
Gaussian tilt of the static Girsanov theorem (`gaussianReal_tilted_const_mul`); no moment of the
jump law is needed. -/
lemma jumpDiffusionIncrementLaw_zero_tilted (b σ : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (θ : ℝ) (τ : ℝ≥0) :
    (jumpDiffusionIncrementLaw b σ 0 ν τ).tilted (θ * ·)
      = jumpDiffusionIncrementLaw (b + θ * σ ^ 2) σ 0 ν τ := by
  rw [jumpDiffusionIncrementLaw_zero, jumpDiffusionIncrementLaw_zero,
    gaussianReal_tilted_const_mul]
  congr 1
  simp only [NNReal.coe_mul, NNReal.coe_mk]
  ring

/-- **Without jumps the Esscher parameter is explicit.** At jump rate `0`, `κ(θ) = bθ + σ²θ²/2`, so
`κ(θ + 1) − κ(θ) = b + σ²/2 + σ²θ`, and `θ = (r − b − σ²/2)/σ²` satisfies the Esscher condition
`κ(θ + 1) − κ(θ) = r`. -/
lemma jumpDiffusionExponent_zero_esscher (b σ r : ℝ) (hσ : σ ≠ 0) (ν : Measure ℝ) :
    jumpDiffusionExponent b σ 0 ν (1 + (r - b - σ ^ 2 / 2) / σ ^ 2)
      - jumpDiffusionExponent b σ 0 ν ((r - b - σ ^ 2 / 2) / σ ^ 2) = r := by
  have h0 : ((0 : ℝ≥0) : ℝ) = 0 := rfl
  simp only [jumpDiffusionExponent, h0, zero_mul, add_zero]
  linear_combination div_mul_cancel₀ (r - b - σ ^ 2 / 2) (pow_ne_zero 2 hσ)

/-- **With no jumps, Esscher pricing is Black–Scholes pricing.** For any drift `b`, the Esscher
parameter `θ = (r − b − σ²/2)/σ²` (`jumpDiffusionExponent_zero_esscher`) moves the log-return law
`N(bτ, σ²τ)` to the risk-neutral `N((r − σ²/2)τ, σ²τ)` (`jumpDiffusionIncrementLaw_zero_tilted`),
and the discounted call integrated against it is the Black–Scholes price `C_BS(S, τ)`
(`jumpDiffusionCallPrice_zero`), for `S, K, σ, τ > 0`. -/
theorem integral_call_tilted_zero_eq_bsV {S K r b σ : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    ∫ y, rexp (-r * τ) * max (S * rexp y - K) 0
        ∂((jumpDiffusionIncrementLaw b σ 0 ν τ).tilted ((r - b - σ ^ 2 / 2) / σ ^ 2 * ·))
      = bsV K r σ S τ := by
  have hθ : b + (r - b - σ ^ 2 / 2) / σ ^ 2 * σ ^ 2 = r - σ ^ 2 / 2 := by
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hσ.ne')]
    ring
  rw [jumpDiffusionIncrementLaw_zero_tilted, hθ]
  exact jumpDiffusionCallPrice_zero hS hK hσ ν hτ

end MathFin
