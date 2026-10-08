/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.JumpDiffusionDigital
public import MathFin.BlackScholes.StrikeConvexity

/-!
# The jump-diffusion call price is strictly convex in the strike

The call price is convex in the strike under any law (`convexOn_integral_call`), and strictly
convex wherever the law charges every interval of strikes (`strictConvexOn_integral_call`), since a
butterfly spread pays a positive amount when the price ends strictly between its outer strikes.

With a Gaussian part (`σ ≠ 0`, `τ > 0`) the log-return density of a jump-diffusion is positive
(`jumpDiffusionDensity_pos`), so the price `Seʸ` charges every interval of positive strikes
(`jumpDiffusionIncrementLaw_price_mem_Ioo_ne_zero`), whatever the jump law.

* `convexOn_jumpDiffusionCallPrice_strike`: the call price is convex in the strike, for every
  jump-diffusion with a finite forward, `σ = 0` included.
* `strictConvexOn_jumpDiffusionCallPrice_strike`: with a Gaussian part it is strictly convex on
  `(0, ∞)`, for any jump law: every butterfly spread with positive strikes has a positive price.
* `bsV_strike_strictConvexOn`: so is the Black–Scholes call price, the jump-diffusion call price
  without jumps (`jumpDiffusionCallPrice_zero`).
* `mertonCallPrice_strictConvexOn_strike`: so is Merton's series, the jump-diffusion call price
  with Gaussian log-jumps (`jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice`), at every expected
  jump count.

With `σ = 0` the call price is convex but has a kink at the strike `Se^{bτ}`
(`not_differentiableAt_jumpDiffusionCallPrice_strike`). No strike derivative is taken here; the
spot-side counterparts `bsV_spot_strictConvexOn` and `mertonCallPrice_strictConvexOn_spot` come
from the second spot derivative.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

/-- A strictly convex function scaled by a positive constant is strictly convex: the strict
counterpart of Mathlib's `ConvexOn.smul`. -/
theorem StrictConvexOn.smul {𝕜 E β : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β]
    {s : Set E} {f : E → β} {c : 𝕜} (hc : 0 < c) (hf : StrictConvexOn 𝕜 s f) :
    StrictConvexOn 𝕜 s fun x ↦ c • f x :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab ↦
    calc c • f (a • x + b • y) < c • (a • f x + b • f y) :=
          smul_lt_smul_of_pos_left (hf.2 hx hy hxy ha hb hab) hc
      _ = a • c • f x + b • c • f y := by rw [smul_add, smul_comm c, smul_comm c]⟩

namespace MathFin

/-- **The jump-diffusion call price is convex in the strike.** For any drift, any `σ` (`σ = 0`
included), any jump law and a finite forward, `k ↦ C(S, k, τ)` is convex: it is the discount factor
times the undiscounted call price of the price `Seʸ` (`jumpDiffusionCallPrice_eq_mul_integral`),
convex under any law (`convexOn_integral_call`). -/
theorem convexOn_jumpDiffusionCallPrice_strike (S r b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (τ : ℝ≥0)
    (hY : Integrable rexp (jumpDiffusionIncrementLaw b σ Λ ν τ)) :
    ConvexOn ℝ univ fun k ↦ jumpDiffusionCallPrice S k r b σ Λ ν τ :=
  ((convexOn_integral_call (hY.const_mul S)).smul (Real.exp_pos (-r * τ)).le).congr fun k _ ↦ by
    simpa only [smul_eq_mul] using (jumpDiffusionCallPrice_eq_mul_integral S k r b σ Λ ν τ).symm

/-- **With a Gaussian part the call price is strictly convex in the strike.** For `σ ≠ 0`, `τ > 0`,
a spot `S > 0` and a finite forward, `k ↦ C(S, k, τ)` is strictly convex on `(0, ∞)`, for any jump
law: every butterfly spread with positive strikes has a positive price. The price `Seʸ` charges
every interval of positive strikes (`jumpDiffusionIncrementLaw_price_mem_Ioo_ne_zero`), so its
undiscounted call price is strictly convex there (`strictConvexOn_integral_call`), and the discount
factor is positive. -/
theorem strictConvexOn_jumpDiffusionCallPrice_strike {S r b σ : ℝ} (hS : 0 < S) (hσ : σ ≠ 0)
    {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν] {τ : ℝ≥0}
    (hY : Integrable rexp (jumpDiffusionIncrementLaw b σ Λ ν τ)) (hτ : 0 < τ) :
    StrictConvexOn ℝ (Ioi 0) fun k ↦ jumpDiffusionCallPrice S k r b σ Λ ν τ :=
  ((strictConvexOn_integral_call (hY.const_mul S) (convex_Ioi 0) fun _ hk₁ _ _ hk ↦
      jumpDiffusionIncrementLaw_price_mem_Ioo_ne_zero b hσ Λ ν hτ hS (mem_Ioi.1 hk₁).le hk).smul
    (Real.exp_pos (-r * τ))).congr fun k _ ↦ by
    simpa only [smul_eq_mul] using (jumpDiffusionCallPrice_eq_mul_integral S k r b σ Λ ν τ).symm

/-- **The Black–Scholes call price is strictly convex in the strike** on `(0, ∞)`, for `S, σ > 0`
and `τ > 0`: it is the jump-diffusion call price without jumps at the drift `r − σ²/2`
(`jumpDiffusionCallPrice_zero`). Its convexity is `bsV_strike_convexOn`. -/
theorem bsV_strike_strictConvexOn {S r σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    StrictConvexOn ℝ (Ioi 0) fun K ↦ bsV K r σ S τ := by
  lift τ to ℝ≥0 using hτ.le
  replace hτ : 0 < τ := NNReal.coe_pos.1 hτ
  exact (strictConvexOn_jumpDiffusionCallPrice_strike (r := r) hS hσ.ne'
    (integrable_exp_jumpDiffusionIncrementLaw_zero (r - σ ^ 2 / 2) σ (Measure.dirac 0) τ)
    hτ).congr fun K hK ↦ jumpDiffusionCallPrice_zero hS (mem_Ioi.1 hK) hσ (Measure.dirac 0) hτ

/-- **Merton's call series is strictly convex in the strike** on `(0, ∞)`, for `S, σ, T > 0` and
`k > −1`, at every expected jump count `Λ`: it is the jump-diffusion call price over `T` with
Gaussian log-jumps `N(log(1 + k) − δ²/2, δ²)`, the jump rate `Λ/T` and the compensated drift
(`jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice`). The spot-side statement is
`mertonCallPrice_strictConvexOn_spot`. -/
theorem mertonCallPrice_strictConvexOn_strike {S r σ T k δ : ℝ} (hS : 0 < S) (hσ : 0 < σ)
    (hT : 0 < T) (hk : -1 < k) (Λ : ℝ≥0) :
    StrictConvexOn ℝ (Ioi 0) fun K ↦ mertonCallPrice S K r σ T k δ Λ := by
  lift T to ℝ≥0 using hT.le
  replace hT : 0 < T := NNReal.coe_pos.1 hT
  refine (strictConvexOn_jumpDiffusionCallPrice_strike (r := r)
    (b := r - σ ^ 2 / 2 - (Λ / T : ℝ≥0) * k) hS hσ.ne'
    (integrable_exp_jumpDiffusionIncrementLaw _ σ (Λ / T)
      (integrable_exp_gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) T) hT).congr
    fun K hK ↦ ?_
  dsimp only
  rw [jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice hS (mem_Ioi.1 hK) hσ hk rfl hT,
    div_mul_cancel₀ Λ hT.ne']

end MathFin
