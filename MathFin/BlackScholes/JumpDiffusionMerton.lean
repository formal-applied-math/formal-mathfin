/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.GaussianSmoothing
public import MathFin.BlackScholes.JumpDiffusionOptionPrices

/-!
# Merton's formula from the general jump-diffusion

Merton (1976) priced the call of a jump-diffusion with lognormal jumps as a Poisson series of
Black–Scholes prices (`mertonCallPrice`): given `n` jumps the log-return is Gaussian, so the call
is the Black–Scholes call at the jump-adjusted spot `S₀e^{−kΛ}(1 + k)ⁿ` and the volatility
`√(σ² + nδ²/T)`. `MertonModel` proves this under its own hypotheses (`merton_call_formula`). Here
it is derived from the general jump-diffusion instead. With log-jumps `N(log(1 + k) − δ²/2, δ²)`,
whose multipliers `e^{Jᵢ}` have mean `1 + k`, Merton's formula for a general jump law
(`JumpDiffusionHyp.call_poisson_mixture`) averages the Black–Scholes price over the sum of `n`
log-jumps, which is `N(n(log(1 + k) − δ²/2), nδ²)`. Gaussian smoothing
(`integral_bsV_mul_exp_gaussianReal_of_sq`) turns each average into the `n`-th term of the
series.

The same computation prices the call in the price process. At the compensated drift the call
price function is the call of the canonical model (`jumpDiffusionCallPrice_eq_canonical`). With
Gaussian jumps it is therefore Merton's series, and the conditional value of the call at every
date is Merton's 1976 formula at the current price and the remaining maturity.

## Main results

* `JumpDiffusionHyp.call_eq_mertonCallPrice`: with Gaussian log-jumps and the compensator `kΛ`,
  the call is `mertonCallPrice`.
* `jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice`: with Gaussian jumps and the compensated
  drift `b = r − σ²/2 − Λk`, the call price function over `τ` is `mertonCallPrice` at the expected
  jump count `Λτ`.
* `JumpDiffusionProcess.condExp_call_eq_mertonCallPrice`: for `t < T`, the conditional value of
  the call given `𝓕_t` is `mertonCallPrice` at `S_t`, `T − t` and `Λ(T − t)`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace JumpDiffusionHyp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {Λ : ℝ≥0} {Z : Ω → ℝ}
  {N : Ω → ℕ} {J : ℕ → Ω → ℝ}

/-- **Merton's formula from the general jump-diffusion.** With log-jumps
`Jᵢ ∼ N(log(1 + k) − δ²/2, δ²)` and the compensator `κ = kΛ`, the call is Merton's series
`mertonCallPrice`. With `n` jumps the jump part is `N(n(log(1 + k) − δ²/2), nδ²)`, and Gaussian
smoothing of the Black–Scholes price gives the `n`-th term
(`integral_bsV_mul_exp_gaussianReal_of_sq`). -/
theorem call_eq_mertonCallPrice (h : JumpDiffusionHyp Q Λ Z N J) {k δ : ℝ} (hk : -1 < k)
    (hJ : ∀ i, HasLaw (J i) (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) Q)
    {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, rexp (-r * T) * max (jumpDiffusionTerminal S_0 r σ T (k * Λ) (Z ω) (N ω)
        (fun i ↦ J i ω) - K) 0 ∂Q
      = mertonCallPrice S_0 K r σ T k δ Λ := by
  have hJexp : Integrable (fun ω ↦ rexp (J 0 ω)) Q := by
    simpa only [one_mul] using integrable_exp_mul_of_hasLaw (hJ 0) 1
  have h1k : (0 : ℝ) < 1 + k := by linarith
  rw [h.call_poisson_mixture hJexp hS_0 hK hσ hT (k * Λ), mertonCallPrice]
  refine integral_congr_ae (ae_of_all _ fun n ↦ ?_)
  -- with `n` jumps the jump part is Gaussian
  have hsum : HasLaw (fun ω ↦ ∑ i ∈ Finset.range n, J i ω)
      (gaussianReal (n * (Real.log (1 + k) - δ ^ 2 / 2)) (n * (δ ^ 2).toNNReal)) Q :=
    (hasLaw_sum_range_gaussianReal hJ h.J_indep n).congr
      (ae_of_all _ fun ω ↦ (Finset.sum_apply ω _ _).symm)
  have hvar : mertonVol σ δ T n ^ 2 * T = σ ^ 2 * T + ((n * (δ ^ 2).toNNReal : ℝ≥0) : ℝ) := by
    rw [mertonVol_sq_mul σ δ hT n, NNReal.coe_mul, NNReal.coe_natCast,
      Real.coe_toNNReal _ (sq_nonneg δ)]
  have hbs : Measurable fun x ↦ bsV K r σ (S_0 * rexp (-(k * Λ)) * rexp x) T :=
    (measurable_bsV_spot K r σ T).comp (by fun_prop)
  calc ∫ ω, bsV K r σ (S_0 * rexp (-(k * Λ) + ∑ i ∈ Finset.range n, J i ω)) T ∂Q
      = ∫ ω, bsV K r σ (S_0 * rexp (-(k * Λ)) * rexp (∑ i ∈ Finset.range n, J i ω)) T ∂Q := by
        simp only [Real.exp_add, mul_assoc]
    _ = ∫ x, bsV K r σ (S_0 * rexp (-(k * Λ)) * rexp x) T
          ∂(gaussianReal (n * (Real.log (1 + k) - δ ^ 2 / 2)) (n * (δ ^ 2).toNNReal)) :=
        hsum.integral_comp hbs.aestronglyMeasurable
    _ = bsV K r (mertonVol σ δ T n) (S_0 * rexp (-(k * Λ))
          * rexp (n * (Real.log (1 + k) - δ ^ 2 / 2) + ((n * (δ ^ 2).toNNReal : ℝ≥0) : ℝ) / 2))
          T :=
        integral_bsV_mul_exp_gaussianReal_of_sq (mul_pos hS_0 (Real.exp_pos _)) hK hσ
          (mertonVol_pos hσ hT n) hT _ hvar
    _ = mertonCallTerm S_0 K r σ T k δ Λ n := by
        rw [mertonCallTerm_eq_bsV, mertonSpot, NNReal.coe_mul, NNReal.coe_natCast,
          Real.coe_toNNReal _ (sq_nonneg δ),
          show (n : ℝ) * (Real.log (1 + k) - δ ^ 2 / 2) + n * δ ^ 2 / 2 = n * Real.log (1 + k)
            by ring,
          Real.exp_nat_mul, Real.exp_log h1k]

end JumpDiffusionHyp

/-- **Merton's 1976 formula for the call price function.** With log-jumps
`N(log(1 + k) − δ²/2, δ²)` and the compensated drift `b = r − σ²/2 − Λk`, the call price
function over a time `τ > 0` is Merton's series `mertonCallPrice` at the expected jump count
`Λτ`: the price function is the call of the canonical model at intensity `Λτ`
(`jumpDiffusionCallPrice_eq_canonical`), with `𝔼[e^J] = 1 + k`
(`integral_exp_gaussianReal`). -/
theorem jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice {S K r b σ k δ : ℝ} (hS : 0 < S)
    (hK : 0 < K) (hσ : 0 < σ) (hk : -1 < k) {Λ : ℝ≥0} (hb : b = r - σ ^ 2 / 2 - Λ * k)
    {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionCallPrice S K r b σ Λ
        (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) τ
      = mertonCallPrice S K r σ τ k δ (Λ * τ) := by
  have hM : ∫ x, rexp x ∂(gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal)
      = 1 + k := by
    rw [integral_exp_gaussianReal, Real.coe_toNNReal _ (sq_nonneg δ), sub_add_cancel,
      Real.exp_log (show (0 : ℝ) < 1 + k by linarith)]
  have hb' : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x
      ∂(gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) - 1) := by
    rw [hM, hb]
    ring
  obtain ⟨h, hJ⟩ := jumpDiffusionHyp_canonical (Λ * τ)
    (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal)
  rw [jumpDiffusionCallPrice_eq_canonical S K hb' τ, hM,
    show (Λ : ℝ) * τ * (1 + k - 1) = k * (Λ * τ : ℝ≥0) by push_cast; ring]
  exact h.call_eq_mertonCallPrice hk hJ hS hK hσ (NNReal.coe_pos.2 hτ)

namespace JumpDiffusionProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b σ : ℝ} {Λ : ℝ≥0}

/-- **Merton's 1976 formula at every date.** In a jump-diffusion with log-jumps
`N(log(1 + k) − δ²/2, δ²)` at the compensated drift `b = r − σ²/2 − Λk`, for `t < T` the
conditional value of the call given `𝓕_t` is Merton's series `mertonCallPrice` at the current
price `S_t = S₀e^{X_t}`, the remaining maturity `T − t` and the expected number of jumps
`Λ(T − t)` (`condExp_call`, `jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice`). -/
theorem condExp_call_eq_mertonCallPrice {k δ : ℝ}
    (h : JumpDiffusionProcess P 𝓕 X b σ Λ
      (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal))
    [IsProbabilityMeasure P] (hk : -1 < k) {r : ℝ} (hb : b = r - σ ^ 2 / 2 - Λ * k)
    {S_0 K : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) {t T : ℝ≥0} (htT : t < T) :
    P[fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * max (S_0 * rexp (X T ω) - K) 0 | 𝓕 t]
      =ᵐ[P] fun ω ↦ mertonCallPrice (S_0 * rexp (X t ω)) K r σ (T - t : ℝ≥0) k δ
        (Λ * (T - t)) :=
  (h.condExp_call (integrable_exp_gaussianReal _ _) hS_0.le hK.le r htT.le).trans <|
    ae_of_all _ fun _ ↦ jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice
      (mul_pos hS_0 (Real.exp_pos _)) hK hσ hk hb (tsub_pos_of_lt htT)

end JumpDiffusionProcess

end MathFin
