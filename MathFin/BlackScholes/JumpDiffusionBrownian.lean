/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.JumpDiffusionOptionPrices
public import MathFin.BlackScholes.GaussianSmoothing
public import MathFin.BlackScholes.Put
public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianModel

/-!
# Brownian motion with drift is a jump-diffusion without jumps

With jump rate `0` the Poisson count vanishes (`poissonMeasure_zero`), so the jump-diffusion
log-return over `τ` is Gaussian, `N(bτ, σ²τ)` (`jumpDiffusionIncrementLaw_zero`). For a filtered
pre-Brownian motion `B` (`IsFilteredPreBrownian B 𝓕 P`) the log-price `X_t = bt + σB_t` is
therefore a `JumpDiffusionProcess` with rate `0`, for any jump law
(`IsFilteredPreBrownian.jumpDiffusionProcess`). The Brownian motion constructed on path space
(`brownian_filtered`) makes the structure satisfiable without jumps
(`jumpDiffusionProcess_brownian`).

The process-level jump-diffusion results then specialize to the Black–Scholes model driven by a
Brownian motion:

* `IsFilteredPreBrownian.martingale_discounted_iff`: the discounted price `e^{−rt}S₀e^{bt + σB_t}`
  (`S₀ ≠ 0`) is a martingale if and only if `b = r − σ²/2`. The "if" direction is also
  `discountedGBM_isMartingale` (`Foundations/ContinuousFTAP.lean`), proved there from the Wald
  martingale; the converse says no other drift gives a martingale.
* `IsFilteredPreBrownian.condExp_call_eq_bsV` and `IsFilteredPreBrownian.condExp_put_eq_bsPut`, the
  **Black–Scholes formulas at every date**: at `b = r − σ²/2` and `t < T`, the conditional values
  of the call and the put given `𝓕_t` are the Black–Scholes prices at the current price `S_t` and
  the remaining maturity `T − t`. With no jumps the price functions are the Black–Scholes formulas
  (`jumpDiffusionCallPrice_zero`, `jumpDiffusionPutPrice_zero`).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- The Poisson law of rate `0` is the point mass at `0`. -/
lemma poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  refine Measure.ext_iff_singleton.2 fun n ↦ ?_
  rw [poissonMeasure_singleton, Measure.dirac_apply]
  rcases n with _ | n
  · rw [Set.indicator_of_mem (Set.mem_singleton 0), Pi.one_apply]
    simp
  · rw [Set.indicator_of_notMem (Set.mem_singleton_iff.not.2 (Nat.succ_ne_zero n).symm)]
    simp

/-- **With no jumps the log-return is Gaussian**: at rate `0` the log-return over `τ` has law
`N(bτ, σ²τ)`, whatever the jump law. -/
lemma jumpDiffusionIncrementLaw_zero (b σ : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (τ : ℝ≥0) :
    jumpDiffusionIncrementLaw b σ 0 ν τ
      = gaussianReal (b * τ) (.mk (σ ^ 2) (sq_nonneg _) * τ) := by
  rw [jumpDiffusionIncrementLaw, zero_mul]
  obtain ⟨h, -⟩ := jumpDiffusionHyp_canonical 0 ν
  -- with rate `0` the jump count vanishes almost surely
  have hN : (fun ω : ℝ × ℕ × (ℕ → ℝ) ↦ ω.2.1) =ᵐ[jumpDiffusionMeasure 0 ν] fun _ ↦ 0 := by
    have hlaw := h.N_law
    rw [poissonMeasure_zero] at hlaw
    exact hlaw.ae_eq_of_dirac
  have hX : jumpDiffusionLogReturn b σ τ
      =ᵐ[jumpDiffusionMeasure 0 ν] fun ω ↦ b * τ + σ * Real.sqrt τ * ω.1 :=
    Filter.Eventually.mono hN fun ω (hω : ω.2.1 = 0) ↦ by
      simp only [jumpDiffusionLogReturn, hω, Finset.range_zero, Finset.sum_empty, add_zero]
  rw [Measure.map_congr hX,
    (gaussianReal_const_add (gaussianReal_const_mul h.Z_law (σ * Real.sqrt τ)) (b * τ)).map_eq]
  congr 1
  · ring
  · ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one]
    rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg τ)]

/-- With no jumps and the risk-neutral drift `r − σ²/2`, the log-return over `τ > 0`, standardized,
is standard normal. -/
lemma hasLaw_std_jumpDiffusionIncrementLaw_zero {r σ : ℝ} (hσ : 0 < σ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    HasLaw (fun y ↦ (id y - (r - σ ^ 2 / 2) * τ) / (σ * Real.sqrt τ)) (gaussianReal 0 1)
      (jumpDiffusionIncrementLaw (r - σ ^ 2 / 2) σ 0 ν τ) := by
  have hlaw : HasLaw id (gaussianReal ((r - σ ^ 2 / 2) * τ) (.mk (σ ^ 2) (sq_nonneg _) * τ))
      (jumpDiffusionIncrementLaw (r - σ ^ 2 / 2) σ 0 ν τ) := by
    rw [jumpDiffusionIncrementLaw_zero]
    exact HasLaw.id
  refine hasLaw_sub_div_of_gaussianReal hlaw (mul_pos hσ (Real.sqrt_pos.2 (NNReal.coe_pos.2 hτ))) ?_
  simp only [NNReal.coe_mul, NNReal.coe_mk]
  rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg τ)]

/-- **With no jumps the call price function is the Black–Scholes formula**: at rate `0` and the
drift `r − σ²/2`, `C(S, τ) = C_BS(S, τ)` for `S, K, σ, τ > 0`. The standardized log-return is
standard normal (`hasLaw_std_jumpDiffusionIncrementLaw_zero`), and it drives the Black–Scholes
terminal price. -/
theorem jumpDiffusionCallPrice_zero {S K r σ : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionCallPrice S K r (r - σ ^ 2 / 2) σ 0 ν τ = bsV K r σ S τ := by
  rw [jumpDiffusionCallPrice, ← integral_bsCall_payoff_eq_bsV (r := r)
    ⟨hS, hK, hσ, NNReal.coe_pos.2 hτ,
      hasLaw_std_jumpDiffusionIncrementLaw_zero (r := r) hσ ν hτ⟩]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  have hw : σ * Real.sqrt τ * ((id y - (r - σ ^ 2 / 2) * τ) / (σ * Real.sqrt τ))
      = y - (r - σ ^ 2 / 2) * τ :=
    mul_div_cancel₀ _ (mul_pos hσ (Real.sqrt_pos.2 (NNReal.coe_pos.2 hτ))).ne'
  show rexp (-r * τ) * max (S * rexp y - K) 0
    = rexp (-r * τ) * max (bsTerminal S r σ τ
      ((id y - (r - σ ^ 2 / 2) * τ) / (σ * Real.sqrt τ)) - K) 0
  rw [bsTerminal, hw, show (r - σ ^ 2 / 2) * (τ : ℝ) + (y - (r - σ ^ 2 / 2) * τ) = y by ring]

/-- **With no jumps the put price function is the Black–Scholes put formula**: at rate `0` and the
drift `r − σ²/2`, `P(S, τ) = Ke^{−rτ}Φ(−d₂) − SΦ(−d₁)` for `S, K, σ, τ > 0`. -/
theorem jumpDiffusionPutPrice_zero {S K r σ : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionPutPrice S K r (r - σ ^ 2 / 2) σ 0 ν τ
      = K * rexp (-r * τ) * Phi (-(bsd2 S K r σ τ)) - S * Phi (-(bsd1 S K r σ τ)) := by
  rw [jumpDiffusionPutPrice, ← bs_put_formula (r := r)
    ⟨hS, hK, hσ, NNReal.coe_pos.2 hτ,
      hasLaw_std_jumpDiffusionIncrementLaw_zero (r := r) hσ ν hτ⟩]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  have hw : σ * Real.sqrt τ * ((id y - (r - σ ^ 2 / 2) * τ) / (σ * Real.sqrt τ))
      = y - (r - σ ^ 2 / 2) * τ :=
    mul_div_cancel₀ _ (mul_pos hσ (Real.sqrt_pos.2 (NNReal.coe_pos.2 hτ))).ne'
  show rexp (-r * τ) * max (K - S * rexp y) 0
    = rexp (-r * τ) * max (K - bsTerminal S r σ τ
      ((id y - (r - σ ^ 2 / 2) * τ) / (σ * Real.sqrt τ))) 0
  rw [bsTerminal, hw, show (r - σ ^ 2 / 2) * (τ : ℝ) + (y - (r - σ ^ 2 / 2) * τ) = y by ring]

end MathFin

namespace ProbabilityTheory.IsFilteredPreBrownian

open MeasureTheory MathFin Real
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ} [hB : IsFilteredPreBrownian B 𝓕 P]

/-- **Brownian motion with drift is a jump-diffusion without jumps.** For a filtered pre-Brownian
motion `B`, the log-price `X_t = bt + σB_t` is a `JumpDiffusionProcess` with rate `0`, for any
jump law: it is adapted, starts at `0`, and its increment `b(t − s) + σ(B_t − B_s)` is
independent of `𝓕_s` with law `N(b(t − s), σ²(t − s))` (`jumpDiffusionIncrementLaw_zero`). -/
theorem jumpDiffusionProcess (b σ : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    JumpDiffusionProcess P 𝓕 (fun t ω ↦ b * t + σ * B t ω) b σ 0 ν where
  adapted t :=
    (((hB.stronglyAdapted t).measurable.const_mul σ).const_add (b * t)).stronglyMeasurable
  zero := by
    have h0 := hB.hasLaw_eval 0
    rw [gaussianReal_zero_var] at h0
    filter_upwards [h0.ae_eq_of_dirac] with ω (hω : B 0 ω = 0)
    simp [hω]
  indep s t hst := by
    -- the increment of `X` is an affine function of the Brownian increment
    refine indep_of_indep_of_le_left (hB.indep s t hst)
      (MeasurableSpace.comap_le_comap_of_eq_comp (fun y ↦ b * ((t : ℝ) - s) + σ * y)
        (by fun_prop : Measurable fun y : ℝ ↦ b * ((t : ℝ) - s) + σ * y) ?_)
    funext ω
    simp only [Function.comp_apply]
    ring
  law s t hst := by
    rw [jumpDiffusionIncrementLaw_zero]
    have h := gaussianReal_const_add
      (gaussianReal_const_mul (MathFin.hasLaw_increment hB.toIsPreBrownianReal hst) σ)
      (b * ((t - s : ℝ≥0) : ℝ))
    rw [mul_zero, zero_add] at h
    refine h.congr (ae_of_all _ fun ω ↦ ?_)
    show (b * (t : ℝ) + σ * B t ω) - (b * s + σ * B s ω)
      = b * ((t - s : ℝ≥0) : ℝ) + σ * (B t ω - B s ω)
    rw [NNReal.coe_sub hst]
    ring

/-- **The risk-neutral drift is the only martingale drift.** For a filtered pre-Brownian motion
`B` and `S₀ ≠ 0`, the discounted price `e^{−rt}S₀e^{bt + σB_t}` is an `𝓕`-martingale if and only
if `b = r − σ²/2`: `JumpDiffusionProcess.martingale_iff` at rate `0`. The "if" direction is also
`discountedGBM_isMartingale` (`Foundations/ContinuousFTAP.lean`). -/
theorem martingale_discounted_iff (b σ : ℝ) {S_0 : ℝ} (hS_0 : S_0 ≠ 0) (r : ℝ) :
    Martingale (fun (t : ℝ≥0) ω ↦ rexp (-r * t) * (S_0 * rexp (b * t + σ * B t ω))) 𝓕 P ↔
      b = r - σ ^ 2 / 2 := by
  rw [(hB.jumpDiffusionProcess b σ (gaussianReal 0 1)).martingale_iff
    (integrable_exp_gaussianReal 0 1) hS_0 r, NNReal.coe_zero, zero_mul, sub_zero]

/-- **The Black–Scholes call formula at every date.** For a filtered pre-Brownian motion `B`, the
price `S_t = S₀e^{(r − σ²/2)t + σB_t}` with `S₀, K, σ > 0`, and dates `t < T`, the conditional
value of the call given `𝓕_t` is the Black–Scholes price at the current price and the remaining
maturity: `𝔼[e^{−r(T−t)}(S_T − K)⁺ | 𝓕_t] = C_BS(S_t, T − t)` almost surely
(`JumpDiffusionProcess.condExp_call`, `jumpDiffusionCallPrice_zero`). -/
theorem condExp_call_eq_bsV {r σ S_0 K : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ)
    {t T : ℝ≥0} (htT : t < T) :
    P[fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * B T ω) - K) 0
        | 𝓕 t]
      =ᵐ[P] fun ω ↦ bsV K r σ (S_0 * rexp ((r - σ ^ 2 / 2) * t + σ * B t ω)) (T - t : ℝ≥0) :=
  ((hB.jumpDiffusionProcess (r - σ ^ 2 / 2) σ (gaussianReal 0 1)).condExp_call
    (integrable_exp_gaussianReal 0 1) S_0 K r htT.le).trans <|
      ae_of_all _ fun _ ↦ jumpDiffusionCallPrice_zero (mul_pos hS_0 (Real.exp_pos _)) hK hσ _
        (tsub_pos_of_lt htT)

/-- **The Black–Scholes put formula at every date.** Under the hypotheses of
`condExp_call_eq_bsV`, the conditional value of the put given `𝓕_t` is
`Ke^{−r(T−t)}Φ(−d₂) − S_tΦ(−d₁)` at the current price `S_t` and the remaining maturity `T − t`
(`JumpDiffusionProcess.condExp_put`, `jumpDiffusionPutPrice_zero`). -/
theorem condExp_put_eq_bsPut {r σ S_0 K : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ)
    {t T : ℝ≥0} (htT : t < T) :
    P[fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * max (K - S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * B T ω)) 0
        | 𝓕 t]
      =ᵐ[P] fun ω ↦ K * rexp (-r * (T - t : ℝ≥0))
          * Phi (-(bsd2 (S_0 * rexp ((r - σ ^ 2 / 2) * t + σ * B t ω)) K r σ (T - t : ℝ≥0)))
        - S_0 * rexp ((r - σ ^ 2 / 2) * t + σ * B t ω)
          * Phi (-(bsd1 (S_0 * rexp ((r - σ ^ 2 / 2) * t + σ * B t ω)) K r σ (T - t : ℝ≥0))) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact ((hB.jumpDiffusionProcess (r - σ ^ 2 / 2) σ (gaussianReal 0 1)).condExp_put
    hS_0.le K r htT.le).trans <|
      ae_of_all _ fun _ ↦ jumpDiffusionPutPrice_zero (mul_pos hS_0 (Real.exp_pos _)) hK hσ _
        (tsub_pos_of_lt htT)

end ProbabilityTheory.IsFilteredPreBrownian

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- **A jump-diffusion process without jumps exists.** On the path space of the constructed
Brownian motion (`brownian_filtered`, with its natural filtration and Gaussian measure), the
log-price `bt + σB_t` is a `JumpDiffusionProcess` with rate `0`, for any jump law. -/
theorem jumpDiffusionProcess_brownian (b σ : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    JumpDiffusionProcess gaussianLimit BlackScholes.AmericanPut.Stopping.brownianFiltration
      (fun t ω ↦ b * t + σ * brownian t ω) b σ 0 ν :=
  have := BlackScholes.AmericanPut.Stopping.brownian_filtered
  IsFilteredPreBrownian.jumpDiffusionProcess b σ ν

end MathFin
