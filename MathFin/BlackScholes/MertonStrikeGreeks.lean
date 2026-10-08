/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.MertonGreeks
public import MathFin.BlackScholes.BreedenLitzenberger

/-!
# Merton's digital and Merton's density: the strike derivatives of Merton's series

Merton's call price is a Poisson mixture of Black–Scholes prices,
`C(K) = ∑ₙ wₙ C_BS(S·cₙ, K, σₙ)` (`mertonCallPrice`; the weights `wₙ`, the jump factors `cₙ` and
the volatilities `σₙ` are those of `MertonGreeks.lean`). As in the spot, the series can be
differentiated term by term in the strike, and its strike derivatives are the Poisson mixtures of
the Black–Scholes ones.

* `hasDerivAt_mertonCallPrice_strike`: `∂C/∂K = −mertonDigitalPrice`, where
  `mertonDigitalPrice = ∑ₙ wₙ e^{−rT}Φ(d₂ⁿ)` mixes the Black–Scholes cash-or-nothing prices
  (`hasDerivAt_bsV_K`). Each term's derivative is at most `wₙe^{−rT}`, and the weights sum to
  one.
* `hasDerivAt_mertonDigitalPrice_strike`: `∂D/∂K = −e^{−rT}·mertonDensity`, where
  `mertonDensity = ∑ₙ wₙ·lognormalTerminalPDF(S·cₙ, r, σₙ, T, K)` mixes the lognormal densities
  (`breedenLitzenberger`, term by term). On `(K/2, ∞)` each term's derivative is at most
  `wₙe^{−rT}/((K/2)σ√T)`, since `ϕ ≤ 1` and `σₙ ≥ σ`.
* `hasDerivAt_deriv_mertonCallPrice_strike`: Merton's Breeden–Litzenberger formula,
  `∂²C/∂K² = e^{−rT}·mertonDensity`.

That the two series are the digital price and the density of the price of the jump-diffusion with
Gaussian log-jumps is `BlackScholes/JumpDiffusionDigital.lean`.
-/

@[expose] public section

namespace MathFin

open Real Set Filter ProbabilityTheory
open scoped NNReal Nat

variable {K r σ T k δ : ℝ} {Λ : ℝ≥0}

/-- **Merton's digital price**: `∑ₙ wₙ e^{−rT}Φ(d₂ⁿ)`, the Poisson mixture of the Black–Scholes
cash-or-nothing prices at the conditional spots `S·cₙ` and volatilities `σₙ`. -/
noncomputable def mertonDigitalPrice (S K r σ T k δ : ℝ) (Λ : ℝ≥0) : ℝ :=
  ∑' n : ℕ, rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
    (rexp (-r * T) * Phi (bsd2 (mertonSpot S k Λ n) K r (mertonVol σ δ T n) T))

/-- **Merton's density** of the price at the strike `K`:
`∑ₙ wₙ·lognormalTerminalPDF(S·cₙ, r, σₙ, T, K)`, the Poisson mixture of the lognormal densities
at the conditional spots and volatilities. -/
noncomputable def mertonDensity (S K r σ T k δ : ℝ) (Λ : ℝ≥0) : ℝ :=
  ∑' n : ℕ, rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
    lognormalTerminalPDF (mertonSpot S k Λ n) r (mertonVol σ δ T n) T K

/-- The digital series converges: its terms lie in `[0, wₙe^{−rT}]`. -/
lemma summable_mertonDigitalPrice_terms (S K : ℝ) :
    Summable fun n : ℕ ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
      (rexp (-r * T) * Phi (bsd2 (mertonSpot S k Λ n) K r (mertonVol σ δ T n) T)) :=
  Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (by positivity) (mul_nonneg (Real.exp_pos _).le (Phi_nonneg _)))
    (fun n ↦ mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (Real.exp_pos _).le (Phi_le_one _)) (by positivity))
    ((hasSum_one_poissonMeasure Λ).summable.mul_right _)

/-- **The strike derivative of Merton's call price is minus Merton's digital price**:
`∂C/∂K = −∑ₙ wₙ e^{−rT}Φ(d₂ⁿ)`. The series of Black–Scholes prices is differentiated term by
term (`hasDerivAt_bsV_K`), each term's derivative being at most `wₙe^{−rT}` in absolute value. -/
theorem hasDerivAt_mertonCallPrice_strike {S : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hT : 0 < T)
    (hk : -1 < k) (hK : 0 < K) :
    HasDerivAt (fun x ↦ mertonCallPrice S x r σ T k δ Λ)
      (-mertonDigitalPrice S K r σ T k δ Λ) K := by
  have hw (n : ℕ) : 0 ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! := by positivity
  have hterm (n : ℕ) (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonCallTerm S y r σ T k δ Λ n)
        (-(rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (rexp (-r * T) * Phi (bsd2 (mertonSpot S k Λ n) x r (mertonVol σ δ T n) T)))) x := by
    have hfun : (fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * mertonCallTerm S y r σ T k δ Λ n)
        = fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n !
          * bsV y r (mertonVol σ δ T n) (mertonSpot S k Λ n) T := by
      funext y
      rw [mertonCallTerm_eq_bsV]
    rw [hfun]
    exact ((hasDerivAt_bsV_K (r := r) (mertonSpot_pos hS hk Λ n)
      (mertonVol_pos (δ := δ) hσ hT n) (show 0 < x from hx) hT).const_mul _).congr_deriv
      (by rw [neg_mul]; ring)
  have hbound (n : ℕ) (x : ℝ) (_ : x ∈ Ioi (0 : ℝ)) :
      ‖-(rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (rexp (-r * T) * Phi (bsd2 (mertonSpot S k Λ n) x r (mertonVol σ δ T n) T)))‖
        ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * rexp (-r * T) := by
    rw [norm_neg, Real.norm_of_nonneg
      (mul_nonneg (hw n) (mul_nonneg (Real.exp_pos _).le (Phi_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (Real.exp_pos _).le (Phi_le_one _))
      (hw n)
  exact ((hasDerivAt_tsum_of_isPreconnected ((hasSum_one_poissonMeasure Λ).summable.mul_right _)
    isOpen_Ioi isPreconnected_Ioi hterm hbound hK
    (summable_weights_mul_mertonCallTerm hS hK hσ hT hk) hK).congr_of_eventuallyEq
    (Eventually.of_forall fun x ↦ mertonCallPrice_eq_tsum S x r σ T k δ Λ)).congr_deriv
    (by rw [tsum_neg, mertonDigitalPrice])

/-- **The strike derivative of Merton's digital price is minus the discounted Merton density**:
`∂D/∂K = −e^{−rT}·∑ₙ wₙ·lognormalTerminalPDF(S·cₙ, r, σₙ, T, K)`. Each term is a Black–Scholes
digital, minus the strike derivative of a Black–Scholes price, so its derivative is the
Black–Scholes Breeden–Litzenberger formula (`breedenLitzenberger`). On `(K/2, ∞)` each term's
derivative is at most `wₙe^{−rT}/((K/2)σ√T)`, since `ϕ ≤ 1` and `σₙ ≥ σ`. -/
theorem hasDerivAt_mertonDigitalPrice_strike {S : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hT : 0 < T)
    (hk : -1 < k) (hK : 0 < K) :
    HasDerivAt (fun x ↦ mertonDigitalPrice S x r σ T k δ Λ)
      (-(rexp (-r * T) * mertonDensity S K r σ T k δ Λ)) K := by
  have hw (n : ℕ) : 0 ≤ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! := by positivity
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hK2 : 0 < K / 2 := half_pos hK
  have hterm (n : ℕ) (x : ℝ) (hx : x ∈ Ioi (K / 2)) :
      HasDerivAt (fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (rexp (-r * T) * Phi (bsd2 (mertonSpot S k Λ n) y r (mertonVol σ δ T n) T)))
        (-(rexp (-r * T) * (rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          lognormalTerminalPDF (mertonSpot S k Λ n) r (mertonVol σ δ T n) T x))) x := by
    have hx0 : 0 < x := hK2.trans hx
    have hSn := mertonSpot_pos hS hk Λ n
    have hvn := mertonVol_pos (δ := δ) hσ hT n
    -- near `x` the Black–Scholes digital is minus the strike derivative of the Black–Scholes
    -- price, whose derivative is `breedenLitzenberger`
    have hBL : HasDerivAt
        (fun y ↦ -(rexp (-(r * T)) * Phi (bsd2 (mertonSpot S k Λ n) y r (mertonVol σ δ T n) T)))
        (rexp (-(r * T)) * lognormalTerminalPDF (mertonSpot S k Λ n) r (mertonVol σ δ T n) T x)
        x :=
      (breedenLitzenberger (r := r) hSn hvn hx0 hT).congr_of_eventuallyEq
        (eventually_of_mem (Ioi_mem_nhds hx0) fun y hy ↦
          (hasDerivAt_bsV_K (r := r) hSn hvn hy hT).deriv.symm)
    have hfun : (fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          (rexp (-r * T) * Phi (bsd2 (mertonSpot S k Λ n) y r (mertonVol σ δ T n) T)))
        = fun y ↦ rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          -(-(rexp (-(r * T)) * Phi (bsd2 (mertonSpot S k Λ n) y r (mertonVol σ δ T n) T))) := by
      funext y
      rw [neg_neg, neg_mul]
    rw [hfun]
    exact (hBL.neg.const_mul _).congr_deriv (by rw [neg_mul]; ring)
  have hbound (n : ℕ) (x : ℝ) (hx : x ∈ Ioi (K / 2)) :
      ‖-(rexp (-r * T) * (rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! *
          lognormalTerminalPDF (mertonSpot S k Λ n) r (mertonVol σ δ T n) T x))‖
        ≤ rexp (-r * T) * (rexp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / n ! * (K / 2 * σ * Real.sqrt T)⁻¹) := by
    have hx' : K / 2 < x := hx
    have hx0 : 0 < x := hK2.trans hx'
    have hden : K / 2 * σ * Real.sqrt T ≤ x * mertonVol σ δ T n * Real.sqrt T :=
      mul_le_mul_of_nonneg_right (mul_le_mul hx'.le (le_mertonVol δ hσ.le hT n) hσ.le hx0.le)
        hsT.le
    have hL0 := lognormalTerminalPDF_nonneg (S_0 := mertonSpot S k Λ n) (r := r) hx0
      (mertonVol_pos (δ := δ) hσ hT n) hT
    have hL : lognormalTerminalPDF (mertonSpot S k Λ n) r (mertonVol σ δ T n) T x
        ≤ (K / 2 * σ * Real.sqrt T)⁻¹ := by
      rw [lognormalTerminalPDF, ← one_div]
      exact div_le_div₀ zero_le_one (gaussianPDFReal_zero_one_le_one _)
        (mul_pos (mul_pos hK2 hσ) hsT) hden
    rw [norm_neg, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (hw n) hL0))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL (hw n)) (Real.exp_pos _).le
  exact (hasDerivAt_tsum_of_isPreconnected
    (((hasSum_one_poissonMeasure Λ).summable.mul_right _).mul_left _) isOpen_Ioi
    isPreconnected_Ioi hterm hbound (half_lt_self hK) (summable_mertonDigitalPrice_terms S K)
    (half_lt_self hK)).congr_deriv (by rw [tsum_neg, tsum_mul_left, mertonDensity])

/-- **Merton's Breeden–Litzenberger formula**: `∂²C/∂K² = e^{−rT}·mertonDensity`, the discounted
Poisson mixture of lognormal densities. The strike derivative of the call price is minus Merton's
digital price on all of `K > 0` (`hasDerivAt_mertonCallPrice_strike`), and the digital's strike
derivative is minus the discounted density (`hasDerivAt_mertonDigitalPrice_strike`). -/
theorem hasDerivAt_deriv_mertonCallPrice_strike {S : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hT : 0 < T)
    (hk : -1 < k) (hK : 0 < K) :
    HasDerivAt (deriv fun x ↦ mertonCallPrice S x r σ T k δ Λ)
      (rexp (-r * T) * mertonDensity S K r σ T k δ Λ) K :=
  hasDerivAt_deriv_of_eventually
    ((eventually_gt_nhds hK).mono fun _ hx ↦ hasDerivAt_mertonCallPrice_strike hS hσ hT hk hx)
    ((hasDerivAt_mertonDigitalPrice_strike (r := r) (δ := δ) (Λ := Λ) hS hσ hT hk hK).neg
      |>.congr_deriv (neg_neg _))

end MathFin
