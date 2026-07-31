/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.PDE

/-!
# Higher-order Black–Scholes Greeks: vanna and volga

For the European call price `V(S, σ, τ) = S Φ(d₁) − K e^{-rτ} Φ(d₂)`, we
derive the two most-used second-order Greeks:

* **Vanna**: `∂²V/∂σ∂S = ∂(vega)/∂S = -ϕ(d₁) · d₂ / σ`.
* **Volga (aka vomma)**: `∂²V/∂σ² = ∂(vega)/∂σ = vega · d₁ · d₂ / σ`.

The key algebraic shortcut is `∂_σ d₁ = -d₂/σ` (from
`hasDerivAt_bsd1_sigma_clean` below), which compresses an otherwise messy
quotient-rule expression. Combined with `ϕ'(z) = -z · ϕ(z)`, both Greeks
follow from one chain rule + one product/scalar rule.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- Clean form: `∂_σ d₁ = -d₂/σ`. Algebraic shortcut for the quotient-rule
expression in `hasDerivAt_bsd1_sigma`. Useful for higher-order Greeks. -/
private lemma hasDerivAt_bsd1_sigma_clean (S K r : ℝ) {σ τ : ℝ}
    (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsd1 S K r s τ) (-(bsd2 S K r σ τ) / σ) σ := by
  have h := hasDerivAt_bsd1_sigma S K r hσ hτ
  convert h using 1
  try rfl
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have h_sqrt_sq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  rw [bsd2, bsd1]
  field_simp
  rw [show Real.sqrt τ ^ 2 = τ from h_sqrt_sq]
  ring

/-- **Vanna**: `∂²V/∂σ∂S = ∂(vega)/∂S = -ϕ(d₁) · d₂ / σ`.

Strategy: vega-as-function-of-S is `S · ϕ(d₁(S)) · √τ`. Product rule:
`d/dS = ϕ(d₁) √τ + S · ϕ'(d₁) · ∂_S d₁ · √τ`. With `ϕ'(d₁) = -d₁ ϕ(d₁)` and
`∂_S d₁ = 1/(S σ √τ)`, the S's cancel:
`= ϕ(d₁) √τ - d₁ ϕ(d₁) / σ = ϕ(d₁) (σ√τ − d₁) / σ = -ϕ(d₁) d₂ / σ`. -/
lemma hasDerivAt_bsV_vanna {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ s * gaussianPDFReal 0 1 (bsd1 s K r σ τ) * Real.sqrt τ)
      (-(gaussianPDFReal 0 1 (bsd1 S K r σ τ) * bsd2 S K r σ τ / σ)) S := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  have h_d1_S := hasDerivAt_bsd1_S (r := r) hK hσ hτ hS
  have h_pdf_d1 := (hasDerivAt_gaussianPDFReal_zero_one (bsd1 S K r σ τ)).comp S h_d1_S
  have h_id : HasDerivAt (fun s : ℝ ↦ s) 1 S := hasDerivAt_id S
  have h_prod := h_id.mul h_pdf_d1
  have h_full := h_prod.mul_const (Real.sqrt τ)
  convert h_full using 1 <;> try rfl
  simp only [Function.comp]
  rw [show bsd2 S K r σ τ = bsd1 S K r σ τ - σ * Real.sqrt τ from by rw [bsd2]]
  field_simp
  ring

/-- **Volga (Vomma)**: `∂²V/∂σ² = ∂(vega)/∂σ = vega · d₁ · d₂ / σ`.

Strategy: vega-as-function-of-σ is `S · ϕ(d₁(σ)) · √τ`. Chain rule via the
clean derivative `∂_σ d₁ = -d₂/σ` (above) and `ϕ'(d₁) = -d₁ ϕ(d₁)`:
`d/dσ[ϕ(d₁(σ))] = -d₁ ϕ(d₁) · (-d₂/σ) = d₁ d₂ ϕ(d₁) / σ`. Multiply by
constants S and √τ. -/
lemma hasDerivAt_bsV_volga {K r : ℝ} (_hK : 0 < K)
    {S σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ S * gaussianPDFReal 0 1 (bsd1 S K r s τ) * Real.sqrt τ)
      (S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) * Real.sqrt τ
        * bsd1 S K r σ τ * bsd2 S K r σ τ / σ) σ := by
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have h_d1_σ := hasDerivAt_bsd1_sigma_clean S K r hσ hτ
  have h_pdf_d1 := (hasDerivAt_gaussianPDFReal_zero_one (bsd1 S K r σ τ)).comp σ h_d1_σ
  have h_S := h_pdf_d1.const_mul S
  have h_full := h_S.mul_const (Real.sqrt τ)
  convert h_full using 1 <;> try rfl
  field_simp

/-- **Charm**: `∂Δ/∂τ = ∂Φ(d₁)/∂τ = ϕ(d₁) · ((r + σ²/2)τ − log(S/K)) / (2στ√τ)`.

The product/chain rules give `ϕ(d₁) · ∂_τ d₁`. The magic identity is not
needed here: `∂_τ d₁` already has a clean closed form. -/
lemma hasDerivAt_bsV_charm {K r σ : ℝ} (hσ : 0 < σ)
    {S τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t ↦ Phi (bsd1 S K r σ t))
      (gaussianPDFReal 0 1 (bsd1 S K r σ τ)
        * (((r + σ ^ 2 / 2) * τ - Real.log (S / K)) / (2 * σ * τ * Real.sqrt τ))) τ := by
  have h_d1_τ := hasDerivAt_bsd1_tau S K r σ hσ hτ
  have h_Phi_d1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp τ h_d1_τ
  convert h_Phi_d1 using 1 <;> rfl

/-- **Speed**: `∂³V/∂S³ = ∂Γ/∂S = -ϕ(d₁) (d₁ + σ√τ) / (S² σ² τ)`.

Gamma is the quotient `ϕ(d₁(S)) / (S σ √τ)` (`hasDerivAt_bsV_SS`), so speed is
one quotient rule away. Numerator derivative is `ϕ'(d₁) ∂_S d₁ = -d₁ ϕ(d₁)/(S σ √τ)`;
denominator derivative is the constant `σ √τ`. The two contributions carry `d₁`
and `σ√τ` respectively, which is where the `d₁ + σ√τ` numerator comes from —
and note the denominator is `S² σ² τ`, not `S² σ √τ`. -/
lemma hasDerivAt_bsV_SSS {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ gaussianPDFReal 0 1 (bsd1 s K r σ τ) / (s * σ * Real.sqrt τ))
      (-(gaussianPDFReal 0 1 (bsd1 S K r σ τ) * (bsd1 S K r σ τ + σ * Real.sqrt τ)
        / (S ^ 2 * σ ^ 2 * τ))) S := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  have h_num := (hasDerivAt_gaussianPDFReal_zero_one (bsd1 S K r σ τ)).comp S
    (hasDerivAt_bsd1_S (r := r) hK hσ hτ hS)
  have h_den : HasDerivAt (fun s : ℝ ↦ s * σ * Real.sqrt τ) (σ * Real.sqrt τ) S := by
    simpa using ((hasDerivAt_id S).mul_const σ).mul_const (Real.sqrt τ)
  -- Pin the quotient's expected type so `.div` elaborates against the goal's
  -- instances rather than handing back a Pi-`/` of functions.
  have h : HasDerivAt (fun s ↦ gaussianPDFReal 0 1 (bsd1 s K r σ τ) / (s * σ * Real.sqrt τ))
      ((-(bsd1 S K r σ τ * gaussianPDFReal 0 1 (bsd1 S K r σ τ)) * (1 / (S * σ * Real.sqrt τ))
            * (S * σ * Real.sqrt τ)
          - gaussianPDFReal 0 1 (bsd1 S K r σ τ) * (σ * Real.sqrt τ))
        / (S * σ * Real.sqrt τ) ^ 2) S :=
    h_num.div h_den (by positivity)
  convert h using 1
  rw [show S ^ 2 * σ ^ 2 * τ = (S * σ * Real.sqrt τ) ^ 2 from by
    rw [mul_pow, mul_pow, Real.sq_sqrt hτ.le]]
  field_simp
  ring

end MathFin
