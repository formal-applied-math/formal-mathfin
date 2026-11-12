/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.BlackScholes.PDE
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Higher-order Black–Scholes Greeks

For the European call price `V(S, σ, τ) = S Φ(d₁) − K e^{-rτ} Φ(d₂)`, the
second- and third-order Greeks, each stated for the price itself:

* **Vanna**: `∂/∂S (∂V/∂σ) = -ϕ(d₁) · d₂ / σ` (`hasDerivAt_S_deriv_bsV_sigma`).
* **Volga (aka vomma)**: `∂²V/∂σ² = vega · d₁ · d₂ / σ` (`hasDerivAt_deriv_bsV_sigma`).
* **Charm**: `∂/∂τ (∂V/∂S) = ϕ(d₁) · ((r + σ²/2)τ − log(S/K)) / (2στ√τ)`
  (`hasDerivAt_tau_deriv_bsV_S`).
* **Speed**: `∂³V/∂S³ = -ϕ(d₁) (d₁ + σ√τ) / (S² σ² τ)` (`hasDerivAt_deriv_deriv_bsV_S`).

Each comes in two steps. A formula lemma (`hasDerivAt_bsV_vanna`, …) differentiates
the closed form of the lower-order Greek. `hasDerivAt_deriv_of_eventually` (volga, speed)
or its mixed-partial form `hasDerivAt_deriv_param_of_eventually` (vanna, charm) then makes
it a statement about the price, since that closed form is the lower-order derivative near
the point.

With `ϕ'(z) = -z · ϕ(z)`, each formula is one chain rule plus one product, quotient or
scalar rule. Volga's uses the shortcut `∂_σ d₁ = -d₂/σ` (`hasDerivAt_bsd1_sigma_clean`
below), which compresses an otherwise messy quotient-rule expression; vanna's uses
`∂_S d₁` and collapses via `σ√τ − d₁ = -d₂`.

## Main results

All for `K, σ, S, τ > 0`.

* `hasDerivAt_S_deriv_bsV_sigma`: vanna, `∂/∂S (∂V/∂σ) = −ϕ(d₁) d₂ / σ`.
* `hasDerivAt_deriv_bsV_sigma`: volga, `∂²V/∂σ² = S ϕ(d₁) √τ d₁ d₂ / σ`.
* `hasDerivAt_tau_deriv_bsV_S`: charm, `∂/∂τ (∂V/∂S) = ϕ(d₁) ((r + σ²/2)τ − log(S/K)) / (2στ√τ)`.
* `hasDerivAt_deriv_deriv_bsV_S`: speed, `∂³V/∂S³ = −ϕ(d₁) (d₁ + σ√τ) / (S² σ² τ)`.
* `hasDerivAt_bsV_SSS`: the `S`-derivative of the gamma formula `ϕ(d₁) / (S σ √τ)`, which is
  the speed formula.
* `hasDerivAt_bsV_S_chainRule`, `hasDerivAt_bsV_param_chainRule`: when the volatility is itself
  a differentiable function `v` of the spot (substituted for both arguments of `bsV`) or of some
  other parameter, the price's derivative is `Δ_BS + Λ_BS · v'` resp. `Λ_BS · v'`. The first is
  proved from the joint Fréchet derivative of `bsV` in `(S, σ)`. Both take
  `DifferentiableAt ℝ v x` and state the slope as `deriv v x`.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 19.4
* [Wystup (2002)][Wystup2002]

## Tags

vanna, volga, vomma, speed, third-order Greeks, higher-order sensitivities, MSC 91G20, JEL G13
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
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have h_sqrt_sq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  rw [bsd2, bsd1]
  field_simp
  rw [show Real.sqrt τ ^ 2 = τ from h_sqrt_sq]
  ring

/-- **The vanna formula**: the S-derivative of the vega formula is `-ϕ(d₁) · d₂ / σ`. The
mixed partial of the price itself is `hasDerivAt_S_deriv_bsV_sigma`.

Strategy: vega-as-function-of-S is `S · ϕ(d₁(S)) · √τ`. Product rule:
`d/dS = ϕ(d₁) √τ + S · ϕ'(d₁) · ∂_S d₁ · √τ`. With `ϕ'(d₁) = -d₁ ϕ(d₁)` and
`∂_S d₁ = 1/(S σ √τ)`, the S's cancel:
`= ϕ(d₁) √τ - d₁ ϕ(d₁) / σ = ϕ(d₁) (σ√τ − d₁) / σ = -ϕ(d₁) d₂ / σ`. -/
private lemma hasDerivAt_bsV_vanna {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
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

/-- **Vanna**: `∂/∂S (∂V/∂σ) = -ϕ(d₁) · d₂ / σ`, for the call price itself: vega
`S · ϕ(d₁) · √τ` is `∂V/∂σ` at every spot `S > 0` (`hasDerivAt_bsV_sigma`), and its
S-derivative is the vanna formula (`hasDerivAt_bsV_vanna`). -/
theorem hasDerivAt_S_deriv_bsV_sigma {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ deriv (fun σ' ↦ bsV K r σ' s τ) σ)
      (-(gaussianPDFReal 0 1 (bsd1 S K r σ τ) * bsd2 S K r σ τ / σ)) S :=
  hasDerivAt_deriv_param_of_eventually
    ((eventually_gt_nhds hS).mono fun _ hs ↦ hasDerivAt_bsV_sigma hK hs hσ hτ)
    (hasDerivAt_bsV_vanna hK hσ hS hτ)

/-- **The volga (vomma) formula**: the σ-derivative of the vega formula is
`vega · d₁ · d₂ / σ`. The second σ-derivative of the price itself is
`hasDerivAt_deriv_bsV_sigma`.

Strategy: vega-as-function-of-σ is `S · ϕ(d₁(σ)) · √τ`. Chain rule via the
clean derivative `∂_σ d₁ = -d₂/σ` (above) and `ϕ'(d₁) = -d₁ ϕ(d₁)`:
`d/dσ[ϕ(d₁(σ))] = -d₁ ϕ(d₁) · (-d₂/σ) = d₁ d₂ ϕ(d₁) / σ`. Multiply by
constants S and √τ. -/
private lemma hasDerivAt_bsV_volga {K r S σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
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

/-- **Volga (vomma)**: `∂²V/∂σ² = vega · d₁ · d₂ / σ`, for the call price itself: vega is
`∂V/∂σ` at every volatility `σ > 0` (`hasDerivAt_bsV_sigma`), and its σ-derivative is the
volga formula (`hasDerivAt_bsV_volga`). -/
theorem hasDerivAt_deriv_bsV_sigma {K r : ℝ} (hK : 0 < K) {S σ τ : ℝ} (hS : 0 < S)
    (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (deriv fun σ' ↦ bsV K r σ' S τ)
      (S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) * Real.sqrt τ * bsd1 S K r σ τ *
        bsd2 S K r σ τ / σ) σ :=
  hasDerivAt_deriv_of_eventually
    ((eventually_gt_nhds hσ).mono fun _ hσ' ↦ hasDerivAt_bsV_sigma hK hS hσ' hτ)
    (hasDerivAt_bsV_volga hS hσ hτ)

/-- **The charm formula**: the τ-derivative of the delta formula `Φ(d₁)` is
`ϕ(d₁) · ((r + σ²/2)τ − log(S/K)) / (2στ√τ)`, by the chain rule: `∂_τ d₁` already has a clean
closed form, so the magic identity is not needed. The mixed partial of the price itself is
`hasDerivAt_tau_deriv_bsV_S`. -/
private lemma hasDerivAt_bsV_charm {K r σ : ℝ} (hσ : 0 < σ)
    {S τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t ↦ Phi (bsd1 S K r σ t))
      (gaussianPDFReal 0 1 (bsd1 S K r σ τ)
        * (((r + σ ^ 2 / 2) * τ - Real.log (S / K)) / (2 * σ * τ * Real.sqrt τ))) τ :=
  (hasDerivAt_Phi (bsd1 S K r σ τ)).comp τ (hasDerivAt_bsd1_tau S K r σ hσ hτ)

/-- **Charm**: `∂/∂τ (∂V/∂S) = ϕ(d₁) · ((r + σ²/2)τ − log(S/K)) / (2στ√τ)`, for the call
price itself: the delta `Φ(d₁)` is `∂V/∂S` at every maturity `τ > 0` (`hasDerivAt_bsV_S`),
and its τ-derivative is the charm formula (`hasDerivAt_bsV_charm`). -/
theorem hasDerivAt_tau_deriv_bsV_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun t ↦ deriv (fun s ↦ bsV K r σ s t) S)
      (gaussianPDFReal 0 1 (bsd1 S K r σ τ) *
        (((r + σ ^ 2 / 2) * τ - Real.log (S / K)) / (2 * σ * τ * Real.sqrt τ))) τ :=
  hasDerivAt_deriv_param_of_eventually
    ((eventually_gt_nhds hτ).mono fun _ ht ↦ hasDerivAt_bsV_S hK hσ hS ht)
    (hasDerivAt_bsV_charm hσ hτ)

/-- **The speed formula**: the S-derivative of the gamma formula is
`-ϕ(d₁) (d₁ + σ√τ) / (S² σ² τ)`. The third derivative of the price itself is
`hasDerivAt_deriv_deriv_bsV_S`.

Gamma is the quotient `ϕ(d₁(S)) / (S σ √τ)` (`hasDerivAt_deriv_bsV_S`), so speed is
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

/-- **Speed**: `∂³V/∂S³ = -ϕ(d₁) (d₁ + σ√τ) / (S² σ² τ)`, for the call price itself: the
genuine gamma `hasDerivAt_deriv_bsV_S` holds on all of `S > 0`, and the derivative of its
formula is `hasDerivAt_bsV_SSS`. -/
theorem hasDerivAt_deriv_deriv_bsV_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (deriv (deriv fun s ↦ bsV K r σ s τ))
      (-(gaussianPDFReal 0 1 (bsd1 S K r σ τ) * (bsd1 S K r σ τ + σ * Real.sqrt τ) /
        (S ^ 2 * σ ^ 2 * τ))) S :=
  hasDerivAt_deriv_of_eventually
    ((eventually_gt_nhds hS).mono fun _ hs ↦ hasDerivAt_deriv_bsV_S hK hσ hs hτ)
    (hasDerivAt_bsV_SSS hK hσ hS hτ)


/-! ### Chain rule when the volatility is itself a function

These hold for any differentiable vol function `v`: the price's derivative is the Black–Scholes
delta and vega combined with the slope of `v`. -/

/-- **The vol-curve Delta chain rule**: if the implied vol used to price a call is
itself a differentiable function `v` of the spot/forward — substituted for *both*
arguments of `bsV` simultaneously, `s ↦ bsV K r (v s) s τ` — the price's derivative at
`S` is `Δ_BS + Λ_BS · v'`, the ordinary Black-Scholes delta and vega (both evaluated at
`σ = v S`) combined with the vol curve's own slope `v' = deriv v S`.

The proof is a total derivative: `bsV` is differentiable as a function of `(S, σ) ∈ ℝ × ℝ`
jointly (`fun_prop` over its elementary pieces, with `Phi`'s own `HasDerivAt` supplied for the
two composed `Phi ∘ bsd1`, `Phi ∘ bsd2` legs). Its Fréchet derivative `F` is identified on the
two coordinate directions with `hasDerivAt_bsV_S` and `hasDerivAt_bsV_sigma`, and composing it
with the path `s ↦ (s, v s)` gives `F (1, v') = F (1, 0) + v' · F (0, 1)`. -/
theorem hasDerivAt_bsV_S_chainRule {K r : ℝ} (hK : 0 < K) {S τ : ℝ} (hS : 0 < S) {v : ℝ → ℝ}
    (hσ : 0 < v S) (hτ : 0 < τ) (hv : DifferentiableAt ℝ v S) :
    HasDerivAt (fun s ↦ bsV K r (v s) s τ)
      (Phi (bsd1 S K r (v S) τ)
        + S * gaussianPDFReal 0 1 (bsd1 S K r (v S) τ) * Real.sqrt τ * deriv v S) S := by
  have h1 : S / K ≠ 0 := div_ne_zero hS.ne' hK.ne'
  have h2 : v S * Real.sqrt τ ≠ 0 := mul_ne_zero hσ.ne' (Real.sqrt_pos.mpr hτ).ne'
  have hd1 : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ bsd1 p.1 K r p.2 τ) (S, v S) := by
    unfold bsd1; fun_prop (disch := assumption)
  have hd2 : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ bsd2 p.1 K r p.2 τ) (S, v S) := by
    unfold bsd2 bsd1; fun_prop (disch := assumption)
  have hg : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ bsV K r p.2 p.1 τ) (S, v S) := by
    have hP1 := (hasDerivAt_Phi (bsd1 S K r (v S) τ)).differentiableAt.comp (S, v S) hd1
    have hP2 := (hasDerivAt_Phi (bsd2 S K r (v S) τ)).differentiableAt.comp (S, v S) hd2
    unfold bsV; fun_prop (disch := assumption)
  have hF := hg.hasFDerivAt
  have hS_eq : fderiv ℝ (fun p : ℝ × ℝ ↦ bsV K r p.2 p.1 τ) (S, v S) (1, 0) =
      Phi (bsd1 S K r (v S) τ) := by
    have h := hF.comp_hasDerivAt S ((hasDerivAt_id S).prodMk (hasDerivAt_const S (v S)))
    exact h.unique (hasDerivAt_bsV_S hK hσ hS hτ)
  have hσ_eq : fderiv ℝ (fun p : ℝ × ℝ ↦ bsV K r p.2 p.1 τ) (S, v S) (0, 1) =
      S * gaussianPDFReal 0 1 (bsd1 S K r (v S) τ) * Real.sqrt τ := by
    have h := hF.comp_hasDerivAt (v S) ((hasDerivAt_const (v S) S).prodMk (hasDerivAt_id (v S)))
    exact h.unique (hasDerivAt_bsV_sigma hK hS hσ hτ)
  have hlin : ((1 : ℝ), deriv v S) = (1, (0 : ℝ)) + deriv v S • ((0 : ℝ), (1 : ℝ)) := by simp
  have h := hF.comp_hasDerivAt S ((hasDerivAt_id S).prodMk hv.hasDerivAt)
  rw [hlin, map_add, map_smul, hS_eq, hσ_eq] at h
  exact h.congr_deriv (by simp; ring)

/-- **The vol-parameter Vega chain rule**: if the spot/forward is held FIXED and the vol
moves only through some other parameter `a` (e.g. `α`), the price's derivative in `a` is
just the ordinary Black-Scholes vega times the vol's own sensitivity, `Λ_BS · v'` — the
plain one-variable chain rule through `hasDerivAt_bsV_sigma` (no bivariate argument
needed, since only one argument of `bsV` moves). -/
theorem hasDerivAt_bsV_param_chainRule {K r S τ : ℝ} (hK : 0 < K) (hS : 0 < S) {v : ℝ → ℝ}
    {x : ℝ} (hσ : 0 < v x) (hτ : 0 < τ) (hv : DifferentiableAt ℝ v x) :
    HasDerivAt (fun a ↦ bsV K r (v a) S τ)
      (S * gaussianPDFReal 0 1 (bsd1 S K r (v x) τ) * Real.sqrt τ * deriv v x) x :=
  (hasDerivAt_bsV_sigma hK hS hσ hτ).comp x hv.hasDerivAt

end MathFin
