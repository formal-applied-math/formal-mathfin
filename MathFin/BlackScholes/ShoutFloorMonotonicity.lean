/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.BlackScholes.DividendsGreeks

/-!
# Shout-floor monotonicity: Dai–Kwok–Wu (2004), Lemma 2.1(i)

**Scope disclaimer**: this file proves one *supporting* calculus lemma from
Dai, Kwok & Wu (2004), "Optimal Shouting Policies of Options with Strike Reset
Right," *Mathematical Finance* 14(3), 383-401 — **Lemma 2.1, case (i)** (p. 387).
It is **not** their Theorem 3.1 (the shout-floor pricing formula itself).
Theorem 3.1 identifies the shout-floor value `R(S, τ)` with the ATM-put value
`S · P(τ)` via a free-boundary / optimal-stopping argument (shout as soon as
holding no longer dominates the reward); this library currently has **no**
optimal-stopping or free-boundary substrate (`grep -rln
"optimalStopping\|freeBoundary\|americanOption"` over `MathFin/` turns up
nothing reusable for this payoff), so that step is out of reach here. What
*is* pure calculus, and is what this file proves: the function whose sign
drives that argument,

  `g(τ) := e^{qτ} · P(τ)`,

is strictly increasing on `(0, ∞)` whenever `r ≤ q`, where `P(τ)` is the
Black–Scholes ATM (`K = S`) put value with continuous dividend yield `q`:

  `P(τ) = e^{-rτ} · N(-d₂) - e^{-qτ} · N(-d₁)`,
  `d₁ = (r - q + σ²/2) √τ / σ`,  `d₂ = d₁ - σ √τ`.

Since `P(τ)` does not depend on the common value of `S = K` (the `log(S/K)`
term in `bsd1`/`bsd2` vanishes on the diagonal), we model it as the `S = K = 1`
instance of the repo's existing `bsPDiv` (`DividendsGreeks.lean`):
`shoutFloorAtmPut r q σ τ := bsPDiv 1 r q σ 1 τ`. For general `S`, the paper's
`R(S, τ) = S · P(τ)` claim is the *statement* of Theorem 3.1 (not proved here);
only the ATM-put side `P(τ)` is built and analyzed in this file.

## What this gives, and what is still missing

`shoutFloor_g_strictMonoOn` is exactly Dai–Kwok–Wu Lemma 2.1(i). To reach
their Theorem 3.1(i) (`R(S, τ) = S · P(τ)` for all `τ > 0` when `r ≤ q`) from
here still needs: (a) a linear-complementarity / free-boundary formulation of
the shout-floor value as an optimal-stopping problem, and (b) the argument
that a monotone-increasing discounted reward (`g` above) forces immediate
exercise, so value = reward everywhere. Neither exists in this library yet;
building them is a substantially larger undertaking (general optimal-stopping
verification theorems, not just this one closed-form computation).

## Main result

* `shoutFloorAtmPut` — the ATM (`K = S = 1`) Black–Scholes put with dividend
  yield `q`, as a function of `τ` alone: `P(τ)`.
* `hasDerivAt_shoutFloorAtmPut_tau` — its `τ`-derivative, by the product rule
  on `bsPDiv = e^{-qτ} · bsP` (mirrors `hasDerivAt_bsVDiv_tau`).
* `shoutFloor_discriminant_pos` — for `r ≤ q`, `σ > 0`, the derivative of
  `g(τ) = e^{qτ} P(τ)` is strictly positive on `(0, ∞)`: the `q · P(τ)` terms
  from the product rule cancel exactly, leaving
  `g'(τ) = σ · ϕ(d₁) / (2√τ) - (r - q) · e^{-(r-q)τ} · Φ(-d₂)`, a sum of two
  nonnegative terms (the first strictly positive).
* `shoutFloor_g_strictMonoOn` — **Lemma 2.1(i)**: `g` is `StrictMonoOn (Ioi 0)`
  when `r ≤ q`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- The Black–Scholes **ATM** (`K = S = 1`) put value with continuous dividend
yield `q`, as a function of time-to-maturity `τ`: Dai–Kwok–Wu's `P(τ)`. Taking
`S = K = 1` is WLOG — the `log(S/K)` term in `bsd1`/`bsd2` vanishes whenever
`S = K`, for any common value, so `P(τ)` does not depend on it. -/
noncomputable def shoutFloorAtmPut (r q σ τ : ℝ) : ℝ := bsPDiv 1 r q σ 1 τ

/-- **`τ`-derivative of the ATM put** `P(τ)`, by the product rule on
`bsPDiv = e^{-qτ} · bsP(·, r - q, σ, ·, ·)`, exactly mirroring the call version
`hasDerivAt_bsVDiv_tau`. -/
theorem hasDerivAt_shoutFloorAtmPut_tau {r q σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (shoutFloorAtmPut r q σ)
      (-(q * shoutFloorAtmPut r q σ τ) +
        Real.exp (-(q * τ)) *
          (σ * gaussianPDFReal 0 1 (bsd1 1 1 (r - q) σ τ) / (2 * Real.sqrt τ)
            - (r - q) * Real.exp (-((r - q) * τ)) * Phi (-bsd2 1 1 (r - q) σ τ))) τ := by
  have h_f : HasDerivAt (fun t : ℝ ↦ Real.exp (-(q * t))) (-q * Real.exp (-(q * τ))) τ := by
    have h_neg : HasDerivAt (fun t : ℝ ↦ -(q * t)) (-q) τ := by
      have := (hasDerivAt_id τ).const_mul q
      convert this.neg using 1 <;> first | rfl | ring
    have h := h_neg.exp
    convert h using 1
    ring
  have h_g := hasDerivAt_bsP_tau (r := r - q) (K := 1) (S := 1)
    one_pos hσ one_pos hτ
  have h_full := h_f.mul h_g
  unfold shoutFloorAtmPut bsPDiv
  convert h_full using 1
  ring

/-- **The shout-floor discriminant is strictly positive** whenever `r ≤ q`.
This is the formula-level content of Lemma 2.1(i): in the product-rule
derivative of `g(τ) = e^{qτ} P(τ)`, the `q · P(τ)` contributions cancel
exactly, leaving `g'(τ) = σ · ϕ(d₁) / (2√τ) - (r - q) · e^{-(r-q)τ} · Φ(-d₂)` —
a strictly positive first term plus a nonnegative second term, since
`r ≤ q ⟹ -(r - q) ≥ 0`. -/
theorem shoutFloor_discriminant_pos {r q σ τ : ℝ} (hrq : r ≤ q) (hσ : 0 < σ) (hτ : 0 < τ) :
    0 < σ * gaussianPDFReal 0 1 (bsd1 1 1 (r - q) σ τ) / (2 * Real.sqrt τ)
      - (r - q) * Real.exp (-((r - q) * τ)) * Phi (-bsd2 1 1 (r - q) σ τ) := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_pdf_pos : 0 < gaussianPDFReal 0 1 (bsd1 1 1 (r - q) σ τ) :=
    gaussianPDFReal_pos 0 1 _ (one_ne_zero : (1 : ℝ≥0) ≠ 0)
  have h_term1_pos : 0 < σ * gaussianPDFReal 0 1 (bsd1 1 1 (r - q) σ τ) / (2 * Real.sqrt τ) := by
    positivity
  have h_phi_nonneg : 0 ≤ Phi (-bsd2 1 1 (r - q) σ τ) := Phi_nonneg _
  have h_rq_nonneg : 0 ≤ -(r - q) := by linarith
  have h_term2_nonneg :
      0 ≤ -((r - q) * Real.exp (-((r - q) * τ)) * Phi (-bsd2 1 1 (r - q) σ τ)) := by
    have : 0 ≤ -(r - q) * Real.exp (-((r - q) * τ)) * Phi (-bsd2 1 1 (r - q) σ τ) := by
      positivity
    linarith
  linarith

/-- **`g(τ) = e^{qτ} P(τ)` is differentiable with derivative the discriminant
of `shoutFloor_discriminant_pos`.** The `q · P(τ)` term from differentiating
`e^{qτ}` exactly cancels the `-(q · P(τ))` term from
`hasDerivAt_shoutFloorAtmPut_tau`, via `Real.exp (q * τ) * Real.exp (-(q * τ)) = 1`. -/
theorem hasDerivAt_shoutFloor_g {r q σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (fun t ↦ Real.exp (q * t) * shoutFloorAtmPut r q σ t)
      (σ * gaussianPDFReal 0 1 (bsd1 1 1 (r - q) σ τ) / (2 * Real.sqrt τ)
        - (r - q) * Real.exp (-((r - q) * τ)) * Phi (-bsd2 1 1 (r - q) σ τ)) τ := by
  have h_exp : HasDerivAt (fun t : ℝ ↦ Real.exp (q * t)) (q * Real.exp (q * τ)) τ := by
    have h_lin : HasDerivAt (fun t : ℝ ↦ q * t) q τ := by
      simpa using (hasDerivAt_id τ).const_mul q
    have h := h_lin.exp
    convert h using 1
    ring
  have h_P := hasDerivAt_shoutFloorAtmPut_tau (r := r) (q := q) hσ hτ
  have h_full := h_exp.mul h_P
  have h_cancel : Real.exp (q * τ) * Real.exp (-(q * τ)) = 1 := by
    rw [← Real.exp_add]; simp
  convert h_full using 1
  have h_expand :
      q * Real.exp (q * τ) * shoutFloorAtmPut r q σ τ +
        Real.exp (q * τ) *
          (-(q * shoutFloorAtmPut r q σ τ) +
            Real.exp (-(q * τ)) *
              (σ * gaussianPDFReal 0 1 (bsd1 1 1 (r - q) σ τ) / (2 * Real.sqrt τ)
                - (r - q) * Real.exp (-((r - q) * τ)) * Phi (-bsd2 1 1 (r - q) σ τ)))
        = (Real.exp (q * τ) * Real.exp (-(q * τ))) *
            (σ * gaussianPDFReal 0 1 (bsd1 1 1 (r - q) σ τ) / (2 * Real.sqrt τ)
              - (r - q) * Real.exp (-((r - q) * τ)) * Phi (-bsd2 1 1 (r - q) σ τ)) := by
    ring
  rw [h_expand, h_cancel, one_mul]

/-- **`g` is continuous on `(0, ∞)`**: it is differentiable there
(`hasDerivAt_shoutFloor_g`). -/
theorem shoutFloor_g_continuousOn {r q σ : ℝ} (hσ : 0 < σ) :
    ContinuousOn (fun t ↦ Real.exp (q * t) * shoutFloorAtmPut r q σ t) (Set.Ioi 0) :=
  fun _ hτ ↦ (hasDerivAt_shoutFloor_g hσ hτ).continuousAt.continuousWithinAt

/-- **Dai–Kwok–Wu (2004), Lemma 2.1(i).** For `r ≤ q` and `σ > 0`, the function
`g(τ) = e^{qτ} P(τ)` is strictly increasing on `(0, ∞)`, where `P(τ)` is the
ATM Black–Scholes put value with dividend yield `q`
(`shoutFloorAtmPut r q σ`). This is the supporting monotonicity result behind
their Theorem 3.1(i) (`R(S, τ) = S · P(τ)` for `r ≤ q`) — see the module
docstring for exactly what is and is not proved here. -/
theorem shoutFloor_g_strictMonoOn {r q σ : ℝ} (hrq : r ≤ q) (hσ : 0 < σ) :
    StrictMonoOn (fun t ↦ Real.exp (q * t) * shoutFloorAtmPut r q σ t) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (shoutFloor_g_continuousOn hσ)
  intro τ hτ_int
  rw [interior_Ioi] at hτ_int
  rw [(hasDerivAt_shoutFloor_g hσ hτ_int).deriv]
  exact shoutFloor_discriminant_pos hrq hσ hτ_int

end MathFin
