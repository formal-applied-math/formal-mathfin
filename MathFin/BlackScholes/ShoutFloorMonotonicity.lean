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

This file proves Dai, Kwok & Wu (2004), "Optimal Shouting Policies of Options
with Strike Reset Right," *Mathematical Finance* 14(3), 383-401, **Lemma 2.1,
case (i)** (p. 386): the shout floor's scaled ATM put

  `g(τ) := e^{qτ} · P(τ)`,

is strictly increasing on `(0, ∞)` whenever `r ≤ q`, where `P(τ)` is the
Black–Scholes ATM (`K = S`) put value with continuous dividend yield `q`:

  `P(τ) = e^{-rτ} · N(-d₂) - e^{-qτ} · N(-d₁)`,
  `d₁ = (r - q + σ²/2) √τ / σ`,  `d₂ = d₁ - σ √τ`.

(The paper leaves `e^{qτ}P(τ)` unnamed here and reuses `g` for the normalized
shout-floor price `R(S, τ)/S` in its §3; the `g` in this file is the scaled
put above, not that one.)

The ATM put is linearly homogeneous on the diagonal — `bsPDiv K r q σ K τ =
K · P(τ)` (`bsPDiv_diagonal_eq_shoutFloorAtmPut`; the `log(S/K)` term in
`bsd1`/`bsd2` vanishes there) — so we model `P(τ)` as the `S = K = 1` instance
of the repo's existing `bsPDiv` (`DividendsGreeks.lean`):
`shoutFloorAtmPut r q σ τ := bsPDiv 1 r q σ 1 τ`.

**Scope**: `shoutFloor_g_strictMonoOn` is exactly Lemma 2.1(i), not the
paper's Theorem 3.1 (the shout-floor pricing identity `R(S, τ) = S · P(τ)`
itself, for `r ≤ q`). Reaching Theorem 3.1(i) from here needs the shout-floor
value as an optimal-stopping value on the library's Brownian model, plus
optional stopping for the *unbounded* discounted-stock martingale
`e^{-(r−q)t} S_t` — this library's optimal-stopping substrate
(`MathFin/BlackScholes/AmericanPut/Stopping/*`) is built around the bounded,
time-independent vanilla put reward, so it does not apply here as stated; a
truncation argument (`min(·, N)` plus monotone convergence) would avoid
needing a full uniform-integrability bridge, but neither that nor the
stopping-value wiring is built here.

## Main result

* `shoutFloorAtmPut` — the ATM (`K = S = 1`) Black–Scholes put with dividend
  yield `q`, as a function of `τ` alone: `P(τ)`; `bsPDiv_diagonal_eq_shoutFloorAtmPut`
  is the diagonal homogeneity `bsPDiv K r q σ K τ = K · P(τ)` that makes `K = 1` WLOG.
* `shoutFloor_g_eq_bsP` — Dai–Kwok–Wu's own first reduction, Appendix A (p. 397):
  `e^{qτ} P(τ; r, q) = P(τ; r - q, 0)`, i.e. `g(τ)` is literally the ordinary
  (no-dividend) ATM put `bsP 1 (r - q) σ 1 τ` at the shifted rate `r - q`.
* `hasDerivAt_shoutFloor_g` — `g`'s `τ`-derivative follows immediately via
  `shoutFloor_g_eq_bsP` from the library's own `hasDerivAt_bsP_tau` (at
  `K = S = 1`, rate `r - q`) — no new differentiation needed, matching the
  paper's own printed route rather than re-deriving a product rule on `bsPDiv`.
* `shoutFloor_discriminant_pos` — for `r ≤ q`, `σ > 0`, that derivative
  `g'(τ) = σ · ϕ(d₁) / (2√τ) - (r - q) · e^{-(r-q)τ} · Φ(-d₂)` is strictly
  positive: a sum of two nonnegative terms (the first strictly positive).
* `shoutFloor_g_strictMonoOn` — **Lemma 2.1(i)**: `g` is `StrictMonoOn (Ioi 0)`
  when `r ≤ q`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- The Black–Scholes **ATM** (`K = S = 1`) put value with continuous dividend
yield `q`, as a function of time-to-maturity `τ`: Dai–Kwok–Wu's `P(τ)`. Taking
`S = K = 1` is the paper's normalization; `bsPDiv_diagonal_eq_shoutFloorAtmPut`
shows the general diagonal value is `K · P(τ)`. -/
noncomputable def shoutFloorAtmPut (r q σ τ : ℝ) : ℝ := bsPDiv 1 r q σ 1 τ

/-- **Diagonal homogeneity of the dividend-yield put**: `bsPDiv K r q σ K τ = K · P(τ)`
for `K > 0`. The `log(S/K)` term in `bsd1`/`bsd2` vanishes on the diagonal, so `d₁`, `d₂`
are those of `shoutFloorAtmPut` and the price scales linearly in the common value. -/
theorem bsPDiv_diagonal_eq_shoutFloorAtmPut {K : ℝ} (hK : 0 < K) (r q σ τ : ℝ) :
    bsPDiv K r q σ K τ = K * shoutFloorAtmPut r q σ τ := by
  unfold shoutFloorAtmPut bsPDiv bsP bsd2 bsd1
  rw [div_self hK.ne', div_one, Real.log_one]
  ring

/-- **Dai–Kwok–Wu's Appendix A reduction** (p. 397, first line): the scaled
ATM put `e^{qτ} P(τ; r, q)` is exactly the ordinary (no-dividend) ATM put at
the shifted rate `r - q`: `g(τ) = e^{qτ}·P(τ) = bsP 1 (r - q) σ 1 τ`. -/
theorem shoutFloor_g_eq_bsP (r q σ τ : ℝ) :
    Real.exp (q * τ) * shoutFloorAtmPut r q σ τ = bsP 1 (r - q) σ 1 τ := by
  unfold shoutFloorAtmPut bsPDiv
  rw [← mul_assoc, ← Real.exp_add]
  simp

/-- **The shout-floor discriminant is strictly positive** whenever `r ≤ q`.
This is the formula-level content of Lemma 2.1(i): `g(τ) = e^{qτ} P(τ)`'s
derivative is `g'(τ) = σ · ϕ(d₁) / (2√τ) - (r - q) · e^{-(r-q)τ} · Φ(-d₂)` —
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
of `shoutFloor_discriminant_pos`.** Via `shoutFloor_g_eq_bsP`, `g` is literally
`bsP 1 (r - q) σ 1 ·`, so this is a direct instance of the library's own
`hasDerivAt_bsP_tau` at the shifted rate `r - q` -- no new product-rule
cancellation needed, matching the paper's own reduction (Appendix A). Appendix A
prints the derivative's first term as `e^{-(r-q)τ} σ n(-d₂) / (2√τ)` rather than
`σ ϕ(d₁) / (2√τ)`; the two agree on the diagonal `S = K` via
`ϕ(d₁) = e^{-(r-q)τ} ϕ(d₂)`, so this is the same value in the library's own
printed form, not a different quantity. -/
theorem hasDerivAt_shoutFloor_g {r q σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (fun t ↦ Real.exp (q * t) * shoutFloorAtmPut r q σ t)
      (σ * gaussianPDFReal 0 1 (bsd1 1 1 (r - q) σ τ) / (2 * Real.sqrt τ)
        - (r - q) * Real.exp (-((r - q) * τ)) * Phi (-bsd2 1 1 (r - q) σ τ)) τ := by
  have h_eq : (fun t ↦ Real.exp (q * t) * shoutFloorAtmPut r q σ t)
      = fun t ↦ bsP 1 (r - q) σ 1 t := funext fun t ↦ shoutFloor_g_eq_bsP r q σ t
  rw [h_eq]
  convert hasDerivAt_bsP_tau (r := r - q) (K := 1) (S := 1) one_pos hσ one_pos hτ using 1
  ring

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
