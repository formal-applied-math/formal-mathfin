/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.StandardNormal

/-!
# Soft barrier options: Hart & Ross's closed form

A "soft" barrier option does not knock in/out at a single level but across a **corridor**
`[L, U]`: the knock-in probability ramps linearly as the underlying's terminal log-price sweeps
the band, rather than jumping at a single barrier (Hart & Ross 1994; Haug, *The Complete Guide
to Option Pricing Formulas*, §4.17.6 "Soft Barrier Options"). Single-underlying, single-variable
Black–Scholes machinery — no bivariate normal CDF, matching the coverage-map note that #63 is
one of the two simplest standalone wins in this batch.

Transcribed from, and cross-checked against, QuantLib's
`ql/pricingengines/barrier/analyticsoftbarrierengine.cpp`
(`AnalyticSoftBarrierEngine::knockInValue`, upstream commit `5f4811e`, 2026-10-16, contributed
2025 by William Day). QuantLib additionally special-cases `S` already knocked in/out and the
degenerate `U = L` (single-barrier) limit; those branches, and the `r = q` singularity guard
the engine applies before calling `knockInValue`, are out of scope here — this file transcribes
exactly `knockInValue`'s closed form for `U ≠ L`.

With cost-of-carry `b = r − q`, `μ = (b + σ²/2)/σ²`, `√T` as usual, and the two mixing factors

  `λ₁ = exp(−σ²T(μ+½)(μ−½)/2)`,  `λ₂ = exp(−σ²T(μ−½)(μ−3/2)/2)`,

the `d`/`e` exponents (all against `log(U²/(SX))` or `log(L²/(SX))`, i.e. the corridor reflected
through the strike) are

  `d₁ = log(U²/(SX))/(σ√T) + μσ√T`,  `d₂ = d₁ − (μ+½)σ√T`,
  `d₃ = log(U²/(SX))/(σ√T) + (μ−1)σ√T`,  `d₄ = d₃ − (μ−½)σ√T`,

and `e₁, e₂, e₃, e₄` the same four with `U` replaced by `L`. Writing `A₁ = (U²/(SX))^{μ+½}`,
`A₂ = (L²/(SX))^{μ+½}`, `B₁ = (U²/(SX))^{μ−½}`, `B₂ = (L²/(SX))^{μ−½}` (as `exp(·log·)`, matching
the `BinaryBarrierOption.lean` convention), `η = 1` for a call / `η = −1` for a put, and

  `C₁ = ηS·e^{(b−r)T}·S^{−2μ}·(SX)^{μ+½} / (2(μ+½))`,
  `C₂ = ηX·e^{−rT}·S^{−2(μ−1)}·(SX)^{μ−½} / (2(μ−1/2))`

the two terms are `term₁ = C₁·(A₁Φ(ηd₁) − λ₁Φ(ηd₂) − A₂Φ(ηe₁) + λ₁Φ(ηe₂))` and
`term₂ = C₂·(B₁Φ(ηd₃) − λ₂Φ(ηd₄) − B₂Φ(ηe₃) + λ₂Φ(ηe₄))`, with the knock-in value
`w = (term₁ − term₂)/(U − L)` (the knock-out value is `vanilla − w`, standard in–out parity, not
separately formalized here for the same reason noted in `HeynenKatTwoAssetBarrier.lean`: it is
the *definition* QuantLib itself uses, not an independent theorem).

## Main results

* `sb_eta_diff_helper`: the algebraic core — for any coefficient `C`, mixing weights `A₁, A₂,
  λ`, and exponents, `η·C·(A₁Φ(ηd₁) − λΦ(ηd₂) − A₂Φ(ηe₁) + λΦ(ηe₂))` at `η = 1` minus the same at
  `η = −1` collapses to `C·(A₁ − A₂)` — the `λ` terms cancel exactly and every `Φ(η·)` pair
  disappears via `Phi_neg`.
* `softBarrier_call_sub_put`: applying the helper to both `term₁` and `term₂` gives
  `w(call) − w(put) = (C₁(A₁−A₂) − C₂(B₁−B₂))/(U−L)` — a genuine cross-check that the `η`
  sign is applied consistently to **both** the outer prefactor and every `Φ` argument, and that
  `λ₁, λ₂` (which QuantLib computes without any `η` dependence) are transcribed that way too: a
  stray extra/missing `η` on any one of the eight `Φ` terms, or an accidental `η` creeping into
  `λ₁`/`λ₂`, breaks the clean cancellation and the right-hand side would retain `Φ` terms.

**Scope, disclosed honestly**: this verifies the closed form's internal `η`-symmetry, not a
from-first-principles derivation of the corridor-crossing probability (the genuinely hard step —
reducing a "soft" barrier to a mixture of Black–Scholes-style terms via Hart & Ross's integration
over the corridor — is Haug's/QuantLib's analytic content, taken as given, exactly as the
two-asset and binary barrier files in this batch take the Heynen–Kat/Rubinstein–Reiner closed
forms as given rather than re-deriving them from a joint density).
-/

@[expose] public section

namespace MathFin

open Real

/-- **`μ = (b + σ²/2)/σ²`** (Haug/QuantLib's soft-barrier drift; distinct from `hkMu`/the binary
barrier's `mu`, which use `b − σ²/2`). -/
noncomputable def sbMu (b σ : ℝ) : ℝ := (b + σ ^ 2 / 2) / σ ^ 2

/-- **`λ₁`**, the mixing weight paired with `d₂, e₂`. -/
noncomputable def sbLambda1 (b σ T : ℝ) : ℝ :=
  Real.exp (-(σ ^ 2 * T * (sbMu b σ + 1 / 2) * (sbMu b σ - 1 / 2)) / 2)

/-- **`λ₂`**, the mixing weight paired with `d₄, e₄`. -/
noncomputable def sbLambda2 (b σ T : ℝ) : ℝ :=
  Real.exp (-(σ ^ 2 * T * (sbMu b σ - 1 / 2) * (sbMu b σ - 3 / 2)) / 2)

/-- **`d₁`**, against the upper corridor edge `U`. -/
noncomputable def sbD1 (S X U b σ T : ℝ) : ℝ :=
  Real.log (U ^ 2 / (S * X)) / (σ * Real.sqrt T) + sbMu b σ * σ * Real.sqrt T

/-- **`d₂` = `d₁ − (μ+½)σ√T`**. -/
noncomputable def sbD2 (S X U b σ T : ℝ) : ℝ :=
  sbD1 S X U b σ T - (sbMu b σ + 1 / 2) * σ * Real.sqrt T

/-- **`d₃`**, the `term₂`-side analogue of `d₁`. -/
noncomputable def sbD3 (S X U b σ T : ℝ) : ℝ :=
  Real.log (U ^ 2 / (S * X)) / (σ * Real.sqrt T) + (sbMu b σ - 1) * σ * Real.sqrt T

/-- **`d₄` = `d₃ − (μ−½)σ√T`**. -/
noncomputable def sbD4 (S X U b σ T : ℝ) : ℝ :=
  sbD3 S X U b σ T - (sbMu b σ - 1 / 2) * σ * Real.sqrt T

/-- **`e₁`**: `d₁` with `U` replaced by the lower corridor edge `L`. -/
noncomputable def sbE1 (S X L b σ T : ℝ) : ℝ := sbD1 S X L b σ T

/-- **`e₂`**: `d₂` with `U` replaced by `L`. -/
noncomputable def sbE2 (S X L b σ T : ℝ) : ℝ := sbD2 S X L b σ T

/-- **`e₃`**: `d₃` with `U` replaced by `L`. -/
noncomputable def sbE3 (S X L b σ T : ℝ) : ℝ := sbD3 S X L b σ T

/-- **`e₄`**: `d₄` with `U` replaced by `L`. -/
noncomputable def sbE4 (S X L b σ T : ℝ) : ℝ := sbD4 S X L b σ T

/-- **`(U²/(SX))^{μ+½}`**, written as `exp(·log·)` as in `BinaryBarrierOption.lean`. -/
noncomputable def sbA1 (S X U b σ : ℝ) : ℝ :=
  Real.exp ((sbMu b σ + 1 / 2) * Real.log (U ^ 2 / (S * X)))

/-- **`(L²/(SX))^{μ+½}`**. -/
noncomputable def sbA2 (S X L b σ : ℝ) : ℝ :=
  Real.exp ((sbMu b σ + 1 / 2) * Real.log (L ^ 2 / (S * X)))

/-- **`(U²/(SX))^{μ−½}`**. -/
noncomputable def sbBB1 (S X U b σ : ℝ) : ℝ :=
  Real.exp ((sbMu b σ - 1 / 2) * Real.log (U ^ 2 / (S * X)))

/-- **`(L²/(SX))^{μ−½}`**. -/
noncomputable def sbBB2 (S X L b σ : ℝ) : ℝ :=
  Real.exp ((sbMu b σ - 1 / 2) * Real.log (L ^ 2 / (S * X)))

/-- **`term₁`'s prefactor `C₁`**. -/
noncomputable def sbTerm1Coef (S X b r σ T : ℝ) : ℝ :=
  S * Real.exp ((b - r) * T) * Real.exp (-2 * sbMu b σ * Real.log S)
    * Real.exp ((sbMu b σ + 1 / 2) * Real.log (S * X)) / (2 * (sbMu b σ + 1 / 2))

/-- **`term₂`'s prefactor `C₂`**. -/
noncomputable def sbTerm2Coef (S X b r σ T : ℝ) : ℝ :=
  X * Real.exp (-r * T) * Real.exp (-2 * (sbMu b σ - 1) * Real.log S)
    * Real.exp ((sbMu b σ - 1 / 2) * Real.log (S * X)) / (2 * (sbMu b σ - 1 / 2))

/-- **`term₁(η)`**. -/
noncomputable def sbTerm1 (eta S X U L b r σ T : ℝ) : ℝ :=
  eta * sbTerm1Coef S X b r σ T *
    (sbA1 S X U b σ * Phi (eta * sbD1 S X U b σ T) - sbLambda1 b σ T * Phi (eta * sbD2 S X U b σ T)
      - sbA2 S X L b σ * Phi (eta * sbE1 S X L b σ T)
      + sbLambda1 b σ T * Phi (eta * sbE2 S X L b σ T))

/-- **`term₂(η)`**. -/
noncomputable def sbTerm2 (eta S X U L b r σ T : ℝ) : ℝ :=
  eta * sbTerm2Coef S X b r σ T *
    (sbBB1 S X U b σ * Phi (eta * sbD3 S X U b σ T)
      - sbLambda2 b σ T * Phi (eta * sbD4 S X U b σ T)
      - sbBB2 S X L b σ * Phi (eta * sbE3 S X L b σ T)
      + sbLambda2 b σ T * Phi (eta * sbE4 S X L b σ T))

/-- **Soft-barrier knock-in value** `w(η) = (term₁(η) − term₂(η))/(U − L)`
(`AnalyticSoftBarrierEngine::knockInValue`). -/
noncomputable def softBarrierKnockIn (eta S X U L b r σ T : ℝ) : ℝ :=
  (sbTerm1 eta S X U L b r σ T - sbTerm2 eta S X U L b r σ T) / (U - L)

/-- **The algebraic core of the `η`-symmetry check**: at `η = ±1`, `η·C·(bracket)` differs by
exactly `C·(A₁ − A₂)` once every `Φ(η·)` pair is rewritten via `Phi_neg` — the `λ` contribution
cancels completely (`−Cλ·1 + Cλ·1 = 0`), independent of what `C, A₁, A₂, λ, d₁, d₂, e₁, e₂`
actually are. This is the reusable lemma both halves of `softBarrier_call_sub_put` instantiate. -/
theorem sb_eta_diff_helper (C A1 A2 lam d1 d2 e1 e2 : ℝ) :
    (1 : ℝ) * C * (A1 * Phi (1 * d1) - lam * Phi (1 * d2) - A2 * Phi (1 * e1) + lam * Phi (1 * e2))
      - (-1 : ℝ) * C *
        (A1 * Phi ((-1) * d1) - lam * Phi ((-1) * d2) - A2 * Phi ((-1) * e1)
          + lam * Phi ((-1) * e2))
      = C * (A1 - A2) := by
  simp only [one_mul, neg_one_mul, Phi_neg]
  ring

/-- **Call minus put, soft-barrier knock-in**: `w(1) − w(−1) = (C₁(A₁−A₂) − C₂(B₁−B₂))/(U−L)`,
with every `Φ`/bivariate term gone — a clean cross-check (see the module docstring) that `η` is
threaded consistently through both the outer sign and all eight `Φ` arguments. -/
theorem softBarrier_call_sub_put (S X U L b r σ T : ℝ) :
    softBarrierKnockIn 1 S X U L b r σ T - softBarrierKnockIn (-1) S X U L b r σ T
      = (sbTerm1Coef S X b r σ T * (sbA1 S X U b σ - sbA2 S X L b σ)
          - sbTerm2Coef S X b r σ T * (sbBB1 S X U b σ - sbBB2 S X L b σ)) / (U - L) := by
  unfold softBarrierKnockIn
  rw [div_sub_div_same]
  congr 1
  unfold sbTerm1 sbTerm2
  have h1 := sb_eta_diff_helper (sbTerm1Coef S X b r σ T) (sbA1 S X U b σ) (sbA2 S X L b σ)
    (sbLambda1 b σ T) (sbD1 S X U b σ T) (sbD2 S X U b σ T) (sbE1 S X L b σ T)
    (sbE2 S X L b σ T)
  have h2 := sb_eta_diff_helper (sbTerm2Coef S X b r σ T) (sbBB1 S X U b σ) (sbBB2 S X L b σ)
    (sbLambda2 b σ T) (sbD3 S X U b σ T) (sbD4 S X U b σ T) (sbE3 S X L b σ T)
    (sbE4 S X L b σ T)
  linear_combination h1 - h2

end MathFin
