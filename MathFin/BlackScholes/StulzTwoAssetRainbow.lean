/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.BlackScholes.GarmanNormalForm
public import MathFin.Foundations.BivariateNormalCDF

/-!
# Stulz (1982): the exact two-asset rainbow (max/min) closed form

A call on `max(S¹_T, S²_T)` or `min(S¹_T, S²_T)` struck at `K` is **exactly** priced by a
pair of bivariate-normal-CDF closed forms (Stulz, *Options on the Minimum or the Maximum of
Two Risky Assets*, Journal of Financial Economics 10 (1982), 161–185) — genuinely distinct
from `BasketMomentMatching.lean`'s `n`-asset moment-matching *approximation*: this is an exact
closed form, but only for `n = 2`.

Transcribed from, and cross-checked against, the Rmetrics `fExoticOptions::TwoRiskyAssetsOption`
reference implementation (itself a transcription of Haug, *The Complete Guide to Option Pricing
Formulas*, §2.8.1) — no independent numerical verification was run, only a side-by-side formula
read. Uses the cost-of-carry convention `bᵢ` (`bᵢ = r` for a non-dividend asset,
`bᵢ = r - qᵢ` under a continuous yield `qᵢ`, `bᵢ = 0` for a futures-style asset). With

  `v = √(σ₁² + σ₂² − 2ρσ₁σ₂)`                          (`stulzEffVol`, the Margrabe spread vol)
  `ρ₁ = (σ₁ − ρσ₂) / v`, `ρ₂ = (σ₂ − ρσ₁) / v`          (`stulzRho1`, `stulzRho2`)
  `yᵢ = (log(Sᵢ/K) + (bᵢ + σᵢ²/2)T) / (σᵢ√T)`           (`stulzY1`, `stulzY2`)
  `d = (log(S¹/S²) + (b₁ − b₂ + v²/2)T) / (v√T)`         (`stulzD`)

the call-on-the-max and call-on-the-min prices are

  `C_max = S¹e^{(b₁−r)T} N₂(y₁, d; ρ₁) + S²e^{(b₂−r)T} N₂(y₂, −d+v√T; ρ₂)`
          `− Ke^{−rT}(1 − N₂(−y₁+σ₁√T, −y₂+σ₂√T; ρ))`,
  `C_min = S¹e^{(b₁−r)T} N₂(y₁, −d; −ρ₁) + S²e^{(b₂−r)T} N₂(y₂, d−v√T; −ρ₂)`
          `− Ke^{−rT} N₂(y₁−σ₁√T, y₂−σ₂√T; ρ)`.

## Main results

* `stulzRho1_sq_le_one`, `stulzRho2_sq_le_one`: `ρ₁, ρ₂` are genuine correlations (`ρᵢ² ≤ 1`)
  whenever `ρ² ≤ 1` — an algebraic fact, unconditional on `v ≠ 0` (Lean's `0/0 = 0` convention
  makes the degenerate `v = 0` case trivially satisfy it too).
* `stulz_max_min_payoff_parity`: the **payoff-level** identity behind Stulz's whole
  construction, `max(max(a,b)−K,0) + max(min(a,b)−K,0) = max(a−K,0) + max(b−K,0)` — pure
  algebra, no probability.
* `stulz_call_max_add_call_min`: the matching **price-level** identity, `C_max + C_min` equals
  the sum of two *ordinary* one-asset Black-Scholes calls on `S¹` and `S²` (via
  `GarmanNormalForm.bsVGarman`). This is exactly the payoff identity transported through
  pricing, and the proof consumes only `bivariateNormalCDF_flip_snd` /
  `bivariateNormalCDF_neg_neg` — the two general bivariate-CDF identities proved for this
  purpose in `BivariateNormalCDF.lean` — with no separate probabilistic derivation.

**Scope, disclosed honestly**: `stulz_call_max_add_call_min` verifies the closed form's
*internal consistency* (it collapses to the one-asset case exactly as Stulz's own derivation
requires), not a from-first-principles derivation from a joint two-GBM model — the same scope
as `GarmanNormalForm.lean`'s own specializations, which take the one-asset BS closed form as
given rather than re-deriving it from Girsanov. Deriving `C_max` itself from a bivariate
lognormal expectation is a separate, harder project (the two-asset analogue of
`MargrabeGrounding.lean`).
-/

@[expose] public section

namespace MathFin

open Real

/-- **Effective spread volatility** `v = √(σ₁² + σ₂² − 2ρσ₁σ₂)` — the same quantity as the
Margrabe effective vol (`margrabe_effective_variance`'s square root). -/
noncomputable def stulzEffVol (σ1 σ2 ρ : ℝ) : ℝ :=
  √(σ1 ^ 2 + σ2 ^ 2 - 2 * ρ * σ1 * σ2)

/-- **Correlation of `Y₁ = log S¹` with the log-spread**: `ρ₁ = (σ₁ − ρσ₂) / v`. -/
noncomputable def stulzRho1 (σ1 σ2 ρ : ℝ) : ℝ :=
  (σ1 - ρ * σ2) / stulzEffVol σ1 σ2 ρ

/-- **Correlation of `Y₂ = log S²` with the log-spread**: `ρ₂ = (σ₂ − ρσ₁) / v`. -/
noncomputable def stulzRho2 (σ1 σ2 ρ : ℝ) : ℝ :=
  (σ2 - ρ * σ1) / stulzEffVol σ1 σ2 ρ

/-- **`y₁`**: the standard BS `d₁` of asset 1 against strike `K` at cost-of-carry `b₁`. -/
noncomputable def stulzY1 (S1 K b1 σ1 T : ℝ) : ℝ :=
  (Real.log (S1 / K) + (b1 + σ1 ^ 2 / 2) * T) / (σ1 * Real.sqrt T)

/-- **`y₂`**: the standard BS `d₁` of asset 2 against strike `K` at cost-of-carry `b₂`. -/
noncomputable def stulzY2 (S2 K b2 σ2 T : ℝ) : ℝ :=
  (Real.log (S2 / K) + (b2 + σ2 ^ 2 / 2) * T) / (σ2 * Real.sqrt T)

/-- **`d`**: the Margrabe-style `d₁` of the ratio `S¹/S²` at the effective spread vol `v`. -/
noncomputable def stulzD (S1 S2 b1 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  (Real.log (S1 / S2) + (b1 - b2 + stulzEffVol σ1 σ2 ρ ^ 2 / 2) * T) /
    (stulzEffVol σ1 σ2 ρ * Real.sqrt T)

/-- **Stulz's call on the maximum of two assets**, `𝔼[e^{−rT}max(max(S¹_T,S²_T)−K,0)]`. -/
noncomputable def stulzCallMax (S1 S2 K r b1 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  let v := stulzEffVol σ1 σ2 ρ
  let ρ1 := stulzRho1 σ1 σ2 ρ
  let ρ2 := stulzRho2 σ1 σ2 ρ
  let y1 := stulzY1 S1 K b1 σ1 T
  let y2 := stulzY2 S2 K b2 σ2 T
  let d := stulzD S1 S2 b1 b2 σ1 σ2 ρ T
  S1 * Real.exp ((b1 - r) * T) * bivariateNormalCDF y1 d ρ1 +
    S2 * Real.exp ((b2 - r) * T) * bivariateNormalCDF y2 (-d + v * Real.sqrt T) ρ2 -
    K * Real.exp (-(r * T)) *
      (1 - bivariateNormalCDF (-y1 + σ1 * Real.sqrt T) (-y2 + σ2 * Real.sqrt T) ρ)

/-- **Stulz's call on the minimum of two assets**, `𝔼[e^{−rT}max(min(S¹_T,S²_T)−K,0)]`. -/
noncomputable def stulzCallMin (S1 S2 K r b1 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  let v := stulzEffVol σ1 σ2 ρ
  let ρ1 := stulzRho1 σ1 σ2 ρ
  let ρ2 := stulzRho2 σ1 σ2 ρ
  let y1 := stulzY1 S1 K b1 σ1 T
  let y2 := stulzY2 S2 K b2 σ2 T
  let d := stulzD S1 S2 b1 b2 σ1 σ2 ρ T
  S1 * Real.exp ((b1 - r) * T) * bivariateNormalCDF y1 (-d) (-ρ1) +
    S2 * Real.exp ((b2 - r) * T) * bivariateNormalCDF y2 (d - v * Real.sqrt T) (-ρ2) -
    K * Real.exp (-(r * T)) *
      bivariateNormalCDF (y1 - σ1 * Real.sqrt T) (y2 - σ2 * Real.sqrt T) ρ

/-! ## `ρ₁`, `ρ₂` are genuine correlations -/

/-- **`ρ₁` is a genuine correlation**: `ρ₁² ≤ 1` whenever `ρ² ≤ 1`. Unconditional on
`v = stulzEffVol σ1 σ2 ρ ≠ 0`: at `v = 0`, `ρ1 = (σ1 - ρσ2) / 0 = 0` by Lean's division
convention, and `0 ≤ 1` trivially. -/
theorem stulzRho1_sq_le_one (σ1 σ2 ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) : stulzRho1 σ1 σ2 ρ ^ 2 ≤ 1 := by
  unfold stulzRho1 stulzEffVol
  have hnonneg : 0 ≤ σ1 ^ 2 + σ2 ^ 2 - 2 * ρ * σ1 * σ2 := by
    nlinarith [sq_nonneg (σ1 - ρ * σ2), mul_nonneg (sq_nonneg σ2) (sub_nonneg.2 hρ)]
  rcases hnonneg.lt_or_eq with hpos | heq
  · rw [div_pow, Real.sq_sqrt hpos.le, div_le_one hpos]
    nlinarith [mul_nonneg (sq_nonneg σ2) (sub_nonneg.2 hρ)]
  · rw [← heq, Real.sqrt_zero, div_zero]
    norm_num

/-- **`ρ₂` is a genuine correlation**: `ρ₂² ≤ 1` whenever `ρ² ≤ 1`, by the same argument as
`stulzRho1_sq_le_one` with `σ1, σ2` exchanged. -/
theorem stulzRho2_sq_le_one (σ1 σ2 ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) : stulzRho2 σ1 σ2 ρ ^ 2 ≤ 1 := by
  have h := stulzRho1_sq_le_one σ2 σ1 ρ hρ
  unfold stulzRho1 stulzEffVol at h
  unfold stulzRho2 stulzEffVol
  rwa [show σ2 ^ 2 + σ1 ^ 2 - 2 * ρ * σ2 * σ1 = σ1 ^ 2 + σ2 ^ 2 - 2 * ρ * σ1 * σ2 from by ring]
    at h

/-! ## The payoff-level parity -/

/-- **The payoff identity behind Stulz's construction**: a call on the max plus a call on the
min, both struck at `K`, pays exactly what a plain call on `a` plus a plain call on `b` pays.
Pure algebra — `rcases le_total a b` collapses `max`/`min` on each side identically. -/
theorem stulz_max_min_payoff_parity (a b K : ℝ) :
    max (max a b - K) 0 + max (min a b - K) 0 = max (a - K) 0 + max (b - K) 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h]; ring
  · rw [max_eq_left h, min_eq_right h]

/-! ## The price-level parity -/

/-- **Log-algebra bridge**: `stulzY1` matches `GarmanNormalForm`'s `gbsd1` at the cost-of-carry
parameters `A = S¹e^{(b₁−r)T}`, `DF = e^{−rT}`. Reuses `log_SexpNegQ_div_KexpNegR` (with
`q = r − b₁`, since `e^{(b₁-r)T} = e^{-((r-b₁)T)}`) rather than re-deriving the log algebra. -/
private lemma stulzY1_eq_gbsd1 (S1 K b1 σ1 T r : ℝ) (hS1 : 0 < S1) (hK : 0 < K) :
    stulzY1 S1 K b1 σ1 T =
      gbsd1 (S1 * Real.exp ((b1 - r) * T)) K (Real.exp (-(r * T))) σ1 T := by
  unfold stulzY1 gbsd1
  congr 1
  rw [show S1 * Real.exp ((b1 - r) * T) = S1 * Real.exp (-((r - b1) * T)) from by ring_nf,
    log_SexpNegQ_div_KexpNegR S1 K r (r - b1) T hS1 hK]
  ring

/-- **Log-algebra bridge** for `stulzY2`, symmetric to `stulzY1_eq_gbsd1`. -/
private lemma stulzY2_eq_gbsd1 (S2 K b2 σ2 T r : ℝ) (hS2 : 0 < S2) (hK : 0 < K) :
    stulzY2 S2 K b2 σ2 T =
      gbsd1 (S2 * Real.exp ((b2 - r) * T)) K (Real.exp (-(r * T))) σ2 T := by
  unfold stulzY2 gbsd1
  congr 1
  rw [show S2 * Real.exp ((b2 - r) * T) = S2 * Real.exp (-((r - b2) * T)) from by ring_nf,
    log_SexpNegQ_div_KexpNegR S2 K r (r - b2) T hS2 hK]
  ring

/-- **The price-level parity**: `C_max + C_min` equals the sum of two one-asset `bsVGarman`
calls on `S¹` and `S²` at strike `K`, discount factor `e^{−rT}`. The proof pairs each `N₂` term
of `C_max` with its counterpart in `C_min` via `bivariateNormalCDF_flip_snd` (asset terms) and
`bivariateNormalCDF_neg_neg` (the strike term) — exactly the algebraic content of
`stulz_max_min_payoff_parity`, transported through the pricing formula. -/
theorem stulz_call_max_add_call_min (S1 S2 K r b1 b2 σ1 σ2 T : ℝ) {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1)
    (hS1 : 0 < S1) (hS2 : 0 < S2) (hK : 0 < K) :
    stulzCallMax S1 S2 K r b1 b2 σ1 σ2 ρ T + stulzCallMin S1 S2 K r b1 b2 σ1 σ2 ρ T =
      bsVGarman (S1 * Real.exp ((b1 - r) * T)) K (Real.exp (-(r * T))) σ1 T +
        bsVGarman (S2 * Real.exp ((b2 - r) * T)) K (Real.exp (-(r * T))) σ2 T := by
  have hρ1sq := stulzRho1_sq_le_one σ1 σ2 ρ hρ
  have hρ2sq := stulzRho2_sq_le_one σ1 σ2 ρ hρ
  -- Abbreviations matching the `let`-bindings inside `stulzCallMax`/`stulzCallMin`.
  set v := stulzEffVol σ1 σ2 ρ
  set ρ1 := stulzRho1 σ1 σ2 ρ
  set ρ2 := stulzRho2 σ1 σ2 ρ
  set y1 := stulzY1 S1 K b1 σ1 T
  set y2 := stulzY2 S2 K b2 σ2 T
  set d := stulzD S1 S2 b1 b2 σ1 σ2 ρ T
  -- The three bivariate-CDF identities that collapse `C_max + C_min` term by term.
  have hasset1 : bivariateNormalCDF y1 d ρ1 + bivariateNormalCDF y1 (-d) (-ρ1) = Phi y1 :=
    bivariateNormalCDF_flip_snd y1 d hρ1sq
  have hasset2 : bivariateNormalCDF y2 (-d + v * Real.sqrt T) ρ2 +
      bivariateNormalCDF y2 (d - v * Real.sqrt T) (-ρ2) = Phi y2 := by
    have h2 := bivariateNormalCDF_flip_snd y2 (-d + v * Real.sqrt T) hρ2sq
    rwa [show -(-d + v * Real.sqrt T) = d - v * Real.sqrt T from by ring] at h2
  have hstrike : (1 - bivariateNormalCDF (-y1 + σ1 * Real.sqrt T) (-y2 + σ2 * Real.sqrt T) ρ) +
      bivariateNormalCDF (y1 - σ1 * Real.sqrt T) (y2 - σ2 * Real.sqrt T) ρ =
      Phi (y1 - σ1 * Real.sqrt T) + Phi (y2 - σ2 * Real.sqrt T) := by
    have hnn := bivariateNormalCDF_neg_neg (y1 - σ1 * Real.sqrt T) (y2 - σ2 * Real.sqrt T) hρ
    rw [show -(y1 - σ1 * Real.sqrt T) = -y1 + σ1 * Real.sqrt T from by ring,
      show -(y2 - σ2 * Real.sqrt T) = -y2 + σ2 * Real.sqrt T from by ring] at hnn
    linarith
  -- The `gbsd1` bridge, so `bsVGarman`'s own `d₁` matches `y1`/`y2` exactly.
  have hgbsd1 : gbsd1 (S1 * Real.exp ((b1 - r) * T)) K (Real.exp (-(r * T))) σ1 T = y1 :=
    (stulzY1_eq_gbsd1 S1 K b1 σ1 T r hS1 hK).symm
  have hgbsd2 : gbsd1 (S2 * Real.exp ((b2 - r) * T)) K (Real.exp (-(r * T))) σ2 T = y2 :=
    (stulzY2_eq_gbsd1 S2 K b2 σ2 T r hS2 hK).symm
  simp only [stulzCallMax, stulzCallMin, bsVGarman, gbsd2, hgbsd1, hgbsd2]
  linear_combination (S1 * Real.exp ((b1 - r) * T)) * hasset1 +
    (S2 * Real.exp ((b2 - r) * T)) * hasset2 - (K * Real.exp (-(r * T))) * hstrike

end MathFin
