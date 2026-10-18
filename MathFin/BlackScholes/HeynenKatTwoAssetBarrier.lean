/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.BivariateNormalCDF

/-!
# Heynen & Kat two-asset barrier option: the exact closed form

A barrier option on asset 1, struck at `X`, but **knocked out by asset 2** crossing a barrier
`H` (Heynen & Kat; Haug, *The Complete Guide to Option Pricing Formulas*, §"Exotic Options on
Two Assets"). Needs the bivariate normal CDF (same substrate as `StulzTwoAssetRainbow.lean`).

Transcribed from, and cross-checked against, QuantLib's
`ql/pricingengines/barrier/analytictwoassetbarrierengine.cpp` (`AnalyticTwoAssetBarrierEngine`,
upstream commit `5f4811e`, 2026-10-16 — its own header cites Haug and states the engine "was
checked against... the formulas in the reference books" as its own validation). An independently
fetched transcription of the same formula in Rmetrics' `fExoticOptions::TwoAssetBarrierOption`
(itself ported from Haug) agrees on every term **except** one `d₁` sub-expression, where the
QuantLib C++ source is unambiguous (`mu(b1,σ1) + σ1*σ1`, i.e. drift `b1 + σ1²/2`, the standard
BS `d₁` convention) and was taken as authoritative over the possibly-garbled Rmetrics extract.

With `μ(b, σ) = b − σ²/2` (`hkMu`) and, for asset 1 against strike `X` and asset 2 against
barrier `H`,

  `d₁ = (log(S₁/X) + (μ(b₁,σ₁) + σ₁²)T) / (σ₁√T)`,  `d₂ = d₁ − σ₁√T`,
  `d₃ = d₁ + 2ρ·log(H/S₂)/(σ₂√T)`,  `d₄ = d₂ + 2ρ·log(H/S₂)/(σ₂√T)`,
  `e₁ = (log(H/S₂) − (μ(b₂,σ₂) + ρσ₁σ₂)T) / (σ₂√T)`,  `e₂ = e₁ + ρσ₁√T`,
  `e₃ = e₁ − 2·log(H/S₂)/(σ₂√T)`,  `e₄ = e₂ − 2·log(H/S₂)/(σ₂√T)`,

the knock-out value (`heynenKatA`, QuantLib's `A(η, φ)`; `η = 1` call / `η = -1` put, `φ = -1`
down / `φ = 1` up) is

  `A(η,φ) = ηS₁e^{(b₁−r)T}(N₂(ηd₁,φe₁;−ηφρ) − e^{2(μ(b₂,σ₂)+ρσ₁σ₂)log(H/S₂)/σ₂²}N₂(ηd₃,φe₃;−ηφρ))`
          `− ηXe^{−rT}(N₂(ηd₂,φe₂;−ηφρ) − e^{2μ(b₂,σ₂)log(H/S₂)/σ₂²}N₂(ηd₄,φe₄;−ηφρ))`,

and the four knock-out prices are `A(1,-1)` (down-out call), `A(1,1)` (up-out call),
`A(-1,-1)` (down-out put), `A(-1,1)` (up-out put) — QuantLib's own `B(η,φ) ≡ 0` for this engine,
so `A` alone is the whole knock-out value.

## Main results

* `heynenKat_downOut_add_upOut`: **the down-out and up-out knock-out values, same option type,
  sum to a closed form with NO bivariate CDF left** — every `N₂(ηdᵢ, φeᵢ; −ηφρ)` pair (`φ = ±1`)
  collapses via `bivariateNormalCDF_flip_snd` to a single `Φ(ηdᵢ)`, exactly the two-asset-barrier
  analogue of `StulzTwoAssetRainbow.lean`'s `stulz_call_max_add_call_min`. This is a genuine
  structural consistency check on the transcription: both exponential-correction terms and both
  strike/asset legs collapse independently and simultaneously.

**Scope, disclosed honestly**: as with `StulzTwoAssetRainbow.lean`, this transcribes and checks
the *closed form*'s internal consistency; it does not re-derive the formula from a joint
two-GBM reflection-principle argument (a separate, substantially harder project — the two-asset
analogue of the barrier reflection argument behind `BlackScholes/BarrierParity.lean`). The
knock-in prices (`vanilla − knock-out`, standard in/out parity) are not separately formalized
here: that parity is the *definition* used in practice (as in QuantLib's own `DownIn`/`UpIn`
cases), not an independent theorem, so stating it would be circular without the vanilla
single-asset closed form's own from-first-principles derivation as a separate input.
-/

@[expose] public section

namespace MathFin

open Real

/-- **Risk-neutral log-drift** `μ(b, σ) = b − σ²/2`. -/
noncomputable def hkMu (b σ : ℝ) : ℝ := b - σ ^ 2 / 2

/-- **`d₁`**: the standard BS `d₁` of asset 1 against strike `X` at cost-of-carry `b₁`. -/
noncomputable def hkD1 (S1 X b1 σ1 T : ℝ) : ℝ :=
  (Real.log (S1 / X) + (hkMu b1 σ1 + σ1 ^ 2) * T) / (σ1 * Real.sqrt T)

/-- **`d₂` = `d₁ − σ₁√T`**. -/
noncomputable def hkD2 (S1 X b1 σ1 T : ℝ) : ℝ :=
  hkD1 S1 X b1 σ1 T - σ1 * Real.sqrt T

/-- **`d₃`**: `d₁` shifted by the asset-2/barrier correlation term. -/
noncomputable def hkD3 (S1 X H S2 b1 σ1 σ2 ρ T : ℝ) : ℝ :=
  hkD1 S1 X b1 σ1 T + 2 * ρ * Real.log (H / S2) / (σ2 * Real.sqrt T)

/-- **`d₄`**: `d₂` shifted by the same correlation term as `d₃`. -/
noncomputable def hkD4 (S1 X H S2 b1 σ1 σ2 ρ T : ℝ) : ℝ :=
  hkD2 S1 X b1 σ1 T + 2 * ρ * Real.log (H / S2) / (σ2 * Real.sqrt T)

/-- **`e₁`**: the "distance" of the barrier `H` from asset 2, at cost-of-carry `b₂`, correlation
`ρ` to asset 1. -/
noncomputable def hkE1 (H S2 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  (Real.log (H / S2) - (hkMu b2 σ2 + ρ * σ1 * σ2) * T) / (σ2 * Real.sqrt T)

/-- **`e₂` = `e₁ + ρσ₁√T`**. -/
noncomputable def hkE2 (H S2 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  hkE1 H S2 b2 σ1 σ2 ρ T + ρ * σ1 * Real.sqrt T

/-- **`e₃`**: `e₁` shifted by the barrier reflection term. -/
noncomputable def hkE3 (H S2 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  hkE1 H S2 b2 σ1 σ2 ρ T - 2 * Real.log (H / S2) / (σ2 * Real.sqrt T)

/-- **`e₄`**: `e₂` shifted by the same barrier reflection term as `e₃`. -/
noncomputable def hkE4 (H S2 b2 σ1 σ2 ρ T : ℝ) : ℝ :=
  hkE2 H S2 b2 σ1 σ2 ρ T - 2 * Real.log (H / S2) / (σ2 * Real.sqrt T)

/-- **Heynen & Kat's knock-out value `A(η, φ)`** (QuantLib's `AnalyticTwoAssetBarrierEngine::A`).
`η = 1` is a call on asset 1, `η = -1` a put; `φ = -1` is a down-barrier (on asset 2), `φ = 1` an
up-barrier. The four knock-out prices are `A(1,-1)`, `A(1,1)`, `A(-1,-1)`, `A(-1,1)`. -/
noncomputable def heynenKatA (eta phi S1 S2 X H T r b1 b2 σ1 σ2 ρ : ℝ) : ℝ :=
  let d1 := hkD1 S1 X b1 σ1 T
  let d2 := hkD2 S1 X b1 σ1 T
  let d3 := hkD3 S1 X H S2 b1 σ1 σ2 ρ T
  let d4 := hkD4 S1 X H S2 b1 σ1 σ2 ρ T
  let e1 := hkE1 H S2 b2 σ1 σ2 ρ T
  let e2 := hkE2 H S2 b2 σ1 σ2 ρ T
  let e3 := hkE3 H S2 b2 σ1 σ2 ρ T
  let e4 := hkE4 H S2 b2 σ1 σ2 ρ T
  let mu2 := hkMu b2 σ2
  eta * S1 * Real.exp ((b1 - r) * T) *
      (bivariateNormalCDF (eta * d1) (phi * e1) (-eta * phi * ρ) -
        Real.exp (2 * (mu2 + ρ * σ1 * σ2) * Real.log (H / S2) / σ2 ^ 2) *
          bivariateNormalCDF (eta * d3) (phi * e3) (-eta * phi * ρ)) -
    eta * X * Real.exp (-(r * T)) *
      (bivariateNormalCDF (eta * d2) (phi * e2) (-eta * phi * ρ) -
        Real.exp (2 * mu2 * Real.log (H / S2) / σ2 ^ 2) *
          bivariateNormalCDF (eta * d4) (phi * e4) (-eta * phi * ρ))

/-- **Down-out and up-out collapse to a bivariate-CDF-free form.** For a fixed option type
`η ∈ {-1,1}`, summing the down-barrier (`φ=-1`) and up-barrier (`φ=1`) knock-out values pairs
every `N₂(ηdᵢ,φeᵢ;−ηφρ)` with its `φ`-flipped partner via `bivariateNormalCDF_flip_snd`
(`N₂(a,b;r)+N₂(a,-b;-r)=Φ(a)`, applied at `a = ηdᵢ`, `b = eᵢ`, `r = -ηρ`), collapsing all four
`N₂` pairs to `Φ(ηd₁), Φ(ηd₂), Φ(ηd₃), Φ(ηd₄)` simultaneously. A genuine structural consistency
check on the transcription, in the spirit of `stulz_call_max_add_call_min`. -/
theorem heynenKat_downOut_add_upOut (S1 S2 X H T r b1 b2 σ1 σ2 : ℝ) {eta ρ : ℝ}
    (heta : eta ^ 2 = 1) (hρ : ρ ^ 2 ≤ 1) :
    heynenKatA eta (-1) S1 S2 X H T r b1 b2 σ1 σ2 ρ +
        heynenKatA eta 1 S1 S2 X H T r b1 b2 σ1 σ2 ρ =
      eta * S1 * Real.exp ((b1 - r) * T) *
          (Phi (eta * hkD1 S1 X b1 σ1 T) -
            Real.exp (2 * (hkMu b2 σ2 + ρ * σ1 * σ2) * Real.log (H / S2) / σ2 ^ 2) *
              Phi (eta * hkD3 S1 X H S2 b1 σ1 σ2 ρ T)) -
        eta * X * Real.exp (-(r * T)) *
          (Phi (eta * hkD2 S1 X b1 σ1 T) -
            Real.exp (2 * hkMu b2 σ2 * Real.log (H / S2) / σ2 ^ 2) *
              Phi (eta * hkD4 S1 X H S2 b1 σ1 σ2 ρ T)) := by
  have heρ : (-(eta * ρ)) ^ 2 ≤ 1 := by
    rw [neg_sq, mul_pow, heta, one_mul]; exact hρ
  set d1 := hkD1 S1 X b1 σ1 T with hd1
  set d2 := hkD2 S1 X b1 σ1 T with hd2
  set d3 := hkD3 S1 X H S2 b1 σ1 σ2 ρ T with hd3
  set d4 := hkD4 S1 X H S2 b1 σ1 σ2 ρ T with hd4
  set e1 := hkE1 H S2 b2 σ1 σ2 ρ T with he1
  set e2 := hkE2 H S2 b2 σ1 σ2 ρ T with he2
  set e3 := hkE3 H S2 b2 σ1 σ2 ρ T with he3
  set e4 := hkE4 H S2 b2 σ1 σ2 ρ T with he4
  have h1 := bivariateNormalCDF_flip_snd (eta * d1) e1 heρ
  have h2 := bivariateNormalCDF_flip_snd (eta * d2) e2 heρ
  have h3 := bivariateNormalCDF_flip_snd (eta * d3) e3 heρ
  have h4 := bivariateNormalCDF_flip_snd (eta * d4) e4 heρ
  simp only [neg_neg] at h1 h2 h3 h4
  -- Unfolding `heynenKatA` at the literal `phi := 1 / -1` substitutes `1 * e_i`, `-1 * e_i`,
  -- `-eta * 1 * ρ`, `-eta * (-1) * ρ` for the bivariate-CDF arguments: these are only RING-equal
  -- (not defeq) to the clean `e_i` / `-e_i` / `-(eta * ρ)` / `eta * ρ` forms in `h1`-`h4`, so the
  -- explicit `← hd_i`/`← he_i` fold-back and sign-normalizing lemmas below are needed before
  -- `linear_combination`'s atom matching can see the two sides as the same bivariate-CDF calls.
  simp only [heynenKatA, ← hd1, ← he1, neg_mul, one_mul, mul_neg, mul_one, neg_neg, hkMu, ← hd3,
    ← he3, ← hd2, ← he2, ← hd4, ← he4]
  linear_combination (eta * S1 * Real.exp ((b1 - r) * T)) * h1 +
    (-(eta * X * Real.exp (-(r * T)))) * h2 +
    (-(eta * S1 * Real.exp ((b1 - r) * T) *
        Real.exp (2 * (b2 - σ2 ^ 2 / 2 + ρ * σ1 * σ2) * Real.log (H / S2) / σ2 ^ 2))) * h3 +
    (eta * X * Real.exp (-(r * T)) *
        Real.exp (2 * (b2 - σ2 ^ 2 / 2) * Real.log (H / S2) / σ2 ^ 2)) * h4

end MathFin
