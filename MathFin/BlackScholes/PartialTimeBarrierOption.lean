/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.BivariateNormalCDF

/-!
# Partial-time barrier options (start window, call): Haug's closed form

A barrier that is monitored only on part of the option's life. This file covers the **start**
window, **call** side (QuantLib's `PartialBarrier::Start`, `Option::Call`): the barrier is live
on `[0, t₁]` and switched off for the remainder `(t₁, T]` of the option's life (Haug, *The
Complete Guide to Option Pricing Formulas*, §"Partial-Time Barrier Options"). Unlike the binary
and soft barriers in this
batch, this genuinely needs the **bivariate** normal CDF — the barrier-monitoring window
`[0, t₁]` and the full life `[0, T]` are correlated (correlation `ρ = √(t₁/T)`, the two Brownian
increments share the `[0, t₁]` leg) — which is exactly why the coverage-map note placed #65
alongside #64 (Heynen–Kat) rather than with the two single-variable items #63/#66, and why this
file builds on the same `BivariateNormalCDF.lean` substrate (`bivariateNormalCDF`,
`bivariateNormalCDF_flip_snd`) as `HeynenKatTwoAssetBarrier.lean`.

**Scope, disclosed honestly**: QuantLib's `AnalyticPartialTimeBarrierOptionEngine` also prices
the **end**-window case (`PartialBarrier::EndB1`/`EndB2`, barrier live only on `(t₁, T]`) via
`CoB1`/`CoB2`, which are substantially more involved (each has its own strike-vs-barrier case
split with extra vanilla-minus-partial decompositions) and are genuinely harder — matching the
coverage-map's own assessment that "#64–65 ... need more substrate or are genuinely harder," this
file formalizes the **start**-window case (`CA`, QuantLib's simplest of the three) and leaves
`EndB1`/`EndB2` out of scope. **`CA` is also call-only**: QuantLib's `CA` is commented
`// Partial-Time-Start-OUT Call Option calculation`, and the engine prices a *put* in
`calculate()` via the put–call spot-reflection symmetry (strike `X ↦ S²/X`, barrier `H ↦ S²/H`,
barrier direction mirrored, the `CA`-call result on the transformed inputs scaled by `X/S`) rather
than a second closed form — that symmetry transform is not formalized here either. The knock-in
case (`CIA = vanilla − CA`) is, as elsewhere in this batch, QuantLib's own *definition* via
in–out parity rather than an independent closed form, so it is not separately formalized.

Transcribed from, and cross-checked against, QuantLib's
`ql/pricingengines/barrier/analyticpartialtimebarrieroptionengine.cpp` (`CA`, upstream commit
`5f4811e`, 2026-10-16; contributed 2014 by Polytech'Nice Sophia Antipolis). We adopt a single
constant volatility `σ` (QuantLib's engine reads a possibly term-structured Black vol evaluated
at `t₁` for `μ` and the `e`-terms and at `T` for the `d`/`f`-terms; Haug's original textbook
closed form, which this transcribes, uses one constant `σ` throughout — the flat-vol case
QuantLib's more general engine specializes to).

With cost-of-carry `b = r − q`, `ρ = √(t₁/T)`, `μ = (b − σ²/2)/σ²`, and

  `d₁ = (log(S/X) + (b+σ²/2)T)/(σ√T)`,  `d₂ = d₁ − σ√T`,
  `e₁ = (log(S/H) + (b+σ²/2)t₁)/(σ√t₁)`,  `e₂ = e₁ − σ√t₁`,
  `e₃ = e₁ + 2log(H/S)/(σ√t₁)`,  `e₄ = e₃ − σ√t₁`,
  `f₁ = (log(S/X) + 2log(H/S) + (b+σ²/2)T)/(σ√T)`,  `f₂ = f₁ − σ√T`,

and `(H/S)^{2μ}`, `(H/S)^{2(μ+1)}` as `exp(·log·)` (as in the other two files of this batch), the
start-window out-barrier **call** value (`η = 1` down, `η = −1` up) is

  `CA(η) = S·e^{(b−r)T}·(N₂(d₁, ηe₁; ηρ) − (H/S)^{2(μ+1)}·N₂(f₁, ηe₃; ηρ))`
         `− X·e^{−rT}·(N₂(d₂, ηe₂; ηρ) − (H/S)^{2μ}·N₂(f₂, ηe₄; ηρ))`.

## Main results

* `ptCA_down_add_up`: **`CA(1) + CA(−1)` collapses to a closed form with no bivariate CDF left**
  — every `N₂(a, ηb; ηρ)` pair (`η = ±1`) telescopes via `bivariateNormalCDF_flip_snd` to a
  single `Φ(a)`, exactly the mechanism behind `HeynenKatTwoAssetBarrier.lean`'s
  `heynenKat_downOut_add_upOut`. As there, the down/up window-start prices are mutually exclusive
  regimes (down-monitored vs. up-monitored), so the sum has no payoff-level meaning; it verifies
  the `(ηe_i, ηρ)` sign pattern is self-consistent across `η = ±1`, the same scope the Heynen–Kat
  file disclosed for its own analogous check.
-/

@[expose] public section

namespace MathFin

open Real

/-- **`ρ = √(t₁/T)`**, the correlation between the barrier-window and full-life log-returns. -/
noncomputable def ptRho (t1 T : ℝ) : ℝ := Real.sqrt (t1 / T)

/-- **`μ = (b − σ²/2)/σ²`**. -/
noncomputable def ptMu (b σ : ℝ) : ℝ := (b - σ ^ 2 / 2) / σ ^ 2

/-- **`d₁`**: the standard BS `d₁` against strike `X` over the full life `T`. -/
noncomputable def ptD1 (S X b σ T : ℝ) : ℝ :=
  (Real.log (S / X) + (b + σ ^ 2 / 2) * T) / (σ * Real.sqrt T)

/-- **`d₂` = `d₁ − σ√T`**. -/
noncomputable def ptD2 (S X b σ T : ℝ) : ℝ := ptD1 S X b σ T - σ * Real.sqrt T

/-- **`e₁`**: the "distance" of the barrier `H` over the monitoring window `t₁`. -/
noncomputable def ptE1 (S H b σ t1 : ℝ) : ℝ :=
  (Real.log (S / H) + (b + σ ^ 2 / 2) * t1) / (σ * Real.sqrt t1)

/-- **`e₂` = `e₁ − σ√t₁`**. -/
noncomputable def ptE2 (S H b σ t1 : ℝ) : ℝ := ptE1 S H b σ t1 - σ * Real.sqrt t1

/-- **`e₃`**: `e₁` shifted by the barrier reflection term. -/
noncomputable def ptE3 (S H b σ t1 : ℝ) : ℝ :=
  ptE1 S H b σ t1 + 2 * Real.log (H / S) / (σ * Real.sqrt t1)

/-- **`e₄` = `e₃ − σ√t₁`**. -/
noncomputable def ptE4 (S H b σ t1 : ℝ) : ℝ := ptE3 S H b σ t1 - σ * Real.sqrt t1

/-- **`f₁`**: `d₁` shifted by the barrier reflection term (over the full life `T`). -/
noncomputable def ptF1 (S X H b σ T : ℝ) : ℝ :=
  (Real.log (S / X) + 2 * Real.log (H / S) + (b + σ ^ 2 / 2) * T) / (σ * Real.sqrt T)

/-- **`f₂` = `f₁ − σ√T`**. -/
noncomputable def ptF2 (S X H b σ T : ℝ) : ℝ := ptF1 S X H b σ T - σ * Real.sqrt T

/-- **`(H/S)^{2μ}`**, written as `exp(·log·)`. -/
noncomputable def ptHSmu (S H b σ : ℝ) : ℝ := Real.exp (2 * ptMu b σ * Real.log (H / S))

/-- **`(H/S)^{2(μ+1)}`**. -/
noncomputable def ptHSmu1 (S H b σ : ℝ) : ℝ := Real.exp (2 * (ptMu b σ + 1) * Real.log (H / S))

/-- **Partial-time-start barrier call value** `CA(η)` (QuantLib's
`AnalyticPartialTimeBarrierOptionEngine::CA`; `η = 1` down, `η = −1` up; call-only — see the
module docstring's "Scope" paragraph for how QuantLib prices the put side instead). -/
noncomputable def ptCA (eta S X H b r σ t1 T : ℝ) : ℝ :=
  S * Real.exp ((b - r) * T) *
      (bivariateNormalCDF (ptD1 S X b σ T) (eta * ptE1 S H b σ t1) (eta * ptRho t1 T)
        - ptHSmu1 S H b σ *
            bivariateNormalCDF (ptF1 S X H b σ T) (eta * ptE3 S H b σ t1) (eta * ptRho t1 T))
    - X * Real.exp (-r * T) *
        (bivariateNormalCDF (ptD2 S X b σ T) (eta * ptE2 S H b σ t1) (eta * ptRho t1 T)
          - ptHSmu S H b σ *
              bivariateNormalCDF (ptF2 S X H b σ T) (eta * ptE4 S H b σ t1) (eta * ptRho t1 T))

/-- `ρ² ≤ 1` whenever `0 ≤ t₁ ≤ T` — the hypothesis `bivariateNormalCDF_flip_snd` needs, since
a monitoring window can only be a sub-interval of the option's life. -/
theorem ptRho_sq_le_one {t1 T : ℝ} (ht1 : 0 ≤ t1) (hT : t1 ≤ T) : ptRho t1 T ^ 2 ≤ 1 := by
  have hT0 : 0 ≤ T := ht1.trans hT
  rw [ptRho, Real.sq_sqrt (div_nonneg ht1 hT0)]
  rcases hT0.eq_or_lt with hT0' | hT0'
  · simp [← hT0']
  · exact (div_le_one hT0').mpr hT

/-- **Down-window plus up-window, same strike/barrier**: `CA(1) + CA(−1)` collapses to a closed
form with every bivariate CDF replaced by a single `Φ`, via `bivariateNormalCDF_flip_snd` applied
to each of the four `N₂` pairs (see the module docstring for the scope this checks). -/
theorem ptCA_down_add_up (S X H b r σ t1 T : ℝ) (ht1 : 0 ≤ t1) (hT : t1 ≤ T) :
    ptCA 1 S X H b r σ t1 T + ptCA (-1) S X H b r σ t1 T
      = S * Real.exp ((b - r) * T) *
          (Phi (ptD1 S X b σ T) - ptHSmu1 S H b σ * Phi (ptF1 S X H b σ T))
        - X * Real.exp (-r * T) *
            (Phi (ptD2 S X b σ T) - ptHSmu S H b σ * Phi (ptF2 S X H b σ T)) := by
  have hr : ptRho t1 T ^ 2 ≤ 1 := ptRho_sq_le_one ht1 hT
  have hd1 := bivariateNormalCDF_flip_snd (ptD1 S X b σ T) (ptE1 S H b σ t1) hr
  have hf1 := bivariateNormalCDF_flip_snd (ptF1 S X H b σ T) (ptE3 S H b σ t1) hr
  have hd2 := bivariateNormalCDF_flip_snd (ptD2 S X b σ T) (ptE2 S H b σ t1) hr
  have hf2 := bivariateNormalCDF_flip_snd (ptF2 S X H b σ T) (ptE4 S H b σ t1) hr
  simp only [ptCA, one_mul, neg_one_mul]
  linear_combination S * Real.exp ((b - r) * T) * hd1
    - S * Real.exp ((b - r) * T) * ptHSmu1 S H b σ * hf1
    - X * Real.exp (-r * T) * hd2 + X * Real.exp (-r * T) * ptHSmu S H b σ * hf2

end MathFin
