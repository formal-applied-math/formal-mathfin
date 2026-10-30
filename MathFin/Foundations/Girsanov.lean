/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.GirsanovConstantTheta

/-!
# Continuous-time Girsanov for Black–Scholes — the EMM as an explicit change of measure

The equivalent martingale measure of the Black–Scholes model, **constructed** as a
Girsanov density change of the physical measure — not recognised after the fact. Under
the physical measure `P` the stock has drift `μ`,
`S_t = S_0 · exp((μ − σ²/2)t + σ X_t)`, so the discounted price is
`D_t = e^{−rt} S_t = S_0 · exp((μ − r − σ²/2)t + σ X_t)`, a `P`-submartingale (drift
`μ − r ≠ 0`). Tilting by the **Girsanov density** with constant market price of risk
`θ = (μ − r)/σ`,

  `Z_t = exp(−θ X_t − ½θ² t)`   (the Wald exponential at `α = −θ`),
  `Q = P.withDensity Z_T`,

turns the discounted price into a `Q`-**martingale** on `[0, T]`: `Q` is the EMM.

The proof is one line of algebra on top of the constant-θ Girsanov theorem. Since
`μ − r = σθ`, the discounted price is `S_0` times the exponential `Q`-martingale of the
drift-corrected process `B^θ_t = X_t + θt` at `a = σ`:

  `(μ − r − σ²/2)t + σX_t = σ(X_t + θt) − ½σ²t`,

and `expBtheta_isQMartingale` (`GirsanovConstantTheta`) is that exponential's martingale
property under the same `Q`. The constant `S_0` comes out of both integrals.

This wires the **I ↔ II seam** (pricing ↔ Itô/Brownian tower) on the martingale side:
the risk-neutral measure is an explicit density change of the physical one, retiring the
Wald shortcut of `discountedGBM_isMartingale` (which took `Q = P` from the start). The
*distributional* Girsanov (the drift-corrected `B^θ_t = B_t + ∫₀ᵗ θ_s ds` is a `Q`-Brownian
motion, `gir-thm-9.1.8`) is strictly stronger: `GirsanovConstantTheta` for constant `θ`,
`GirsanovAdaptedTheta` for bounded continuous adapted `θ`, and `GirsanovPredictableTheta`
for bounded predictable `θ`.

## Main result

* `MathFin.bs_discounted_isQMartingale`
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- **Black–Scholes EMM via Girsanov.** With physical drift `μ`, rate `r`, volatility
`σ ≠ 0`, and market price of risk `θ = (μ − r)/σ`, the discounted stock price
`D_t = S_0 · exp((μ − r − σ²/2)t + σ X_t)` is a martingale on `[0, T]` under the tilted
measure `Q = P.withDensity (exp(−θ X_T − ½θ² T))`: for `s ≤ t ≤ T` and `A ∈ 𝓕_s`, the
`Q`-integrals of `D_t` and `D_s` over `A` agree. `Q` is the equivalent martingale measure,
exhibited as an explicit Girsanov change of measure. It is `S_0` times
`expBtheta_isQMartingale` at `a = σ`. -/
theorem bs_discounted_isQMartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [IsFilteredPreBrownian X 𝓕 P]
    (S_0 r μ σ : ℝ) (hσ : σ ≠ 0) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, (S_0 * Real.exp ((μ - r - σ ^ 2 / 2) * (t : ℝ) + σ * X t ω))
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal
          (Real.exp (-((μ - r) / σ) * X T ω - ((μ - r) / σ) ^ 2 * (T : ℝ) / 2)))
      = ∫ ω in A, (S_0 * Real.exp ((μ - r - σ ^ 2 / 2) * (s : ℝ) + σ * X s ω))
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal
          (Real.exp (-((μ - r) / σ) * X T ω - ((μ - r) / σ) ^ 2 * (T : ℝ) / 2))) := by
  have hD (u : ℝ≥0) (ω : Ω) : (μ - r - σ ^ 2 / 2) * (u : ℝ) + σ * X u ω
      = σ * (X u ω + (μ - r) / σ * (u : ℝ)) - σ ^ 2 * (u : ℝ) / 2 := by
    field_simp
    ring
  simp only [hD, integral_const_mul]
  rw [expBtheta_isQMartingale ((μ - r) / σ) σ T hst htT hA]

end MathFin
