/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Connectors: the American value is the Snell envelope of a market's price

The finite binomial American price is the Snell envelope of the discounted intrinsic value under the
risk-neutral coin flips, and in the Black–Scholes market the American put value dominates the
European put price.
-/

open MathFin MathFin.Contracts MeasureTheory
open scoped NNReal

/-- **The binomial American price is the Snell envelope** (general `snellEnvelope`, Mathlib's
conditional expectation on the flip filtration) of the discounted intrinsic value along the spot
path, under the risk-neutral coin flips, at time `0`. -/
theorem MathFinFrontier.americanPrice_eq_snellEnvelope {u d ρ : ℝ} (hna : BinomialNoArb u d ρ)
    {q : ℝ≥0} (hq : q ≤ 1) (hqcrr : crrUpProb u d ρ = q) (g : ℝ → ℝ) (S₀ : ℝ) (N : ℕ) :
    ∀ᵐ ω ∂coinFlipMeasure q hq,
      snellEnvelope (coinFlipMeasure q hq) flipFiltration Set.univ
        (fun n ω ↦ Real.exp (-ρ * n) * g (spotPath S₀ u d n ω)) N 0 ω = americanPrice u d ρ g N S₀ := by
  sorry

/-- **The American put value dominates the Black–Scholes price of the European put.** At the
Girsanov pricing measure of `θ = (m − r)/σ`, whose drift-corrected process `B^θ` is the Brownian
motion driving the risk-neutral asset, the European put's price in `BlackScholes.market` is at
most the American put value (no dividends) over stopping rules bounded by `T`. -/
theorem MathFinFrontier.price_europeanPut_le_americanPutValue {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hW : ProbabilityTheory.IsPreBrownianReal W μ) (hWmeas : ∀ t, Measurable (W t))
    {S_0 m r σ K : ℝ} {T H : ℝ≥0} (hTH : T ≤ H)
    (hB : Measurable (MathFin.Contracts.BlackScholes.constBtheta (μ := μ) hWmeas ((m - r) / σ) H).uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S_0) :
    (MathFin.Contracts.BlackScholes.market μ hWmeas S_0 m r σ).price
        (MathFin.Contracts.BlackScholes.constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (europeanPut K T) ≤
      MathFin.BlackScholes.AmericanPut.Stopping.americanPutValue
        (MathFin.Contracts.BlackScholes.constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (ItoIntegralL2.natFiltration hWmeas)
        (MathFin.Contracts.BlackScholes.constBtheta (μ := μ) hWmeas ((m - r) / σ) H) K r 0 σ S_0 T := by
  sorry
