/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.Binomial.American
public import MathFin.Models.Binomial.Market
public import MathFin.Pricing.AmericanPrice
public import MathFin.Probability.Martingales.GridStopping
public import MathFin.Probability.Discrete.DiscreteStoppingValue

/-!
# The binomial American price is the market's American price

The binomial market (`Models/Binomial/Market.lean`) is a `Market` in continuous time whose
information, spot and money market change only at the dates `n h`. Its American price of the put,
`Market.americanPrice` of the exercise right `europeanPutPayoff K` under the risk-neutral coin
flips, is the binomial American put price `americanPrice u d ρ g N S₀` of the Bellman recursion,
with `N = ⌊T / h⌋₊`. Three identities chain:

* the deflated exercise value of the put is the discounted put payoff `e^{−ρ n} (K − Sₙ)⁺` read on
  the grid (`exerciseValue_market_europeanPutPayoff`);
* stopping on the grid is discrete stopping (`stoppingValue_comp_floorDiv`);
* the discrete stopping value is the expectation of the Snell envelope at `0` (Snell's theorem,
  `snellEnvelope_optimalStopping`), which is almost surely the Bellman price
  (`americanPrice_eq_snellEnvelope`).

So the tree's backward recursion computes the supremum, over all stopping rules of the market, of
the expected deflated exercise value: the optimal stopping problem, not only the recursion.

## Main results

* `Contracts.Binomial.exerciseValue_market_europeanPutPayoff`: the deflated exercise value of the
  put is `e^{−ρ ⌊t / h⌋₊} (K − S_{⌊t / h⌋₊})⁺`.
* `Contracts.Binomial.americanPrice_market_europeanPutPayoff`: for `h > 0` and the CRR probability
  `q`, the American price of the put in the binomial market under `coinFlipMeasure q`, with
  horizon `T`, is `americanPrice u d ρ (fun S ↦ max (K − S) 0) ⌊T / h⌋₊ S₀`.

## References

* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  4.4
* [H. Föllmer and A. Schied, *Stochastic Finance*][FollmerSchied], §6.1

## Tags

American put, binomial tree, Snell envelope, optimal stopping, market, pricing measure,
MSC 91G20, MSC 60G40, JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts.Binomial

variable {u d ρ h : ℝ}

/-- The deflated exercise value of the put in the binomial market is the discounted put payoff
after the steps made: `e^{−ρ n} (K − Sₙ)⁺` with `n = ⌊t / h⌋₊`. -/
theorem exerciseValue_market_europeanPutPayoff (P : Measure (ℕ → Bool)) (S₀ K : ℝ)
    (hh : 0 ≤ h) :
    (market P S₀ u d ρ hh).exerciseValue (europeanPutPayoff K) = fun (t : ℝ≥0) ω ↦
      Real.exp (-ρ * ⌊(t : ℝ) / h⌋₊) * max (K - spotPath S₀ u d ⌊(t : ℝ) / h⌋₊ ω) 0 := by
  funext t ω
  simp [Market.exerciseValue, Market.deflator, market, europeanPutPayoff, Payoff.eval,
    scenarioAt, assets, div_eq_mul_inv, ← Real.exp_neg]

/-- **The binomial American put is the market's American put.** For a step `h > 0` and the
risk-neutral probability `q = crrUpProb u d ρ`, the American price of the put
(`Market.americanPrice` of the exercise right `europeanPutPayoff K`) in the binomial market under
the coin flips `coinFlipMeasure q`, with horizon `T`, is the Bellman price of the tree with
`⌊T / h⌋₊` steps. -/
theorem americanPrice_market_europeanPutPayoff (hh : 0 < h) {q : ℝ≥0} (hq : q ≤ 1)
    (hqcrr : crrUpProb u d ρ = q) (P : Measure (ℕ → Bool)) (S₀ K : ℝ) (T : ℝ≥0) :
    (market P S₀ u d ρ hh.le).americanPrice (coinFlipMeasure q hq) (europeanPutPayoff K) T =
      americanPrice u d ρ (fun S ↦ max (K - S) 0) ⌊(T : ℝ) / h⌋₊ S₀ := by
  have hZ (n : ℕ) :
      PathAdaptedAt n fun ω ↦ Real.exp (-ρ * n) * max (K - spotPath S₀ u d n ω) 0 :=
    fun ω ω' hω ↦ by dsimp only; rw [pathAdaptedAt_spotPath S₀ u d n ω ω' hω]
  rw [Market.americanPrice, exerciseValue_market_europeanPutPayoff]
  calc _ = stoppingValue (coinFlipMeasure q hq) flipFiltration
          (fun n ω ↦ Real.exp (-ρ * n) * max (K - spotPath S₀ u d n ω) 0) ⌊(T : ℝ) / h⌋₊ :=
        stoppingValue_comp_floorDiv (monotone_floor_div hh.le) hh _ _ T
    _ = ∫ ω, snellEnvelope (coinFlipMeasure q hq) flipFiltration Set.univ
          (fun n ω ↦ Real.exp (-ρ * n) * max (K - spotPath S₀ u d n ω) 0)
          ⌊(T : ℝ) / h⌋₊ 0 ω ∂coinFlipMeasure q hq :=
        (snellEnvelope_optimalStopping
          (fun n ↦ (stronglyMeasurable_flipFiltration_iff.2 (hZ n)).measurable)
          (fun n ↦ (hZ n).integrable hq) _).2.2.1
    _ = ∫ _, americanPrice u d ρ (fun S ↦ max (K - S) 0) ⌊(T : ℝ) / h⌋₊ S₀
          ∂coinFlipMeasure q hq :=
        integral_congr_ae (americanPrice_eq_snellEnvelope hq hqcrr _ S₀ _)
    _ = _ := by simp

end MathFin.Contracts.Binomial
