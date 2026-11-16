/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.BlackScholes.Market
public import MathFin.Pricing.AmericanPrice
public import MathFin.Probability.Brownian.BrownianMartingale
public import MathFin.Models.BlackScholes.American.Stopping.BrownianBellman
public import MathFin.Models.BlackScholes.American.Stopping.ActualNormalization

/-!
# The Black–Scholes market's American put

The Black–Scholes market (`Models/BlackScholes/Market.lean`) is a `Market`, so it prices an
American exercise right by `Market.americanPrice`: the supremum, over the stopping rules of the
information of `W`, of the expected deflated exercise value. This file computes it for the put, at
the Girsanov pricing measure `Q` of the market price of risk `θ = (m − r)/σ`, and finds the American
put price of the free-boundary problem, `K · canonicalPrice`.

Three steps chain.

* **A continuous version of `B^θ`.** The Girsanov drift is frozen after the horizon `H`
  (`driftContinuousMod_of_ge`), so at every time `u`, almost surely,
  `B^θ_u = W_u + θ min(u, H)` (`constBtheta_ae_eq_path`). The right side, `constBthetaPath`, is
  adapted to the information of `W` and has continuous paths wherever `W` does, and as an adapted
  modification of `B^θ` it is a filtered pre-Brownian motion under `Q`
  (`isFilteredPreBrownian_constBthetaPath`, through `IsFilteredPreBrownian.congr`).
* **The exercise value is the risk-neutral put reward, path by path.** Up to `H`, the physical
  asset `S₀ exp((m − σ²/2)u + σW_u)` is `S₀ exp((r − σ²/2)u + σ(W_u + θu))`, so the deflated
  exercise value of the put equals the discounted put reward of the risk-neutral asset of
  `constBthetaPath` at every time and on every path
  (`exerciseValue_europeanPutPayoff_eq_putRewardAt`), with no null set to remove.
* **The American put value is law-invariant** (`americanPutValue_eq_brownianAmericanPut`): over any
  filtered pre-Brownian motion with continuous paths it is the canonical value
  `brownianAmericanPut`, which normalizes to `K · canonicalPrice`
  (`brownianAmericanPut_normalization`).

## Main definitions

* `constBthetaPath`: `W_u + θ min(u, H)`, the pathwise version of the Girsanov Brownian motion.

## Main results

* `isFilteredPreBrownian_constBthetaPath`: it is a filtered pre-Brownian motion under the Girsanov
  measure.
* `americanPrice_market_europeanPutPayoff`: for `σ ≠ 0`, `T ≤ H`, continuous paths of `W`,
  `K, r ≥ 0` and `S₀ > 0`, the American price of the put in `BlackScholes.market` under the
  Girsanov measure is `brownianAmericanPut K r 0 σ S₀ T`.
* `americanPrice_market_europeanPutPayoff_eq_canonicalPrice`: for `K, σ > 0` it is
  `K · canonicalPrice` at the normalized rate `2r/σ²`, log-moneyness `log(S₀/K)` and normalized
  time `σ²T/2`.

## References

* [I. Karatzas and S. E. Shreve, *Methods of Mathematical Finance*][KaratzasShreve1998], §2.5
* [G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*][PeskirShiryaev2006]

## Tags

American put, Black–Scholes market, Girsanov measure, optimal stopping, law invariance,
continuous modification, MSC 91G20, MSC 60G40, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open MathFin MathFin.BlackScholes.AmericanPut.Stopping MathFin.BlackScholes.AmericanPut.Boundary
  ItoIntegralL2 ItoIntegralProcessContinuousModification

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The Girsanov Brownian motion of a constant market price of risk `θ` with horizon `H`, read path
by path: `W_u + θ min(u, H)`. -/
noncomputable def constBthetaPath (W : ℝ≥0 → Ω → ℝ) (θ : ℝ) (H u : ℝ≥0) (ω : Ω) : ℝ :=
  W u ω + θ * ((min u H : ℝ≥0) : ℝ)

theorem continuous_constBthetaPath {ω : Ω} (hpaths : Continuous fun t ↦ W t ω) (θ : ℝ)
    (H : ℝ≥0) : Continuous fun u ↦ constBthetaPath W θ H u ω :=
  hpaths.add (continuous_const.mul
    (NNReal.continuous_coe.comp (continuous_id.min continuous_const)))

variable (hWmeas : ∀ t, Measurable (W t))

/-- **`B^θ` is `W_u + θ min(u, H)` at each time.** Up to `H` this is `constBtheta_drift_ae`; after
`H` the drift is frozen at its value at `H` (`driftContinuousMod_of_ge`). -/
theorem constBtheta_ae_eq_path (θ : ℝ) (H u : ℝ≥0) :
    constBtheta (μ := μ) hWmeas θ H u =ᵐ[μ] constBthetaPath W θ H u := by
  rcases le_total u H with hu | hu
  · filter_upwards [constBtheta_drift_ae (μ := μ) hWmeas θ H hu] with ω hω
    rw [hω, constBthetaPath, min_eq_left hu]
  · filter_upwards [constBtheta_drift_ae (μ := μ) hWmeas θ H le_rfl] with ω hω
    have hfreeze : constBtheta (μ := μ) hWmeas θ H u ω - W u ω
        = constBtheta (μ := μ) hWmeas θ H H ω - W H ω := by
      simp only [constBtheta, BthetaPred, add_sub_cancel_left]
      exact driftContinuousMod_of_ge _ _ _ hu ω
    rw [constBthetaPath, min_eq_right hu]
    linarith

variable (hW : IsPreBrownianReal W μ)

/-- **The pathwise `B^θ` is a Brownian motion for the information of `W` under `Q`**: an adapted
modification of `B^θ` (`isFilteredPreBrownian_constBtheta`, `IsFilteredPreBrownian.congr`). -/
theorem isFilteredPreBrownian_constBthetaPath (θ : ℝ) (H : ℝ≥0) :
    IsFilteredPreBrownian (constBthetaPath W θ H) (natFiltration hWmeas)
      (constGirsanovMeasure hW hWmeas θ H) :=
  (isFilteredPreBrownian_constBtheta hW hWmeas θ H).congr
    (fun u ↦ ((stronglyAdapted_natFiltration hWmeas u).measurable.add_const _).stronglyMeasurable)
    fun u ↦ (withDensity_absolutelyContinuous _ _).ae_le (constBtheta_ae_eq_path hWmeas θ H u)

omit [IsProbabilityMeasure μ] in
/-- **The deflated exercise value of the put is the risk-neutral put reward**, at every time up to
the horizon `H` and on every path: the physical asset `S₀ exp((m − σ²/2)t + σW_t)` is the
risk-neutral asset `S₀ exp((r − σ²/2)t + σ(W_t + θt))` of `θ = (m − r)/σ`. -/
theorem exerciseValue_europeanPutPayoff_eq_putRewardAt {S_0 m r σ K : ℝ} (hσ : σ ≠ 0)
    {H t : ℝ≥0} (ht : t ≤ H) (ω : Ω) :
    (market μ hWmeas S_0 m r σ).exerciseValue (europeanPutPayoff K) t ω =
      putRewardAt (constBthetaPath W ((m - r) / σ) H) K r 0 σ S_0 t ω := by
  have key : (m - σ ^ 2 / 2) * (t : ℝ) + σ * W t ω
      = (r - 0 - σ ^ 2 / 2) * (t : ℝ) + σ * constBthetaPath W ((m - r) / σ) H t ω := by
    rw [constBthetaPath, min_eq_left ht]
    field_simp
    ring
  rw [Market.exerciseValue, deflator_market]
  simp only [europeanPutPayoff, Payoff.eval, scenarioAt, market, pathAssets, putRewardAt, putReward,
    gbmValue, key]

/-- **The American put of the Black–Scholes market.** For `σ ≠ 0`, a horizon `T ≤ H`, `W` with
continuous paths, `K, r ≥ 0` and `S₀ > 0`, the American price of the put
(`Market.americanPrice` of the exercise right `europeanPutPayoff K`) in `BlackScholes.market` under
the Girsanov pricing measure of `θ = (m − r)/σ` is the canonical American put value
`brownianAmericanPut K r 0 σ S₀ T`. -/
theorem americanPrice_market_europeanPutPayoff (hpaths : ∀ ω, Continuous fun t ↦ W t ω)
    {S_0 m r σ K : ℝ} {T H : ℝ≥0} (hσ : σ ≠ 0) (hTH : T ≤ H) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hS : 0 < S_0) :
    (market μ hWmeas S_0 m r σ).americanPrice (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (europeanPutPayoff K) T = brownianAmericanPut K r 0 σ S_0 T := by
  have := constGirsanovMeasure_isProbabilityMeasure hW hWmeas ((m - r) / σ) H
  rw [Market.americanPrice, ← americanPutValue_eq_brownianAmericanPut
    (isFilteredPreBrownian_constBthetaPath hWmeas hW ((m - r) / σ) H)
    (fun ω ↦ continuous_constBthetaPath (hpaths ω) _ H) hK hr hS T, americanPutValue]
  exact stoppingValue_congr fun t ht ω ↦
    exerciseValue_europeanPutPayoff_eq_putRewardAt hWmeas hσ (ht.trans hTH) ω

/-- **The American put of the Black–Scholes market in normalized coordinates.** For `K, σ > 0`
it is `K · canonicalPrice` of the normalized rates, log-moneyness `log(S₀/K)` and normalized time
`σ²T/2`: the value of the canonical free-boundary problem. -/
theorem americanPrice_market_europeanPutPayoff_eq_canonicalPrice
    (hpaths : ∀ ω, Continuous fun t ↦ W t ω) {S_0 m r σ K : ℝ} {T H : ℝ≥0} (hσ : 0 < σ)
    (hTH : T ≤ H) (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S_0) :
    (market μ hWmeas S_0 m r σ).americanPrice (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (europeanPutPayoff K) T =
      K * canonicalPrice (normalizedRate r σ) (normalizedRate 0 σ) (Real.log (S_0 / K))
        (σ ^ 2 / 2 * (T : ℝ)) := by
  rw [americanPrice_market_europeanPutPayoff hWmeas hW hpaths hσ.ne' hTH hK.le hr hS,
    brownianAmericanPut_normalization hK hr hσ hS T]

end MathFin.Contracts.BlackScholes
