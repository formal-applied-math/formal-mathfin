/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Bridges.PricingFromBrownian
public import MathFin.BlackScholes.AmericanPut.Stopping.UsualBrownianValue

/-!
# The American put dominates the Black–Scholes–Merton European put

The American-put tower (`BlackScholes/AmericanPut/Stopping/`) defines the continuous-time
American put value as a supremum of expected discounted put payoffs over stopping rules bounded
by the horizon `T` (`americanPutValue`), with the stock the explicit geometric Brownian motion
`gbmValue S (r − q) σ t (W t)` and discount rate `r`. Because the deterministic rule `θ ≡ T` is
admissible, that value dominates the expected payoff of exercising at maturity
(`european_expectation_le_value`). This file computes that expectation in closed form: when `W`
is a pre-Brownian motion it is the Black–Scholes–Merton European put with continuous dividend
yield `q`,

  `bsPDiv K r q σ S T = e^{−qT}·(K·e^{−(r−q)T}·Φ(−d₂) − S·Φ(−d₁))`

(`maturityReward_eq_bsPDiv`, via `bs_dividends_put_formula_via_brownian`, i.e. `bs_put_formula`
under `BSCallHyp.of_isPreBrownian`). Hence the American put value is at least the closed-form
European put (`bsPDiv_le_americanPutValue`), in particular for the constructed Brownian model on
its raw natural filtration and on its completed usual filtration, the setting of the
exercise-boundary results (`bsPDiv_le_brownianAmericanPut`,
`bsPDiv_le_brownianUsualAmericanPut`).

Not proved here: that the inequality is strict (a positive early-exercise premium), or any
optimal-stopping characterization of the value.

## Results

* `maturityReward_eq_bsPDiv`: the expected discounted payoff of exercise at `T` is `bsPDiv`.
* `bsPDiv_le_americanPutValue`: the American put value over any filtration dominates `bsPDiv`.
* `bsPDiv_le_brownianAmericanPut`, `bsPDiv_le_brownianUsualAmericanPut`: the constructed
  Brownian model on its raw and on its usual filtration.
* `bsP_le_brownianUsualAmericanPut`: without dividends, the Black–Scholes put `bsP`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Exercise at maturity is worth the Black–Scholes–Merton put.** For a pre-Brownian motion
`W` under `P` and `S, K, σ > 0`, `T > 0`, the expected discounted payoff of the deterministic
rule `θ ≡ T`, `E[e^{−rT}·(K − S·e^{(r−q−σ²/2)T + σ W_T})⁺]`, is `bsPDiv K r q σ S T`. -/
theorem maturityReward_eq_bsPDiv {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W P) {K r q σ S : ℝ}
    (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) {T : ℝ≥0} (hT : 0 < T) :
    ∫ ω, putReward W K r q σ S (fun _ ↦ T) ω ∂P = bsPDiv K r q σ S T := by
  have hT' : (0 : ℝ) < T := NNReal.coe_pos.mpr hT
  rw [← bs_dividends_put_formula_via_brownian P W hW hS hK hσ hT', Real.toNNReal_coe]
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  simp only [putReward, gbmValue, bsTerminal]
  rw [mul_assoc σ, mul_div_cancel₀ _ (Real.sqrt_pos.mpr hT').ne']

/-- **The American put dominates the Black–Scholes–Merton European put.** For a jointly
measurable pre-Brownian motion `W` under `P`, any filtration `𝓕`, `r ≥ 0` and `S, K, σ, T > 0`,
the American put value over `𝓕`-stopping rules bounded by `T` is at least `bsPDiv K r q σ S T`.
-/
theorem bsPDiv_le_americanPutValue {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
    (hW : IsPreBrownianReal W P) (hWm : Measurable W.uncurry) {K r q σ S : ℝ}
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) (hS : 0 < S) {T : ℝ≥0} (hT : 0 < T) :
    bsPDiv K r q σ S T ≤ americanPutValue P 𝓕 W K r q σ S T :=
  (maturityReward_eq_bsPDiv hW hK hσ hS hT).symm.trans_le
    (european_expectation_le_value hWm hK.le hr hS.le)

/-- The constructed Brownian model on its raw natural filtration: `bsPDiv ≤ brownianAmericanPut`. -/
theorem bsPDiv_le_brownianAmericanPut {K r q σ S : ℝ} (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ)
    (hS : 0 < S) {T : ℝ≥0} (hT : 0 < T) :
    bsPDiv K r q σ S T ≤ brownianAmericanPut K r q σ S T :=
  bsPDiv_le_americanPutValue isBrownianReal_brownian.toIsPreBrownianReal
    measurable_brownian_uncurry hK hr hσ hS hT

/-- **The American put of the constructed Brownian model, on its completed usual filtration,
dominates the Black–Scholes–Merton European put.** This is the value whose exercise boundary the
boundary-convexity results study. The maturity reward is computed on `gaussianLimit` and
transported to its completion (`integral_completion_original`). -/
theorem bsPDiv_le_brownianUsualAmericanPut {K r q σ S : ℝ} (hK : 0 < K) (hr : 0 ≤ r)
    (hσ : 0 < σ) (hS : 0 < S) {T : ℝ≥0} (hT : 0 < T) :
    bsPDiv K r q σ S T ≤ brownianUsualAmericanPut K r q σ S T := by
  have he := integral_completion_original gaussianLimit
    (putReward_measurable measurable_brownian_uncurry K r q σ S measurable_const).stronglyMeasurable
      (f := putReward brownian K r q σ S (fun _ => T))
  rw [← maturityReward_eq_bsPDiv isBrownianReal_brownian.toIsPreBrownianReal hK hσ hS hT, ← he]
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact european_expectation_le_value (P := μ) (𝓕 := brownianUsualFiltration)
    brownian_completed_measurable hK.le hr hS.le

/-- Without dividends (`q = 0`): the American put of the constructed Brownian model on its usual
filtration is at least the Black–Scholes put `bsP K r σ S T = K e^{−rT}Φ(−d₂) − SΦ(−d₁)`. -/
theorem bsP_le_brownianUsualAmericanPut {K r σ S : ℝ} (hK : 0 < K) (hr : 0 ≤ r)
    (hσ : 0 < σ) (hS : 0 < S) {T : ℝ≥0} (hT : 0 < T) :
    bsP K r σ S T ≤ brownianUsualAmericanPut K r 0 σ S T := by
  simpa [bsPDiv] using bsPDiv_le_brownianUsualAmericanPut (q := 0) hK hr hσ hS hT

end MathFin.BlackScholes.AmericanPut.Stopping
