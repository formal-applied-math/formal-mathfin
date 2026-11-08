/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.BlackScholes.BlackScholesChooser
public import MathFin.Models.BlackScholes.DeltaHedge

/-!
# The Black–Scholes delta hedge of the European call contract

`Models/BlackScholes/DeltaHedge` proves the replication theorem in terms of the closed form `bsV`.
This file states it for the contract: under the Black–Scholes model map `BlackScholes.pathAssets`
(`S_u = S₀ exp((r − σ²/2)u + σ B_u)`), the value of the reified `europeanCall K T` is the call
price `bsV K r σ S₀ T`, and the delta hedge started with that capital reproduces the discounted
call price at every time before maturity. The continuous-time counterpart of the binomial
statement that the hedge's capital is the contract's value.

* The contract's value is the hedge's initial capital: the discounted call price
  `e^{−rt} bsV K r σ S_t (T − t)` is `(europeanCall K T).value …` plus the Itô integral of the
  delta-hedge integrand, almost surely, for all `t ≤ T'` at once, for every `T' < T`
  (`europeanCall_deltaHedge`).
* At maturity the discounted call price converges, as `t → T⁻`, along every path continuous at
  `T`, to the contract's discounted payoff `pathPV` (`tendsto_hedge_europeanCall_payoff`).

The integral identity is stated on `[0, T']` with `T' < T`; the limit at `T` is a separate
statement, not an identity of the integral up to `T`. Nothing here says the hedge is an
admissible self-financing strategy as a structure, or that the Itô integral against `B` equals
the integral of the delta against the discounted stock.

## Main results

* `BlackScholes.value_europeanCall_pathAssets`: under a pre-Brownian `B`, the value of
  `europeanCall K T` along the Black–Scholes path is `bsV K r σ S₀ T`.
* `BlackScholes.europeanCall_deltaHedge`: the discounted call price along the path is the
  contract's value plus the delta-hedge gains, on `[0, T']`, `T' < T`.
* `BlackScholes.tendsto_hedge_europeanCall_payoff`: the discounted call price tends to the
  contract's discounted payoff as `t → T⁻`.

## References

* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 4.5
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 15.6

## Tags

delta hedging, replication, European call, contract value, Black–Scholes path,
MSC 91G20, MSC 60H05, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The Black–Scholes model map along a path is `gbmValue` at the Brownian coordinate. -/
theorem pathAssets_eq_gbmValue (S_0 r σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    pathAssets S_0 r σ B () t ω = gbmValue S_0 r σ t (B t ω) := rfl

/-- **The call contract's value along the Black–Scholes path is the call price.** For a
pre-Brownian `B` under a probability measure `μ`, positive spot, strike and volatility and a
positive maturity, `(europeanCall K T).value` at the discount `e^{−ru}` is `bsV K r σ S₀ T`. -/
theorem value_europeanCall_pathAssets {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {T : ℝ≥0} (hT : 0 < (T : ℝ))
    {S_0 K r σ : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) :
    (europeanCall K T).value μ (fun u _ ↦ Real.exp (-r * u)) (pathAssets S_0 r σ B)
      = bsV K r σ S_0 T := by
  have hyp : BSCallHyp μ S_0 K r σ T (fun ω ↦ B T ω / Real.sqrt T) := by
    simpa using BSCallHyp.of_isPreBrownian μ B hB hS₀ hK hσ hT
  rw [europeanCall, Contract.value_pay]
  simp only [europeanCallPayoff, Payoff.eval, scenarioAt, pathAssets_eq_bsTerminal B hT]
  rw [bs_call_formula hyp, bsV]
  simp only [neg_mul]

/-- **The contract's value is the delta hedge's initial capital.** Let `B` be a Brownian motion
with continuous paths, `T' < T`, and `K, σ, S₀ > 0`. Almost surely, for all
`t ≤ T'` at once, the discounted call price along the Black–Scholes path equals the value of
`europeanCall K T` plus the gains `∫₀ᵗ Δ σ e^{−rs} S_s dB_s` of the delta hedge, with the delta
`Φ(d₁(S_s, T − s))` (`deltaHedgeIntegrand`). Stated on `[0, T']` for `T' < T`;
the limit at `T` is `tendsto_hedge_europeanCall_payoff`. -/
theorem europeanCall_deltaHedge {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) {T : ℝ≥0} (hT : 0 < (T : ℝ))
    {S_0 K r σ : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (T' : ℝ≥0) (hT' : T' < T) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T',
      Real.exp (-(r * t)) * bsV K r σ (pathAssets S_0 r σ B () t ω) (T - t)
        = (europeanCall K T).value μ (fun u _ ↦ Real.exp (-r * u)) (pathAssets S_0 r σ B)
          + ItoIntegralLocalised.predItoIntegral (μ := μ) T' hBmeas
            (deltaHedgeIntegrand_isStronglyPredictable hBmeas hBcont K r σ S_0 (T : ℝ)) t ω := by
  filter_upwards [bs_delta_hedge_replication hB hBmeas hBcont hK hσ hS₀ T'
    (NNReal.coe_lt_coe.2 hT')] with ω h t ht
  rw [value_europeanCall_pathAssets hB hT hS₀ hK hσ]
  exact h t ht

/-- **The hedge pays the contract.** Along a path `B · ω` continuous at `T`, the discounted call
price `e^{−rt} bsV K r σ S_t (T − t)` tends, as `t → T⁻`, to the discounted payoff of
`europeanCall K T` on that path (`Contract.pathPV`). -/
theorem tendsto_hedge_europeanCall_payoff {B : ℝ≥0 → Ω → ℝ} {S_0 K r σ : ℝ} (hK : 0 < K)
    (hσ : 0 < σ) (hS₀ : 0 < S_0) (T : ℝ≥0) {ω : Ω}
    (hω : ContinuousAt (fun t ↦ B t ω) T) :
    Tendsto (fun t : ℝ≥0 ↦ Real.exp (-(r * t)) * bsV K r σ (pathAssets S_0 r σ B () t ω) (T - t))
      (𝓝[<] T)
      (𝓝 ((europeanCall K T).pathPV (fun u ↦ Real.exp (-r * u))
        (scenarioAt (pathAssets S_0 r σ B) ω))) := by
  have hexp : Tendsto (fun t : ℝ≥0 ↦ Real.exp (-(r * t))) (𝓝[<] T) (𝓝 (Real.exp (-(r * T)))) :=
    ((by fun_prop : Continuous fun t : ℝ≥0 ↦ Real.exp (-(r * t))).tendsto T).mono_left
      nhdsWithin_le_nhds
  have h := hexp.mul (tendsto_bsV_gbm_payoff (r := r) T hK hσ hS₀ hω)
  convert h using 2 <;>
    simp [Contract.pathPV, Contract.cashflows, europeanCall, europeanCallPayoff, Payoff.eval,
      scenarioAt, pathAssets, gbmValue, neg_mul]

end MathFin.Contracts.BlackScholes
