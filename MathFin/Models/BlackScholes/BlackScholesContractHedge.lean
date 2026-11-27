/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Pricing.ContractHedge
public import MathFin.Models.BlackScholes.BlackScholesHedge

/-!
# The European call under Black–Scholes is replicated by a holding in the price

`Pricing/ContractHedge.lean` proves, for every fixed-dated contract of the language with
square-integrable discounted cash flows, that the cash flows are `value + ∫₀ᵀ ψ dS` for a unique
holding `ψ` in the Brownian price `S = S₀ + (vol●B)`. This file instantiates it at the reified
`europeanCall K T` on the Black–Scholes path `pathAssets S₀ r σ B`: the cash flow is the discounted
payoff `e^{−rT} max (S_T − K) 0`, the initial wealth of the hedge is the Black–Scholes price
`bsV K r σ S₀ T` (`value_europeanCall_pathAssets`), and the one new input is that the call payoff
is square-integrable, because the lognormal terminal price is (`memLp_two_bsTerminal`).

## Scope

The price `S` in which the hedge is held is the Itô price `S₀ + (vol●B)` for **any** volatility
`vol` square-integrable against `dt ⊗ μ` and almost everywhere nonzero; it is not shown to be the
discounted Black–Scholes stock `e^{−ru}S_u`, whose volatility is `σ e^{−ru}S_u`. The library has
the stock as a solution of its SDE with the localised integral `predItoIntegral`
(`pathAssets_solves_sde`), whereas the price `S` is built from the `L²` integral `itoProcessCLM`;
the bridge between the two integrals is not proved. For that reason the holding `ψ` is **not**
identified with the delta `Φ(d₁)` of `europeanCall_deltaHedge`, which integrates the delta-hedge
integrand against `B` on `[0, T']`, `T' < T`. What both hedges share is the capital they start
from, the contract's value `bsV K r σ S₀ T`.

## Main results

* `BlackScholes.europeanCall_hedge_in_price`: the discounted call payoff is
  `bsV K r σ S₀ T + ∫₀ᵀ ψ dS` almost surely for a unique holding `ψ` in the price.

## References

* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 5.4
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]

## Tags

replication, hedging strategy, European call, Black–Scholes price, complete market,
martingale representation, MSC 91G20, MSC 60H05, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathFin ItoIntegralCLM ItoIntegralAgainstMartingale ItoIntegralL2
open scoped NNReal

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The Black–Scholes call price is the initial capital of a replicating holding in the price.**
Let `B` be a Brownian motion with continuous paths under `μ`, `S = S₀ + (vol●B)` a discounted price
with volatility `vol ≠ 0` a.e., and `S₀, K, σ, T > 0`. The discounted payoff of
`europeanCall K T` on the Black–Scholes path `pathAssets S₀ r σ B` is

  `bsV K r σ S₀ T + ∫₀ᵀ ψ dS`  almost surely

for a **unique** holding `ψ` in the price: the contract's value, which is the call price
(`value_europeanCall_pathAssets`), is the capital the hedge starts from. -/
theorem europeanCall_hedge_in_price {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) {T : ℝ≥0} (hT : 0 < (T : ℝ))
    {S_0 K r σ : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ)
    (vol : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hvol : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas), (vol : ℝ≥0 × Ω → ℝ) z ≠ 0) :
    ∃! ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas vol),
      (fun ω ↦ (europeanCall K T).pathPV (fun u ↦ Real.exp (-r * u))
          (scenarioAt (pathAssets S_0 r σ B) ω)) =ᵐ[μ]
        fun ω ↦ bsV K r σ S_0 T + (itoIntegralAgainstCLM hB T hBmeas vol ψ : Ω → ℝ) ω := by
  have hfix : (europeanCall K T).FixedDated := by simp [europeanCall, Contract.FixedDated]
  have hX (i : Unit) (t : ℝ≥0) :
      Measurable[natFiltration hBmeas t] (pathAssets S_0 r σ B i t) := by
    have hBt : Measurable[natFiltration hBmeas t] (B t) :=
      (stronglyAdapted_natFiltration hBmeas t).measurable
    exact (Real.measurable_exp.comp
      ((hBt.const_mul σ).const_add ((r - σ ^ 2 / 2) * (t : ℝ)))).const_mul S_0
  have hobs : ∀ p ∈ (europeanCall K T).obsList, p.2 ≤ T := by
    simp [europeanCall, europeanCallPayoff, Contract.obsList, Payoff.obsList]
  have hdates : ∀ t ∈ (europeanCall K T).dates, t ≤ T := by
    simp [europeanCall, Contract.dates]
  have hpv (ω : Ω) : (europeanCall K T).pathPV (fun u ↦ Real.exp (-r * u))
      (scenarioAt (pathAssets S_0 r σ B) ω)
        = Real.exp (-r * T) * max (pathAssets S_0 r σ B () T ω - K) 0 := by
    simp [Contract.pathPV, Contract.cashflows, europeanCall, europeanCallPayoff, Payoff.eval,
      scenarioAt]
  have hZ : HasLaw (fun ω ↦ B T ω / Real.sqrt T) (gaussianReal 0 1) μ := by
    simpa using scaled_isPreBrownian_eval_law B hB hT
  have hmemS : MemLp (fun ω ↦ pathAssets S_0 r σ B () T ω) 2 μ := by
    simp only [pathAssets_eq_bsTerminal B hT]
    exact memLp_two_bsTerminal hZ S_0 r σ T
  have hmeas := Contract.measurable_pathPV hfix (D := fun u _ ↦ Real.exp (-r * u))
    (fun _ ↦ measurable_const) (X := pathAssets S_0 r σ B)
    (fun i t ↦ (hX i t).mono ((natFiltration hBmeas).le t) le_rfl)
  have hL2 : MemLp (fun ω ↦ (europeanCall K T).pathPV (fun u ↦ Real.exp (-r * u))
      (scenarioAt (pathAssets S_0 r σ B) ω)) 2 μ := by
    refine MemLp.of_le (g := fun ω ↦ Real.exp (-r * T) * pathAssets S_0 r σ B () T ω)
      (hmemS.const_mul _) hmeas.aestronglyMeasurable (.of_forall fun ω ↦ ?_)
    have hS : 0 ≤ pathAssets S_0 r σ B () T ω := pathAssets_nonneg B hS₀.le r σ T ω
    show ‖(europeanCall K T).pathPV (fun u ↦ Real.exp (-r * u))
        (scenarioAt (pathAssets S_0 r σ B) ω)‖
      ≤ ‖Real.exp (-r * T) * pathAssets S_0 r σ B () T ω‖
    rw [hpv ω, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (le_max_right _ _)),
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hS)]
    exact mul_le_mul_of_nonneg_left (max_le (by linarith) hS) (Real.exp_pos _).le
  have h := Contract.exists_unique_hedge_in_price hB hBmeas hBcont T vol hvol hfix
    (D := fun u _ ↦ Real.exp (-r * u)) (X := pathAssets S_0 r σ B) (fun _ ↦ measurable_const) hX
    hobs hdates hL2
  rwa [value_europeanCall_pathAssets hB hT hS₀ hK hσ] at h

end MathFin.Contracts.BlackScholes
