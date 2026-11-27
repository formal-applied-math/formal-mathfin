/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Pricing.ContractHedge
public import MathFin.Models.BlackScholes.BlackScholesContractHedge
public import MathFin.Models.BlackScholes.BlackScholesSDE
public import MathFin.Probability.Brownian.Ito.ItoIntegralPredictableL2

/-!
# In Black–Scholes, a contract on the stock is replicated by a holding in the stock

`BlackScholesContractHedge` replicates a contract by a holding in a Brownian price
`S₀ + (vol●B)` for an arbitrary nonzero `L²` volatility. Here the volatility is the stock's. The
discounted Black–Scholes stock is `S̃_t = e^{−rt} S_t = S₀ exp(−σ²t/2 + σB_t)`, a geometric
Brownian motion with volatility `σ S̃`, so its price in the sense of `pricePath` is the one with
`vol = σ S̃`.

* `stockVol` is the class of `σ S̃` in `Lp ℝ 2 (trimMeasure T)`. It exists because `σ S̃` is
  predictable (`isStronglyPredictable_diffusion_pathAssets`) and its second moments are bounded on
  `[0, T]` by the lognormal moment (`memLp_two_diffusion_pathAssets`).
* `pricePath_stockVol_ae_eq`: `pricePath` with volatility `stockVol` is, at every `t ≤ T`, almost
  surely the discounted stock. The stock solves its SDE with the localised integral
  `predItoIntegral` (`pathAssets_solves_sde` at `r = 0`), and for a square-integrable integrand
  that integral is the `L²` one behind `pricePath` (`ae_predItoIntegral_eq_itoProcessCLM`).
* `exists_unique_hedge_in_stock`: for every contract on the stock that pays at fixed dates in
  `[0, T]` and whose discounted cash flows are square-integrable, a unique holding in this price
  — the discounted stock — has terminal wealth the contract's discounted cash flow, at initial
  wealth `Contract.value`.
* `europeanCall_hedge_in_stock`: the call, at initial wealth the Black–Scholes price `bsV`.

## Scope

The wealth is in discounted units, as in `Pricing/ContractHedge.lean`, and the contract is on the
stock `pathAssets S₀ r σ B` with the deterministic discount `e^{−ru}`. The statements here do not
say what the holding `ψ` is: it is an `L²` class, given by the representation theorem. That it is
the delta `Φ(d₁)` of `europeanCall_deltaHedge` is `europeanCall_hedge_in_stock_eq_delta`
(`BlackScholesStockDelta`), which passes from that theorem's localised integral on `[0, T']`,
`T' < T`, to the `L²` integral on `[0, T]`.
Square-integrability of the cash flows is a hypothesis (`hL2`), discharged for the call.

## Main definitions

* `BlackScholes.stockVol`: the class of the discounted stock's volatility `σ S̃` on `(0, T] × Ω`.

## Main results

* `BlackScholes.memLp_two_diffusion_pathAssets`: `σ S` is square-integrable on `(0, T] × Ω`.
* `BlackScholes.pricePath_stockVol_ae_eq`: the price with volatility `stockVol` is the
  discounted stock.
* `BlackScholes.exists_unique_hedge_in_stock`, `BlackScholes.europeanCall_hedge_in_stock`; the
  holding of the call is the delta in `BlackScholesStockDelta`.

## References

* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 5.4
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]

## Tags

replication, hedging strategy, geometric Brownian motion, Black–Scholes model, complete market,
contract value, MSC 91G20, MSC 60H05, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open MathFin ItoIntegralCLM ItoIntegralAgainstMartingale ItoIntegralL2 ItoIntegralLocalised
open scoped NNReal

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The volatility `σ S` is square-integrable -/

/-- The square of the diffusion coefficient, as a constant times an exponential of the Brownian
value. -/
theorem sq_diffusion_pathAssets (S_0 r σ : ℝ) (s : ℝ≥0) (ω : Ω) :
    (σ * pathAssets S_0 r σ B () s ω) ^ 2
      = σ ^ 2 * S_0 ^ 2 * Real.exp ((2 * r - σ ^ 2) * s) * Real.exp ((2 * σ) * B s ω) := by
  have h : ((r - σ ^ 2 / 2) * s + σ * B s ω) + ((r - σ ^ 2 / 2) * s + σ * B s ω)
      = (2 * r - σ ^ 2) * s + (2 * σ) * B s ω := by ring
  simp only [pathAssets]
  rw [mul_pow, mul_pow, sq (Real.exp _), ← Real.exp_add, h, Real.exp_add]
  ring

/-- **Second moment of the diffusion coefficient.** At a time `s ≤ T`, `(σ S_s)²` is integrable
with expectation at most `σ² S₀² e^{|2r + σ²| T}`: the lognormal moment
`𝔼 exp(2σ B_s) = exp(2σ² s)`. -/
theorem integral_sq_diffusion_pathAssets_le (hB : IsPreBrownianReal B μ) (S_0 r σ : ℝ)
    {T s : ℝ≥0} (hs : s ≤ T) :
    Integrable (fun ω ↦ (σ * pathAssets S_0 r σ B () s ω) ^ 2) μ ∧
      ∫ ω, (σ * pathAssets S_0 r σ B () s ω) ^ 2 ∂μ
        ≤ σ ^ 2 * S_0 ^ 2 * Real.exp (|2 * r + σ ^ 2| * T) := by
  have hlaw := hB.hasLaw_eval s
  have hint : Integrable (fun ω ↦ Real.exp ((2 * σ) * B s ω)) μ := by
    refine Integrable.comp_aemeasurable (g := fun x ↦ Real.exp ((2 * σ) * x)) ?_
      hlaw.aemeasurable
    rw [hlaw.map_eq]
    exact integrable_exp_mul_gaussianReal _
  have hmgf : ∫ ω, Real.exp ((2 * σ) * B s ω) ∂μ
      = Real.exp (0 * (2 * σ) + (s : ℝ) * (2 * σ) ^ 2 / 2) := mgf_gaussianReal hlaw (2 * σ)
  have hfun : (fun ω ↦ (σ * pathAssets S_0 r σ B () s ω) ^ 2) = fun ω ↦
      (σ ^ 2 * S_0 ^ 2 * Real.exp ((2 * r - σ ^ 2) * s)) * Real.exp ((2 * σ) * B s ω) :=
    funext fun ω ↦ sq_diffusion_pathAssets S_0 r σ s ω
  rw [hfun]
  refine ⟨hint.const_mul _, ?_⟩
  rw [integral_const_mul, hmgf]
  have h1 : Real.exp ((2 * r - σ ^ 2) * s)
      * Real.exp (0 * (2 * σ) + (s : ℝ) * (2 * σ) ^ 2 / 2)
        = Real.exp ((2 * r + σ ^ 2) * s) := by
    rw [← Real.exp_add]
    exact congrArg Real.exp (by ring)
  have h2 : (2 * r + σ ^ 2) * (s : ℝ) ≤ |2 * r + σ ^ 2| * T :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (NNReal.coe_nonneg s)).trans
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hs) (abs_nonneg _))
  calc σ ^ 2 * S_0 ^ 2 * Real.exp ((2 * r - σ ^ 2) * s)
        * Real.exp (0 * (2 * σ) + (s : ℝ) * (2 * σ) ^ 2 / 2)
      = σ ^ 2 * S_0 ^ 2 * Real.exp ((2 * r + σ ^ 2) * s) := by rw [mul_assoc, h1]
    _ ≤ σ ^ 2 * S_0 ^ 2 * Real.exp (|2 * r + σ ^ 2| * T) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (by positivity)

/-- **The diffusion coefficient `σ S` is square-integrable on `(0, T] × Ω`** for the predictable
measure: it is predictable (`isStronglyPredictable_diffusion_pathAssets`) with second moments
bounded on `(0, T]` (`integral_sq_diffusion_pathAssets_le`). -/
theorem memLp_two_diffusion_pathAssets (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (S_0 r σ : ℝ) :
    MemLp (Function.uncurry fun (s : ℝ≥0) ω ↦ σ * pathAssets S_0 r σ B () s ω) 2
      (trimMeasure (μ := μ) T hBmeas) :=
  memLp_uncurry_trimMeasure_of_integral_sq_le hBmeas
    (isStronglyPredictable_diffusion_pathAssets hBmeas hBcont S_0 r σ) T _
    fun s hs ↦ integral_sq_diffusion_pathAssets_le hB S_0 r σ hs.2

/-- Every path of the diffusion coefficient is continuous. -/
theorem continuousOn_diffusion_pathAssets (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    (S_0 r σ : ℝ) (T : ℝ≥0) (ω : Ω) :
    ContinuousOn (fun s : ℝ≥0 ↦ σ * pathAssets S_0 r σ B () s ω) (Icc 0 T) := by
  have hg : Continuous fun p : ℝ × ℝ ↦ σ * gbmValue S_0 r σ p.1 p.2 := by
    unfold gbmValue; fun_prop
  exact (hg.comp (NNReal.continuous_coe.prodMk (hBcont ω))).continuousOn

/-! ### The discounted stock as a price -/

/-- **The volatility of the discounted stock**, as a class of `Lp ℝ 2 (trimMeasure T)`: the
process `σ S̃_s = σ S₀ exp(−σ²s/2 + σB_s)`, the diffusion coefficient of `pathAssets S₀ 0 σ B`. -/
noncomputable def stockVol (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0) (S_0 σ : ℝ) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  (memLp_two_diffusion_pathAssets hB hBmeas hBcont T S_0 0 σ).toLp _

/-- The class `stockVol` is the process `σ S̃` almost everywhere. -/
theorem stockVol_ae_eq (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0) (S_0 σ : ℝ) :
    stockVol hB hBmeas hBcont T S_0 σ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      Function.uncurry fun (s : ℝ≥0) ω ↦ σ * pathAssets S_0 0 σ B () s ω :=
  MemLp.coeFn_toLp _

/-- **The volatility of the discounted stock is nonzero** almost everywhere, for a positive spot
and a nonzero volatility `σ`: it is `σ S̃` with `S̃ > 0`. -/
theorem stockVol_ne_zero (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0) {S_0 σ : ℝ} (hS₀ : 0 < S_0)
    (hσ : σ ≠ 0) :
    ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas),
      (stockVol hB hBmeas hBcont T S_0 σ : ℝ≥0 × Ω → ℝ) z ≠ 0 := by
  filter_upwards [stockVol_ae_eq hB hBmeas hBcont T S_0 σ] with z hz
  rw [hz]
  exact mul_ne_zero hσ (mul_pos hS₀ (Real.exp_pos _)).ne'

/-- **The price with the stock's volatility is the discounted stock.** For `t ≤ T`, almost surely,
`S₀ + (stockVol●B)_t = pathAssets S₀ 0 σ B t = e^{−rt} S_t`'s discounted form: the stock solves
`dS̃ = σ S̃ dB` with the localised integral (`pathAssets_solves_sde` at `r = 0`), and that integral
is the `L²` one (`ae_predItoIntegral_eq_itoProcessCLM`, `stockVol` being `σ S̃` a.e.). -/
theorem pricePath_stockVol_ae_eq (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0) (S_0 σ : ℝ) {t : ℝ≥0}
    (ht : t ≤ T) :
    MarketCompletenessInPrice.pricePath hB T hBmeas S_0 (stockVol hB hBmeas hBcont T S_0 σ) t
      =ᵐ[μ] pathAssets S_0 0 σ B () t := by
  have hpred := isStronglyPredictable_diffusion_pathAssets hBmeas hBcont S_0 0 σ
  have hA := ae_predItoIntegral_eq_itoProcessCLM hB T hBmeas hBcont hpred
    (ae_of_all _ fun ω ↦ continuousOn_diffusion_pathAssets hBcont S_0 0 σ T ω)
    (stockVol hB hBmeas hBcont T S_0 σ) (stockVol_ae_eq hB hBmeas hBcont T S_0 σ) ht
  filter_upwards [pathAssets_solves_sde hB hBmeas hBcont T S_0 0 σ, hA] with ω h1 h2
  have h3 := h1 t ⟨zero_le, ht⟩
  simp only [zero_mul, integral_zero, add_zero] at h3
  simp only [MarketCompletenessInPrice.pricePath]
  rw [h3]
  exact congrArg (fun x ↦ S_0 + x) h2.symm

/-- Discounting the stock at the rate `r` removes the drift: `e^{−rt} S_t` is the path with rate
`0`. -/
theorem exp_neg_mul_pathAssets (S_0 r σ : ℝ) (t : ℝ≥0) (ω : Ω) :
    Real.exp (-r * t) * pathAssets S_0 r σ B () t ω = pathAssets S_0 0 σ B () t ω := by
  simp only [pathAssets]
  rw [mul_left_comm, ← Real.exp_add]
  exact congrArg (fun x ↦ S_0 * Real.exp x) (by ring)

/-! ### The hedge in the stock -/

/-- **In Black–Scholes, every contract on the stock is replicated by a unique holding in the
stock.** Let `B` be a Brownian motion with continuous paths, `S = pathAssets S₀ r σ B` the
Black–Scholes stock with `S₀ > 0`, `σ ≠ 0`, and `c` a contract that pays at fixed dates,
observing and paying at dates `≤ T`, whose discounted cash flows at the discount `e^{−ru}` are
square-integrable. Then

* the price `S₀ + (stockVol●B)` is, at every `t ≤ T`, almost surely the discounted stock
  `e^{−rt} S_t`; and
* there is a **unique** holding `ψ` in it with `c.pathPV = c.value + ∫₀ᵀ ψ dS̃` almost surely.

So the contract's value is the initial cost of replicating it in the stock. The wealth is in
discounted units, and this statement does not identify `ψ` (for the call it is the delta,
`europeanCall_hedge_in_stock_eq_delta`). -/
theorem exists_unique_hedge_in_stock (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    {S_0 r σ : ℝ} (hS₀ : 0 < S_0) (hσ : σ ≠ 0) {c : Contract Unit} (hc : c.FixedDated)
    (hobs : ∀ p ∈ c.obsList, p.2 ≤ T) (hdates : ∀ t ∈ c.dates, t ≤ T)
    (hL2 : MemLp (fun ω ↦ c.pathPV (fun u ↦ Real.exp (-r * u))
      (scenarioAt (pathAssets S_0 r σ B) ω)) 2 μ) :
    (∀ t : ℝ≥0, t ≤ T →
      MarketCompletenessInPrice.pricePath hB T hBmeas S_0 (stockVol hB hBmeas hBcont T S_0 σ) t
        =ᵐ[μ] fun ω ↦ Real.exp (-r * t) * pathAssets S_0 r σ B () t ω) ∧
    ∃! ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas (stockVol hB hBmeas hBcont T S_0 σ)),
      (fun ω ↦ c.pathPV (fun u ↦ Real.exp (-r * u)) (scenarioAt (pathAssets S_0 r σ B) ω))
        =ᵐ[μ] fun ω ↦ c.value μ (fun u _ ↦ Real.exp (-r * u)) (pathAssets S_0 r σ B)
          + (itoIntegralAgainstCLM hB T hBmeas (stockVol hB hBmeas hBcont T S_0 σ) ψ :
              Ω → ℝ) ω := by
  refine ⟨fun t ht ↦ (pricePath_stockVol_ae_eq hB hBmeas hBcont T S_0 σ ht).trans
    (.of_forall fun ω ↦ (exp_neg_mul_pathAssets S_0 r σ t ω).symm), ?_⟩
  exact Contract.exists_unique_hedge_in_price hB hBmeas hBcont T
    (stockVol hB hBmeas hBcont T S_0 σ) (stockVol_ne_zero hB hBmeas hBcont T hS₀ hσ) hc
    (D := fun u _ ↦ Real.exp (-r * u)) (X := pathAssets S_0 r σ B) (fun _ ↦ measurable_const)
    (measurable_pathAssets_natFiltration hBmeas S_0 r σ) hobs hdates hL2

/-- **The Black–Scholes call is replicated by a unique holding in the stock, at the Black–Scholes
price.** The discounted payoff of `europeanCall K T` on the stock is `bsV K r σ S₀ T + ∫₀ᵀ ψ dS̃`
almost surely for a unique holding `ψ` in the price `S₀ + (stockVol●B)`, which is the discounted
stock at every `t ≤ T`. That `ψ` is the delta `Φ(d₁)` is `europeanCall_hedge_in_stock_eq_delta`. -/
theorem europeanCall_hedge_in_stock (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) {S_0 K r σ : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) :
    (∀ t : ℝ≥0, t ≤ T →
      MarketCompletenessInPrice.pricePath hB T hBmeas S_0 (stockVol hB hBmeas hBcont T S_0 σ) t
        =ᵐ[μ] fun ω ↦ Real.exp (-r * t) * pathAssets S_0 r σ B () t ω) ∧
    ∃! ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas (stockVol hB hBmeas hBcont T S_0 σ)),
      (fun ω ↦ (europeanCall K T).pathPV (fun u ↦ Real.exp (-r * u))
          (scenarioAt (pathAssets S_0 r σ B) ω)) =ᵐ[μ]
        fun ω ↦ bsV K r σ S_0 T
          + (itoIntegralAgainstCLM hB T hBmeas (stockVol hB hBmeas hBcont T S_0 σ) ψ :
              Ω → ℝ) ω := by
  have hfix : (europeanCall K T).FixedDated := by simp [europeanCall, Contract.FixedDated]
  have hobs : ∀ p ∈ (europeanCall K T).obsList, p.2 ≤ T := by
    simp [europeanCall, europeanCallPayoff, Contract.obsList, Payoff.obsList]
  have hdates : ∀ t ∈ (europeanCall K T).dates, t ≤ T := by
    simp [europeanCall, Contract.dates]
  obtain ⟨h1, h2⟩ := exists_unique_hedge_in_stock hB hBmeas hBcont T hS₀ hσ.ne' hfix hobs hdates
    (memLp_two_europeanCall_pathPV hB hBmeas hT hS₀ hK hσ)
  exact ⟨h1, by rwa [value_europeanCall_pathAssets hB hT hS₀ hK hσ] at h2⟩

end MathFin.Contracts.BlackScholes
