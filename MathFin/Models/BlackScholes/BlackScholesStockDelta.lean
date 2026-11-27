/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.BlackScholes.BlackScholesHedge
public import MathFin.Models.BlackScholes.BlackScholesSelfFinancing
public import MathFin.Models.BlackScholes.BlackScholesStockHedge

/-!
# The holding that replicates the Black–Scholes call in the stock is the delta

`europeanCall_hedge_in_stock` (`BlackScholesStockHedge`) gives a unique holding `ψ` in the
discounted stock, in the `L²` integral against `stockVol`, whose terminal wealth is the call's
discounted payoff at initial wealth `bsV`. `europeanCall_deltaHedge` (`BlackScholesHedge`) gives
the delta hedge in the localised integral `predItoIntegral`, up to every `T' < T`. This file joins
the two: `ψ` is the delta `Φ(d₁(S_t, T − t))` (`hedgeDelta`), almost everywhere for the bracket
measure of the stock.

The route is the one the integrals dictate.

* The delta hedge integrand `Δ σ S̃` is predictable, and bounded in absolute value by the
  volatility `σ S̃` of the stock, so it is square-integrable on every `(0, τ] × Ω`
  (`memLp_two_deltaHedgeIntegrand`) and its paths are continuous on `[0, T']` for `T' < T`
  (`continuousOn_deltaHedgeIntegrand`). The agreement `ae_predItoIntegral_eq_itoProcessCLM` and the
  horizon consistency `itoProcessCLM_toLp_eq_itoIntegralCLM` turn the identity of
  `europeanCall_deltaHedge` at `T'` into one in the `L²` Itô process of its class at horizon `T`
  (`europeanCall_deltaHedge_eq_itoProcessCLM`).
* Let `T' → T`. The discounted call price tends to the discounted payoff almost surely
  (`tendsto_hedge_europeanCall_payoff`), and the `L²` Itô process is `L²`-continuous in time with
  value the terminal integral at `T` (`itoIntegralProcessGen_l2_continuous`,
  `itoProcessCLM_terminal_eq`). Almost sure and in-measure limits agree
  (`tendstoInMeasure_ae_unique`), so the payoff is `bsV` plus the terminal integral of the delta
  hedge integrand (`europeanCall_payoff_eq_value_add_itoIntegral`).
* A holding `ψ` with the same terminal wealth has `ψ φ` and the class of the delta hedge
  integrand equal, by injectivity of the Itô isometry, hence `ψ = Δ` wherever
  `φ = σ S̃ ≠ 0` (`ae_eq_hedgeDelta_of_replicates`).

## Main definitions

* `deltaHedgeLp` is the class of the delta hedge integrand in `L²(trimMeasure τ)`.

## Main results

* `BlackScholes.europeanCall_payoff_eq_value_add_itoIntegral`: the discounted payoff of the call is
  `bsV` plus the `L²` Itô integral over `[0, T]` of the delta hedge integrand, almost surely.
* `BlackScholes.europeanCall_hedge_in_stock_eq_delta`: the replicating holding in the stock exists,
  is unique, and is the delta `Φ(d₁(S_t, T − t))` almost everywhere for the bracket measure.

## References

* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 4.5
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]

## Tags

delta hedging, replication, Black–Scholes model, stochastic integral against price,
bracket measure, MSC 91G20, MSC 60H05, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open MathFin ItoIntegralCLM ItoIntegralAgainstMartingale ItoIntegralL2 ItoIntegralLocalised
  ItoIntegralProcessGeneral LpMulIsometry
open scoped NNReal

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The delta hedge integrand as an integrand in `L²` -/

/-- **The hedge integrand is the delta times the volatility of the discounted stock**:
`σ e^{−rs} S_s Φ(d₁) = Φ(d₁) · σ S̃_s`, with `S̃ = pathAssets S₀ 0 σ B`. -/
theorem deltaHedgeIntegrand_eq_hedgeDelta_mul (K r σ S_0 T : ℝ) (s : ℝ≥0) (ω : Ω) :
    deltaHedgeIntegrand K r σ S_0 T s (B s ω)
      = hedgeDelta K r σ S_0 T B s ω * (σ * pathAssets S_0 0 σ B () s ω) := by
  have h := exp_neg_mul_pathAssets (B := B) S_0 r σ s ω
  simp only [pathAssets_eq_gbmValue, neg_mul] at h
  simp only [deltaHedgeIntegrand, hedgeDelta, pathAssets_eq_gbmValue]
  linear_combination (σ * Phi (bsd1 (gbmValue S_0 r σ s (B s ω)) K r σ (T - s))) * h

/-- The hedge integrand is dominated by the volatility of the discounted stock: the delta is in
`[0, 1]`. -/
theorem abs_deltaHedgeIntegrand_le (K r σ S_0 T : ℝ) (s : ℝ≥0) (ω : Ω) :
    |deltaHedgeIntegrand K r σ S_0 T s (B s ω)| ≤ |σ * pathAssets S_0 0 σ B () s ω| := by
  have h0 : 0 ≤ hedgeDelta K r σ S_0 T B s ω := Phi_nonneg _
  have h1 : hedgeDelta K r σ S_0 T B s ω ≤ 1 := Phi_le_one _
  rw [deltaHedgeIntegrand_eq_hedgeDelta_mul (B := B) K r σ S_0 T s ω, abs_mul, abs_of_nonneg h0]
  exact mul_le_of_le_one_left (abs_nonneg _) h1

/-- **The delta hedge integrand is square-integrable** on `(0, τ] × Ω` for every `τ`: it is
predictable and dominated by the volatility `σ S̃` of the stock
(`memLp_two_diffusion_pathAssets`). -/
theorem memLp_two_deltaHedgeIntegrand (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (τ : ℝ≥0)
    (K r σ S_0 T : ℝ) :
    MemLp (Function.uncurry fun (s : ℝ≥0) ω ↦ deltaHedgeIntegrand K r σ S_0 T s (B s ω)) 2
      (trimMeasure (μ := μ) τ hBmeas) :=
  (memLp_two_diffusion_pathAssets hB hBmeas hBcont τ S_0 0 σ).of_le
    (deltaHedgeIntegrand_isStronglyPredictable hBmeas hBcont K r σ S_0 T).aestronglyMeasurable
    (ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact abs_deltaHedgeIntegrand_le (B := B) K r σ S_0 T z.1 z.2)

/-- **The class of the delta hedge integrand** in `L²(trimMeasure τ)`: `σ e^{−rs} S_s Φ(d₁(S_s,
T − s))`, the integrand of the delta hedge, as an integrand of the `L²` Itô integral. -/
noncomputable def deltaHedgeLp (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (τ : ℝ≥0) (K r σ S_0 T : ℝ) :
    Lp ℝ 2 (trimMeasure (μ := μ) τ hBmeas) :=
  (memLp_two_deltaHedgeIntegrand hB hBmeas hBcont τ K r σ S_0 T).toLp _

/-- The class `deltaHedgeLp` is the delta hedge integrand almost everywhere. -/
theorem deltaHedgeLp_ae_eq (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (τ : ℝ≥0) (K r σ S_0 T : ℝ) :
    deltaHedgeLp hB hBmeas hBcont τ K r σ S_0 T =ᵐ[trimMeasure (μ := μ) τ hBmeas]
      Function.uncurry fun (s : ℝ≥0) ω ↦ deltaHedgeIntegrand K r σ S_0 T s (B s ω) :=
  MemLp.coeFn_toLp _

/-- **The delta hedge integrand has continuous paths up to every `T' < T`**: after the smooth cap
of time `timeCap T' T` it is jointly continuous (`continuous_deltaHedgeIntegrand_comp`), and the
cap is the identity on `[0, T']`. -/
theorem continuousOn_deltaHedgeIntegrand (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {K S_0 r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hS₀ : 0 < S_0) {T T' : ℝ≥0} (hT' : T' < T)
    (ω : Ω) :
    ContinuousOn (fun s : ℝ≥0 ↦ deltaHedgeIntegrand K r σ S_0 T s (B s ω)) (Icc 0 T') := by
  have hT'' : (T' : ℝ) < T := NNReal.coe_lt_coe.2 hT'
  have hcomp := continuous_deltaHedgeIntegrand_comp (K := K) (r := r) (σ := σ) (S₀ := S_0)
    (T := (T : ℝ)) (ψ := timeCap (T' : ℝ) T) hK hσ hS₀ (contDiff_timeCap 1).continuous
    (timeCap_lt hT'')
  refine ((hcomp.comp (NNReal.continuous_coe.prodMk (hBcont ω))).continuousOn).congr fun s hs ↦ ?_
  show deltaHedgeIntegrand K r σ S_0 T s (B s ω)
    = deltaHedgeIntegrand K r σ S_0 T (timeCap (T' : ℝ) T s) (B s ω)
  rw [timeCap_of_le hT'' (NNReal.coe_le_coe.2 hs.2)]

/-! ### The delta hedge identity in the `L²` Itô process -/

/-- **The delta hedge in the `L²` Itô process.** For `T' < T`, almost surely the discounted call
price at `T'` is `bsV K r σ S₀ T` plus the value at `T'` of the `L²` Itô process, at horizon `T`,
of the class of the delta hedge integrand. This is `europeanCall_deltaHedge` at `t = T'`, with the
localised integral `predItoIntegral` replaced by the `L²` one
(`ae_predItoIntegral_eq_itoProcessCLM`, then the horizon `T'` to `T` by
`itoProcessCLM_toLp_eq_itoIntegralCLM`). -/
theorem europeanCall_deltaHedge_eq_itoProcessCLM (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) {S_0 K r σ : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) {T' : ℝ≥0}
    (hT' : T' < T) :
    (fun ω ↦ Real.exp (-(r * T')) * bsV K r σ (pathAssets S_0 r σ B () T' ω) (T - T'))
      =ᵐ[μ] fun ω ↦ bsV K r σ S_0 T
        + (itoProcessCLM hB T T' hBmeas
            (deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T) : Ω → ℝ) ω := by
  have hpred := deltaHedgeIntegrand_isStronglyPredictable hBmeas hBcont K r σ S_0 (T : ℝ)
  have hA := ae_predItoIntegral_eq_itoProcessCLM hB T' hBmeas hBcont hpred
    (ae_of_all _ fun ω ↦ continuousOn_deltaHedgeIntegrand hBcont hK hσ hS₀ hT' ω)
    (deltaHedgeLp hB hBmeas hBcont T' K r σ S_0 T)
    (deltaHedgeLp_ae_eq hB hBmeas hBcont T' K r σ S_0 T) (le_refl T')
  have hLp : itoProcessCLM hB T' T' hBmeas
        (deltaHedgeLp hB hBmeas hBcont T' K r σ S_0 T)
      = itoProcessCLM hB T T' hBmeas
        (deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T) :=
    (itoProcessCLM_terminal_eq hB T' hBmeas _).trans
      (itoProcessCLM_toLp_eq_itoIntegralCLM hB T hBmeas hT'.le hpred
        (memLp_two_deltaHedgeIntegrand hB hBmeas hBcont T K r σ S_0 T)
        (memLp_two_deltaHedgeIntegrand hB hBmeas hBcont T' K r σ S_0 T)).symm
  filter_upwards [europeanCall_deltaHedge hB hBmeas hBcont hT hS₀ hK hσ T' hT', hA] with ω h1 h2
  have h3 : predItoIntegral (μ := μ) T' hBmeas hpred T' ω
      = (itoProcessCLM hB T T' hBmeas
        (deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T) : Ω → ℝ) ω := by
    rw [← hLp]
    exact h2
  rw [h1 T' ⟨zero_le, le_rfl⟩, value_europeanCall_pathAssets hB hT hS₀ hK hσ, h3]

/-! ### The payoff is the value plus the terminal integral of the delta hedge -/

/-- **The call's discounted payoff is its price plus the `L²` Itô integral of the delta hedge.**
Almost surely, the discounted payoff of `europeanCall K T` on the Black–Scholes stock is
`bsV K r σ S₀ T + ∫₀ᵀ Δ σ S̃ dB`, the integral being the terminal `L²` Itô integral of the class of
the delta hedge integrand `σ e^{−rs} S_s Φ(d₁(S_s, T − s))`. At `T' < T` this is
`europeanCall_deltaHedge_eq_itoProcessCLM`; the passage `T' → T` combines the almost sure limit
`tendsto_hedge_europeanCall_payoff` with the `L²`-continuity of the Itô process in time, the limits
agreeing by `tendstoInMeasure_ae_unique`. -/
theorem europeanCall_payoff_eq_value_add_itoIntegral (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) {S_0 K r σ : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) :
    (fun ω ↦ (europeanCall K T).pathPV (fun u ↦ Real.exp (-r * u))
        (scenarioAt (pathAssets S_0 r σ B) ω))
      =ᵐ[μ] fun ω ↦ bsV K r σ S_0 T
        + (itoIntegralCLM hB T hBmeas
            (deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T) : Ω → ℝ) ω := by
  obtain ⟨u, -, hu, hlim⟩ := exists_seq_strictMono_tendsto' (NNReal.coe_pos.1 hT)
  have hlim' : Tendsto u atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n ↦ (hu n).2⟩
  -- the discounted call prices, less the price, are the `L²` Itô processes of the delta hedge
  have h1 (n : ℕ) : (fun ω ↦ Real.exp (-(r * u n)) * bsV K r σ (pathAssets S_0 r σ B () (u n) ω)
        (T - u n) - bsV K r σ S_0 T)
      =ᵐ[μ] ⇑(itoProcessCLM hB T (u n) hBmeas
        (deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T)) := by
    filter_upwards [europeanCall_deltaHedge_eq_itoProcessCLM hB hBmeas hBcont hT hS₀ hK hσ
      (hu n).2] with ω h
    rw [h]
    ring
  -- they converge almost surely to the payoff less the price ...
  have hae : TendstoInMeasure μ (fun n ω ↦ Real.exp (-(r * u n))
        * bsV K r σ (pathAssets S_0 r σ B () (u n) ω) (T - u n) - bsV K r σ S_0 T) atTop
      fun ω ↦ (europeanCall K T).pathPV (fun u ↦ Real.exp (-r * u))
        (scenarioAt (pathAssets S_0 r σ B) ω) - bsV K r σ S_0 T :=
    tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (Lp.aestronglyMeasurable (itoProcessCLM hB T (u n) hBmeas
        (deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T))).congr (h1 n).symm)
      (ae_of_all _ fun ω ↦
        ((tendsto_hedge_europeanCall_payoff hK hσ hS₀ T (hBcont ω).continuousAt).comp
          hlim').sub_const _)
  -- ... and in `L²` to the terminal integral
  have hL2 : TendstoInMeasure μ
      (fun n ↦ ⇑(itoProcessCLM hB T (u n) hBmeas
        (deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T))) atTop
      ⇑(itoIntegralCLM hB T hBmeas (deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T)) := by
    rw [← itoProcessCLM_terminal_eq hB T hBmeas (deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T)]
    exact tendstoInMeasure_of_tendsto_Lp
      (((itoIntegralProcessGen_l2_continuous hB T hBmeas
        (deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T)).tendsto T).comp hlim)
  filter_upwards [tendstoInMeasure_ae_unique hae (hL2.congr_left fun n ↦ (h1 n).symm)] with ω h
  linarith

/-! ### The holding is the delta -/

/-- **A holding with the call's terminal wealth is the delta.** If `ψ` replicates the discounted
payoff of `europeanCall K T` at initial wealth `bsV` in the price `S₀ + (stockVol●B)`, then `ψ` is
almost everywhere, for the bracket measure of `stockVol`, the delta process
`Φ(d₁(S_t, T − t))`. The holding times the volatility `φ = σ S̃` and the class of the delta hedge
integrand have the same terminal integral, hence are equal (the Itô isometry is injective); and
the hedge integrand is the delta times `φ`, with `φ ≠ 0`. -/
theorem ae_eq_hedgeDelta_of_replicates (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) {S_0 K r σ : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ)
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas (stockVol hB hBmeas hBcont T S_0 σ)))
    (hψ : (fun ω ↦ (europeanCall K T).pathPV (fun u ↦ Real.exp (-r * u))
          (scenarioAt (pathAssets S_0 r σ B) ω)) =ᵐ[μ]
        fun ω ↦ bsV K r σ S_0 T
          + (itoIntegralAgainstCLM hB T hBmeas (stockVol hB hBmeas hBcont T S_0 σ) ψ :
              Ω → ℝ) ω) :
    ⇑ψ =ᵐ[bracketMeasure (μ := μ) T hBmeas (stockVol hB hBmeas hBcont T S_0 σ)]
      fun z ↦ hedgeDelta K r σ S_0 T B z.1 z.2 := by
  have hφm : Measurable ⇑(stockVol hB hBmeas hBcont T S_0 σ) :=
    (Lp.stronglyMeasurable (stockVol hB hBmeas hBcont T S_0 σ)).measurable
  -- the two terminal integrals agree
  have h1 : itoIntegralCLM hB T hBmeas (mulLI (trimMeasure (μ := μ) T hBmeas) hφm ψ)
      = itoIntegralCLM hB T hBmeas (deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T) := by
    refine Lp.ext ?_
    have hA := itoIntegralAgainstCLM_apply (hB := hB) T hBmeas
      (stockVol hB hBmeas hBcont T S_0 σ) ψ
    filter_upwards [hψ, europeanCall_payoff_eq_value_add_itoIntegral hB hBmeas hBcont hT hS₀ hK
      hσ] with ω h h'
    rw [hA] at h
    exact add_left_cancel (h.symm.trans h')
  -- so `φ ψ` is the class of the hedge integrand
  have h2 : mulLI (trimMeasure (μ := μ) T hBmeas) hφm ψ
      = deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T := by
    have h := itoIntegralCLM_norm hB T hBmeas
      (mulLI (trimMeasure (μ := μ) T hBmeas) hφm ψ
        - deltaHedgeLp hB hBmeas hBcont T K r σ S_0 T)
    rw [map_sub, h1, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (norm_eq_zero.1 h.symm)
  -- hence `ψ = Δ` wherever `φ ≠ 0`, which is `trimMeasure`-almost everywhere
  have h3 : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas), (ψ : ℝ≥0 × Ω → ℝ) z
      = hedgeDelta K r σ S_0 T B z.1 z.2 := by
    filter_upwards [coeFn_mulLI (trimMeasure (μ := μ) T hBmeas) hφm ψ,
      deltaHedgeLp_ae_eq hB hBmeas hBcont T K r σ S_0 T,
      stockVol_ae_eq hB hBmeas hBcont T S_0 σ,
      stockVol_ne_zero hB hBmeas hBcont T hS₀ hσ.ne'] with z hz1 hz2 hz3 hz4
    rw [h2] at hz1
    refine mul_left_cancel₀ hz4 ?_
    rw [← hz1, hz2, hz3]
    exact (deltaHedgeIntegrand_eq_hedgeDelta_mul (B := B) K r σ S_0 T z.1 z.2).trans
      (mul_comm _ _)
  have hac : bracketMeasure (μ := μ) T hBmeas (stockVol hB hBmeas hBcont T S_0 σ)
      ≪ trimMeasure (μ := μ) T hBmeas :=
    withDensity_absolutelyContinuous _ _
  exact h3.filter_mono hac.ae_le

/-- **In Black–Scholes the call is replicated by the delta, held in the stock.** Let `B` be a
Brownian motion with continuous paths, `T > 0`, and `S₀, K, σ > 0`. There is a unique holding `ψ`
in the price `S₀ + (stockVol●B)` — the discounted stock — such that the discounted payoff of
`europeanCall K T` is `bsV K r σ S₀ T + ∫₀ᵀ ψ dS̃` almost surely, and it is the delta:
`ψ_t = Φ(d₁(S_t, T − t))` for the bracket measure of the stock, that is almost everywhere on
`(0, T] × Ω` for the predictable measure weighted by `(σ S̃)²`.

The `L²` class `ψ` is only defined up to that measure, and so is the identification: it is not a
pathwise statement about the delta at each `(t, ω)`. -/
theorem europeanCall_hedge_in_stock_eq_delta (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) {S_0 K r σ : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) :
    ∃! ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas (stockVol hB hBmeas hBcont T S_0 σ)),
      (fun ω ↦ (europeanCall K T).pathPV (fun u ↦ Real.exp (-r * u))
          (scenarioAt (pathAssets S_0 r σ B) ω)) =ᵐ[μ]
        (fun ω ↦ bsV K r σ S_0 T
          + (itoIntegralAgainstCLM hB T hBmeas (stockVol hB hBmeas hBcont T S_0 σ) ψ :
              Ω → ℝ) ω) ∧
      ⇑ψ =ᵐ[bracketMeasure (μ := μ) T hBmeas (stockVol hB hBmeas hBcont T S_0 σ)]
        fun z ↦ hedgeDelta K r σ S_0 T B z.1 z.2 := by
  obtain ⟨-, ψ, hψ, huniq⟩ := europeanCall_hedge_in_stock hB hBmeas hBcont hT hS₀ hK hσ
  exact ⟨ψ, ⟨hψ, ae_eq_hedgeDelta_of_replicates hB hBmeas hBcont hT hS₀ hK hσ ψ hψ⟩,
    fun ψ' h ↦ huniq ψ' h.1⟩

end MathFin.Contracts.BlackScholes
