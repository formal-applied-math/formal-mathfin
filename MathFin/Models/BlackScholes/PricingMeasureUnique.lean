/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.BlackScholes.Market
public import MathFin.Probability.Brownian.MartingaleMeasureUniqueness
public import MathFin.Probability.Brownian.Ito.ItoFormulaGBM

/-!
# Every pricing measure of the Black–Scholes market prices the call at the Black–Scholes formula

The Girsanov measure `Q*` of the market price of risk `θ = (m − r)/σ` is a pricing measure of the
Black–Scholes market (`isPricingMeasure_constGirsanovMeasure`). This file shows it is the only one
among the measures whose density with respect to `Q*` is square-integrable: such a pricing measure
agrees with `Q*` on `𝓕_T`, hence prices every `𝓕_T`-measurable payoff, and in particular the
European call, as `Q*` does, at `S₀ Φ(d₁) − K e^{−rT} Φ(d₂)`.

## The argument

Under `Q*` the process `W*_u = W_u + θ min(u, H)` is a pre-Brownian motion with the same natural
filtration as `W` (`isPreBrownianReal_girsanovDriver`, `natFiltration_girsanovDriver`): it agrees
for each `u` almost surely with `B^θ`, which is Brownian under `Q*`. On `[0, T]`, `T ≤ H`, the
deflated asset is pointwise `S₀ exp(σ W*_u − σ²u/2)` (`deflated_market_eq_girsanovDriver`), the
discounted geometric Brownian motion of the driver `W*`, whose increment is the Itô integral of
`σ S̃` (`discountedGBM_eq_itoIntegral`). The abstract uniqueness theorem
`trim_eq_of_martingale_withDensity` for martingale measures on a Brownian filtration then applies.

## Main results

* `BlackScholes.trim_eq_of_isPricingMeasure_withDensity`: a pricing measure `Q = D·Q*` of the
  market with `D ∈ L²(Q*)` agrees with `Q*` on `𝓕_T`.
* `BlackScholes.price_europeanCall_of_isPricingMeasure_withDensity`: it prices the European call at
  the Black–Scholes formula.

## References

* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 5.4
* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 9.1.8

## Tags

Black–Scholes market, uniqueness of the risk-neutral measure, pricing measure, Girsanov theorem,
martingale representation, European call, MSC 91G20, MSC 60H05, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal
open MathFin ItoIntegralL2 ItoIntegralProcessContinuousModification

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- **The driver of the Girsanov measure**: `W*_u = W_u + θ min(u, H)`. Under the Girsanov measure
`Q*` of the constant price of risk `θ` at the horizon `H` it is a Brownian motion; the drift stops
at the horizon, where `Z_H` stops. -/
def girsanovDriver (W : ℝ≥0 → Ω → ℝ) (θ : ℝ) (H : ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ :=
  W u ω + θ * (min u H : ℝ≥0)

lemma measurable_girsanovDriver (hWmeas : ∀ t, Measurable (W t)) (θ : ℝ) (H u : ℝ≥0) :
    Measurable (girsanovDriver W θ H u) :=
  (hWmeas u).add_const _

omit mΩ in
lemma continuous_girsanovDriver (hWcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ W s ω) (θ : ℝ) (H : ℝ≥0)
    (ω : Ω) : Continuous fun u ↦ girsanovDriver W θ H u ω :=
  (hWcont ω).add (continuous_const.mul (NNReal.continuous_coe.comp (continuous_id.min
    continuous_const)))

/-- The driver and `W` generate the same filtration: it is a deterministic shift at each time. -/
lemma natFiltration_girsanovDriver (hWmeas : ∀ t, Measurable (W t)) (θ : ℝ) (H : ℝ≥0) :
    natFiltration (measurable_girsanovDriver hWmeas θ H) = natFiltration hWmeas := by
  refine le_antisymm (fun t ↦ ?_) fun t ↦ ?_
  · refine iSup₂_le fun j hj ↦ Measurable.comap_le ?_
    exact ((stronglyAdapted_natFiltration hWmeas j).mono
      ((natFiltration hWmeas).mono hj)).measurable.add_const _
  · refine iSup₂_le fun j hj ↦ Measurable.comap_le ?_
    have := ((stronglyAdapted_natFiltration (measurable_girsanovDriver hWmeas θ H) j).mono
      ((natFiltration (measurable_girsanovDriver hWmeas θ H)).mono hj)).measurable.sub_const
      (θ * (min j H : ℝ≥0))
    simpa [girsanovDriver] using this

variable (hW : IsPreBrownianReal W μ) (hWmeas : ∀ t, Measurable (W t))

/-- `B^θ` is, at every date, the driver: for `u ≤ H` by `constBtheta_drift_ae`, and past `H` the
drift of `B^θ` is frozen (`driftContinuousMod_of_ge`) at its value at `H`. -/
lemma constBtheta_ae_eq_girsanovDriver (θ : ℝ) (H u : ℝ≥0) :
    constBtheta (μ := μ) hWmeas θ H u =ᵐ[μ] girsanovDriver W θ H u := by
  rcases le_total u H with huH | hHu
  · filter_upwards [constBtheta_drift_ae (μ := μ) hWmeas θ H huH] with ω hω
    rw [hω, girsanovDriver, min_eq_left huH]
  · filter_upwards [constBtheta_drift_ae (μ := μ) hWmeas θ H le_rfl] with ω hω
    have hfrozen := driftContinuousMod_of_ge H hWmeas
      (processToLpPredictable (μ := μ) H hWmeas (isStronglyPredictable_const hWmeas θ)
        (fun _ _ ↦ le_rfl)) hHu ω
    simp only [constBtheta, BthetaPred] at hω ⊢
    rw [hfrozen, girsanovDriver, min_eq_right hHu]
    linarith

include hW in
/-- **The driver is a pre-Brownian motion under the Girsanov measure.** -/
theorem isPreBrownianReal_girsanovDriver (θ : ℝ) (H : ℝ≥0) :
    IsPreBrownianReal (girsanovDriver W θ H) (constGirsanovMeasure hW hWmeas θ H) :=
  (isPreBrownianReal_constBtheta hW hWmeas θ H).congr fun u ↦
    (withDensity_absolutelyContinuous _ _).ae_le (constBtheta_ae_eq_girsanovDriver (μ := μ) hWmeas θ H u)

variable {S_0 m r σ : ℝ}

omit [IsProbabilityMeasure μ] in
/-- On `[0, H]` the deflated asset is `S₀ exp(σ W*_u − σ²u/2)`, the discounted geometric Brownian
motion of the driver: the drift `m − r` is `σθ`. -/
lemma deflated_market_eq_girsanovDriver (hσ : σ ≠ 0) {H u : ℝ≥0} (hu : u ≤ H) (ω : Ω) :
    (market μ hWmeas S_0 m r σ).deflated () u ω
      = S_0 * Real.exp (-(σ ^ 2 / 2) * u + σ * girsanovDriver W ((m - r) / σ) H u ω) := by
  rw [deflated_market, girsanovDriver, min_eq_left hu]
  congr 2
  field_simp
  ring

include hW in
/-- **Uniqueness of the pricing measure with a square-integrable density.** A pricing measure `Q`
of the Black–Scholes market up to `T ≤ H` whose density with respect to the Girsanov measure
`Q*` of `θ = (m − r)/σ` is a nonnegative `D ∈ L²(Q*)` agrees with `Q*` on `𝓕_T`.

The deflated asset is the discounted geometric Brownian motion of the Brownian driver `W*` of
`Q*`, so `trim_eq_of_martingale_withDensity` applies. A density that is merely in `L²(μ)`, or
that is not square-integrable under `Q*`, is not covered. -/
theorem trim_eq_of_isPricingMeasure_withDensity
    (hWcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ W s ω) (hS₀ : 0 < S_0) (hσ : 0 < σ) {T H : ℝ≥0}
    (hTH : T ≤ H) {Q : Measure Ω} (hQ : (market μ hWmeas S_0 m r σ).IsPricingMeasure T Q)
    (D : Lp ℝ 2 (constGirsanovMeasure hW hWmeas ((m - r) / σ) H))
    (hD : ∀ᵐ ω ∂(constGirsanovMeasure hW hWmeas ((m - r) / σ) H), 0 ≤ D ω)
    (hQD : Q = (constGirsanovMeasure hW hWmeas ((m - r) / σ) H).withDensity
      fun ω ↦ ENNReal.ofReal (D ω)) :
    Q.trim ((market μ hWmeas S_0 m r σ).𝓕.le T)
      = (constGirsanovMeasure hW hWmeas ((m - r) / σ) H).trim
          ((market μ hWmeas S_0 m r σ).𝓕.le T) := by
  have : IsProbabilityMeasure (constGirsanovMeasure hW hWmeas ((m - r) / σ) H) :=
    constGirsanovMeasure_isProbabilityMeasure hW hWmeas _ H
  have : IsProbabilityMeasure Q := hQ.isProb
  have hmeas := measurable_girsanovDriver hWmeas ((m - r) / σ) H
  have hWs := isPreBrownianReal_girsanovDriver hW hWmeas ((m - r) / σ) H
  have hfil := natFiltration_girsanovDriver hWmeas ((m - r) / σ) H
  set M := market μ hWmeas S_0 m r σ with hM
  let X : ℝ≥0 → Ω → ℝ := fun t ↦ M.deflated () (min t T)
  have hXQs : Martingale X (natFiltration hmeas) (constGirsanovMeasure hW hWmeas ((m - r) / σ) H) := by
    rw [hfil]
    exact (isPricingMeasure_constGirsanovMeasure hW hWmeas hσ.ne' hTH).martingale ()
  have hXQ : Martingale (fun t ↦ X (min t T)) (natFiltration hmeas) Q := by
    have h : Martingale (fun t ↦ M.deflated () (min t T)) (natFiltration hWmeas) Q :=
      hQ.martingale ()
    rw [hfil]
    simpa [X, min_assoc] using h
  obtain ⟨ψ, hψname, hψ⟩ := discountedGBM_eq_itoIntegral hWs hmeas
    (continuous_girsanovDriver hWcont ((m - r) / σ) H) T S_0 σ
  have hXT (ω : Ω) : X T ω
      = S_0 * Real.exp (-(σ ^ 2 / 2) * T + σ * girsanovDriver W ((m - r) / σ) H T ω) := by
    simp only [X, min_self]
    exact deflated_market_eq_girsanovDriver hWmeas hσ.ne' hTH ω
  have hX0 (ω : Ω) : X 0 ω = S_0 * Real.exp (σ * girsanovDriver W ((m - r) / σ) H 0 ω) := by
    have h := deflated_market_eq_girsanovDriver (μ := μ) (S_0 := S_0) (m := m) (r := r) hWmeas
      hσ.ne' (show (0 : ℝ≥0) ≤ H from bot_le) ω
    simpa [X] using h
  have hψ' : (fun ω ↦ X T ω - X 0 ω) =ᵐ[constGirsanovMeasure hW hWmeas ((m - r) / σ) H] ItoIntegralCLM.itoIntegralCLM hWs T hmeas ψ := by
    filter_upwards [hψ] with ω h
    rw [hXT, hX0]
    exact h
  have hψ0 : ∀ᵐ z ∂(ItoIntegralCLM.trimMeasure (μ := constGirsanovMeasure hW hWmeas ((m - r) / σ) H) T hmeas), ψ z ≠ 0 := by
    filter_upwards [hψname] with z hz
    rw [hz]
    exact (mul_pos hσ (mul_pos hS₀ (Real.exp_pos _))).ne'
  have hX0L2 : MemLp (X 0) 2 (constGirsanovMeasure hW hWmeas ((m - r) / σ) H) := by
    refine (memLp_const S_0).ae_eq ?_
    filter_upwards [hWs.eval_zero_ae_eq_zero] with ω h
    rw [hX0, h]
    simp
  have key := trim_eq_of_martingale_withDensity hWs hmeas (continuous_girsanovDriver hWcont ((m - r) / σ) H)
    T hXQs ψ hψ' hψ0 hX0L2 D hD hQD hXQ
  have hgen : ∀ F : Filtration ℝ≥0 mΩ, F = natFiltration hmeas →
      Q.trim (F.le T) = (constGirsanovMeasure hW hWmeas ((m - r) / σ) H).trim (F.le T) := by
    rintro F rfl
    exact key
  exact hgen _ hfil.symm

include hW in
/-- **Every pricing measure with a square-integrable density prices the European call at the
Black–Scholes formula.** A pricing measure `Q` of the Black–Scholes market up to `T ≤ H` whose
density with respect to the Girsanov measure `Q*` of `θ = (m − r)/σ` is a nonnegative
`D ∈ L²(Q*)` prices the call at `S₀ Φ(d₁) − K e^{−rT} Φ(d₂)`: it agrees with `Q*` on `𝓕_T`
(`trim_eq_of_isPricingMeasure_withDensity`), and the discounted call payoff is `𝓕_T`-measurable,
so its `Q`-integral is its `Q*`-integral (`price_europeanCall_constGirsanovMeasure`). -/
theorem price_europeanCall_of_isPricingMeasure_withDensity
    (hWcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ W s ω) {K : ℝ} {T H : ℝ≥0} (hTH : T ≤ H)
    (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < (T : ℝ)) {Q : Measure Ω}
    (hQ : (market μ hWmeas S_0 m r σ).IsPricingMeasure T Q)
    (D : Lp ℝ 2 (constGirsanovMeasure hW hWmeas ((m - r) / σ) H))
    (hD : ∀ᵐ ω ∂(constGirsanovMeasure hW hWmeas ((m - r) / σ) H), 0 ≤ D ω)
    (hQD : Q = (constGirsanovMeasure hW hWmeas ((m - r) / σ) H).withDensity
      fun ω ↦ ENNReal.ofReal (D ω)) :
    (market μ hWmeas S_0 m r σ).price Q (europeanCall K T)
      = S_0 * Phi (bsd1 S_0 K r σ T) - K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) := by
  have htrim : Q.trim ((natFiltration hWmeas).le T)
      = (constGirsanovMeasure hW hWmeas ((m - r) / σ) H).trim ((natFiltration hWmeas).le T) :=
    trim_eq_of_isPricingMeasure_withDensity hW hWmeas hWcont hS₀ hσ hTH hQ D hD hQD
  set F : ℝ → ℝ := fun x ↦
    Real.exp (-r * T) * max (S_0 * Real.exp ((m - σ ^ 2 / 2) * T + σ * x) - K) 0 with hF
  have hprice (P : Measure Ω) :
      (market μ hWmeas S_0 m r σ).price P (europeanCall K T) = ∫ ω, F (W T ω) ∂P := by
    simp [price_market, europeanCall, europeanCallPayoff, Contract.value_pay, Payoff.eval,
      scenarioAt, pathAssets, hF]
  have hFm : StronglyMeasurable[natFiltration hWmeas T] fun ω ↦ F (W T ω) :=
    (by fun_prop : Continuous F).comp_stronglyMeasurable (stronglyAdapted_natFiltration hWmeas T)
  rw [hprice, integral_trim ((natFiltration hWmeas).le T) hFm, htrim,
    ← integral_trim ((natFiltration hWmeas).le T) hFm, ← hprice]
  exact price_europeanCall_constGirsanovMeasure hW hWmeas hTH hS₀ hK hσ hT

/-! ### Bounded densities against the physical measure -/

section Bounded

open ItoIntegralCLM in
/-- The sliced integral of the squared constant integrand is `c²H`, on almost every path. -/
lemma ae_integral_sq_processToLpPredictable_const (c : ℝ) (H : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∫ s in Set.Ioc (0 : ℝ≥0) H,
      (processToLpPredictable (μ := μ) H hWmeas (isStronglyPredictable_const hWmeas c)
        (fun _ _ ↦ le_rfl) (s, ω)) ^ 2 ∂ItoIntegralL2.timeMeasure = c ^ 2 * H := by
  filter_upwards [processToLpPredictable_ae_slice (μ := μ) H hWmeas
    (isStronglyPredictable_const hWmeas c) (fun _ _ ↦ le_rfl)] with ω h
  have h3 : ∀ᵐ s ∂(ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) H)),
      (processToLpPredictable (μ := μ) H hWmeas (isStronglyPredictable_const hWmeas c)
        (fun _ _ ↦ le_rfl) (s, ω)) ^ 2 = c ^ 2 := h.mono fun s hs ↦ by rw [hs]
  rw [integral_congr_ae h3, setIntegral_const, smul_eq_mul, measureReal_def,
    ItoIntegralL2.timeMeasure_Ioc, ENNReal.toReal_ofReal (by simp), NNReal.coe_zero, sub_zero]
  ring

include hW in
/-- **The Doléans densities of `θ` and `−θ` multiply to a constant.** For the constant integrand
the Itô integral is odd and the bracket is `θ²H`, so `Z_H(θ)·Z_H(−θ) = exp(−θ²H)` almost surely. -/
lemma ae_mul_ZTpred_const_neg (θ : ℝ) (H : ℝ≥0) :
    ∀ᵐ ω ∂μ,
      ZTpred hW H hWmeas (isStronglyPredictable_const hWmeas θ) (fun _ _ ↦ le_rfl) ω
        * ZTpred hW H hWmeas (isStronglyPredictable_const hWmeas (-θ)) (fun _ _ ↦ le_rfl) ω
        = Real.exp (-(θ ^ 2 * H)) := by
  have hP : processToLpPredictable (μ := μ) H hWmeas (isStronglyPredictable_const hWmeas (-θ))
      (fun _ _ ↦ le_rfl)
      = -processToLpPredictable (μ := μ) H hWmeas (isStronglyPredictable_const hWmeas θ)
        (fun _ _ ↦ le_rfl) := by
    refine Lp.ext ?_
    filter_upwards [processToLpPredictable_coeFn (μ := μ) H hWmeas
        (isStronglyPredictable_const hWmeas (-θ)) (fun _ _ ↦ le_rfl),
      processToLpPredictable_coeFn (μ := μ) H hWmeas (isStronglyPredictable_const hWmeas θ)
        (fun _ _ ↦ le_rfl), Lp.coeFn_neg (processToLpPredictable (μ := μ) H hWmeas
          (isStronglyPredictable_const hWmeas θ) (fun _ _ ↦ le_rfl))] with z h1 h2 h3
    rw [h1, h3, Pi.neg_apply, h2]
    rfl
  filter_upwards [ae_integral_sq_processToLpPredictable_const (μ := μ) hWmeas θ H,
    ae_integral_sq_processToLpPredictable_const (μ := μ) hWmeas (-θ) H,
    Lp.coeFn_neg (ItoIntegralCLM.itoIntegralCLM hW H hWmeas
      (processToLpPredictable (μ := μ) H hWmeas (isStronglyPredictable_const hWmeas θ)
        (fun _ _ ↦ le_rfl)))] with ω h1 h2 h3
  simp only [ZTpred, contDoleansExp, itoIntPred]
  rw [h1, h2, ← Real.exp_add, hP, map_neg, h3]
  congr 1
  simp only [Pi.neg_apply]
  ring

include hW in
/-- **The inverse Doléans density is integrable.** `1/Z_H(θ) = exp(θ²H)·Z_H(−θ)` almost surely
(`ae_mul_ZTpred_const_neg`), and `Z_H(−θ)` is integrable. -/
lemma integrable_inv_ZTpred_const (θ : ℝ) (H : ℝ≥0) :
    Integrable (fun ω ↦
      (ZTpred hW H hWmeas (isStronglyPredictable_const hWmeas θ) (fun _ _ ↦ le_rfl) ω)⁻¹) μ := by
  obtain ⟨V, hV⟩ := exists_approxSeq (μ := μ) hWmeas H
    (isStronglyPredictable_const hWmeas (-θ)) (fun _ _ ↦ le_rfl)
  have h := (memLp_ZTpred_one hW hWmeas H (isStronglyPredictable_const hWmeas (-θ))
    (fun _ _ ↦ le_rfl) V hV).integrable le_rfl
  refine (h.const_mul (Real.exp (θ ^ 2 * H))).congr ?_
  filter_upwards [ae_mul_ZTpred_const_neg hW hWmeas θ H] with ω hω
  refine eq_inv_of_mul_eq_one_left ?_
  calc _ = Real.exp (θ ^ 2 * H) * (ZTpred hW H hWmeas (isStronglyPredictable_const hWmeas θ)
        (fun _ _ ↦ le_rfl) ω * ZTpred hW H hWmeas (isStronglyPredictable_const hWmeas (-θ))
        (fun _ _ ↦ le_rfl) ω) := by ring
    _ = 1 := by rw [hω, ← Real.exp_add]; simp

include hW in
/-- **A bounded density against the physical measure is a square-integrable density against the
Girsanov measure.** If `Q = D·μ` with `0 ≤ D ≤ C`, then `Q = D'·Q*` with `D' = D/Z_H`, and
`𝔼_{Q*}[D'²] = 𝔼_μ[D²/Z_H] ≤ C² 𝔼_μ[1/Z_H] < ∞` (`integrable_inv_ZTpred_const`). -/
lemma exists_memLp_two_density_of_bdd (θ : ℝ) (H : ℝ≥0) {D : Ω → ℝ} (hDm : Measurable D)
    (hD0 : ∀ ω, 0 ≤ D ω) {C : ℝ} (hDC : ∀ ω, D ω ≤ C)
    {Q : Measure Ω} (hQD : Q = μ.withDensity fun ω ↦ ENNReal.ofReal (D ω)) :
    ∃ D' : Lp ℝ 2 (constGirsanovMeasure hW hWmeas θ H),
      (∀ᵐ ω ∂(constGirsanovMeasure hW hWmeas θ H), 0 ≤ D' ω) ∧
      Q = (constGirsanovMeasure hW hWmeas θ H).withDensity fun ω ↦ ENNReal.ofReal (D' ω) := by
  set Z := ZTpred hW H hWmeas (isStronglyPredictable_const hWmeas θ) (fun _ _ ↦ le_rfl) with hZdef
  have hZpos (ω : Ω) : 0 < Z ω := contDoleansExp_pos _ _ _ _
  have hZ := aestronglyMeasurable_ZTpred hW hWmeas (isStronglyPredictable_const hWmeas θ)
    (fun _ _ ↦ le_rfl) H
  have hZamb : AEStronglyMeasurable Z μ :=
    (hZ.stronglyMeasurable_mk.mono ((natFiltration hWmeas).le H)).aestronglyMeasurable.congr
      hZ.ae_eq_mk.symm
  have hD'm : AEMeasurable (fun ω ↦ D ω / Z ω) μ := hDm.aemeasurable.div hZamb.aemeasurable
  have hac : constGirsanovMeasure hW hWmeas θ H ≪ μ := withDensity_absolutelyContinuous _ _
  have hQD' : Q = (constGirsanovMeasure hW hWmeas θ H).withDensity
      fun ω ↦ ENNReal.ofReal (D ω / Z ω) := by
    rw [hQD, constGirsanovMeasure, ← withDensity_mul₀ hZamb.aemeasurable.ennreal_ofReal
      hD'm.ennreal_ofReal]
    congr 1
    funext ω
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (hZpos ω).le, mul_div_cancel₀ _ (hZpos ω).ne']
  have hmem : MemLp (fun ω ↦ D ω / Z ω) 2 (constGirsanovMeasure hW hWmeas θ H) := by
    rw [memLp_two_iff_integrable_sq (hD'm.aestronglyMeasurable.mono_ac hac)]
    refine (integrable_withDensity_iff_integrable_smul₀' hZamb.aemeasurable.ennreal_ofReal
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2 ?_
    refine ((integrable_inv_ZTpred_const hW hWmeas θ H).const_mul (C ^ 2)).mono' ?_ ?_
    · exact (hZamb.aemeasurable.ennreal_ofReal.ennreal_toReal.smul
        (hD'm.pow_const 2)).aestronglyMeasurable
    · refine .of_forall fun ω ↦ ?_
      rw [ENNReal.toReal_ofReal (hZpos ω).le, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hZpos ω).le (sq_nonneg _)), div_pow,
        show Z ω * (D ω ^ 2 / Z ω ^ 2) = D ω ^ 2 * (Z ω)⁻¹ by field_simp]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hD0 ω) (hDC ω) 2)
        (inv_nonneg.2 (hZpos ω).le)
  refine ⟨hmem.toLp _, ?_, ?_⟩
  · filter_upwards [hmem.coeFn_toLp] with ω hω
    rw [hω]
    exact div_nonneg (hD0 ω) (hZpos ω).le
  · rw [hQD']
    exact withDensity_congr_ae (hmem.coeFn_toLp.mono fun ω hω ↦ congrArg ENNReal.ofReal hω.symm)

include hW in
/-- **Every pricing measure with a bounded density against the physical measure prices the
European call at the Black–Scholes formula.** A pricing measure `Q = D·μ` of the Black–Scholes
market up to `T ≤ H`, with `0 ≤ D ≤ C`, prices the call at `S₀ Φ(d₁) − K e^{−rT} Φ(d₂)`: its
density against the Girsanov measure is square-integrable
(`exists_memLp_two_density_of_bdd`), so
`price_europeanCall_of_isPricingMeasure_withDensity` applies. -/
theorem price_europeanCall_of_isPricingMeasure_bdd
    (hWcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ W s ω) {K : ℝ} {T H : ℝ≥0} (hTH : T ≤ H)
    (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < (T : ℝ)) {Q : Measure Ω}
    (hQ : (market μ hWmeas S_0 m r σ).IsPricingMeasure T Q) {D : Ω → ℝ} (hDm : Measurable D)
    (hD0 : ∀ ω, 0 ≤ D ω) {C : ℝ} (hDC : ∀ ω, D ω ≤ C)
    (hQD : Q = μ.withDensity fun ω ↦ ENNReal.ofReal (D ω)) :
    (market μ hWmeas S_0 m r σ).price Q (europeanCall K T)
      = S_0 * Phi (bsd1 S_0 K r σ T) - K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) :=
  let ⟨_, hD', hQD'⟩ := exists_memLp_two_density_of_bdd hW hWmeas ((m - r) / σ) H hDm hD0 hDC hQD
  price_europeanCall_of_isPricingMeasure_withDensity hW hWmeas hWcont hTH hS₀ hK hσ hT hQ _ hD'
    hQD'

end Bounded

end MathFin.Contracts.BlackScholes
