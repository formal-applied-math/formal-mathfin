/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Yang Ye
-/
module

public import MathFin.Models.BlackScholes.BlackScholes
public import MathFin.Models.BlackScholes.BlackScholesAsian
public import MathFin.Models.BlackScholes.BlackScholesChooser
public import MathFin.Probability.Brownian.Girsanov.GirsanovFiltered
public import MathFin.Models.BlackScholes.BSCallHypFromBrownian

/-!
# Contracts priced from the physical Black–Scholes market

The contract theorems of `BlackScholes.lean`, `BlackScholesChooser.lean` and
`BlackScholesAsian.lean` price under a measure that is *assumed* risk-neutral: the asset is
`pathAssets S₀ r σ B` for a pre-Brownian `B` under the pricing measure. This file starts from the
physical market instead. The asset is `S_u = S₀ exp((m − σ²/2)u + σ W_u)` for a physical Brownian
motion `W` under `μ` and a physical drift `m`, that is `pathAssets S₀ m σ W`. The market price of
risk `θ = (m − r)/σ` is constant, hence bounded and predictable, so the Girsanov theorem for the
filtration (`Btheta_isFilteredPreBrownian_predictable_of_bdd`,
`Probability/Brownian/Girsanov/GirsanovFiltered.lean`)
applies at any horizon `H`: under `Q = Z_H·μ` the drift-corrected process `B^θ` is an
`𝓕`-pre-Brownian motion.

For each date `u ≤ H`, `B^θ_u = W_u + θu` almost surely (the drift of a constant integrand is
`θu`), so the physical asset at `u` is almost surely the risk-neutral asset
`pathAssets S₀ r σ B^θ` at `u`. A fixed-dated contract reads finitely many such dates, so by
`Contract.value_congr_ae` its value in the physical market under `Q` is its value in
`pathAssets S₀ r σ B^θ`, which the existing contract theorems give in closed form. The identity is
almost sure at each date, not pathwise, and only for dates `≤ H`: past `H` the process `B^θ` has
frozen drift, which is why the contracts below carry the hypothesis that their dates lie in
`[0, H]`.

## Main definitions

* `BlackScholes.constGirsanovMeasure`: the horizon-`H` Girsanov measure `Z_H·μ` of a constant
  market price of risk `θ`.
* `BlackScholes.constBtheta`: the drift-corrected process `B^θ` of that `θ`.

## Main results

* `BlackScholes.constBtheta_drift_ae`: for `u ≤ H`, `B^θ_u = W_u + θu` almost surely, for the
  constant integrand `θ`.
* `BlackScholes.pathAssets_physical_ae_eq`: for `u ≤ H` and `θ = (m − r)/σ`, the physical asset at
  `u` equals `pathAssets S₀ r σ B^θ` at `u`, `Q`-almost surely.
* `BlackScholes.isPreBrownianReal_constBtheta`: `B^θ` is a pre-Brownian motion under `Q`.
* `BlackScholes.value_physical_eq_riskNeutral`: any fixed-dated contract observed in `[0, H]` has
  the same `Q`-value on the physical asset as on `pathAssets S₀ r σ B^θ`.
* `BlackScholes.value_europeanCall_physical`, `BlackScholes.value_chooser_physical`,
  `BlackScholes.value_geomAsianCall_physical`: the European call, the chooser and the geometric
  Asian call on the physical asset are worth their Black–Scholes closed forms under `Q`, as
  instances of `value_physical_eq_riskNeutral`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 9.1.8
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 5.2
* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [A. G. Z. Kemna and A. C. F. Vorst, *A pricing method for options based on average asset
  values*][KemnaVorst1990]
* [M. Rubinstein, *Options for the undecided*][Rubinstein1991]
* [Zhang, *Exotic Options*][ZhangExoticOptions]

## Tags

Girsanov theorem, physical measure, market price of risk, risk-neutral valuation, Black–Scholes
model, contract pricing, MSC 91G20, MSC 60H05, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal
open MathFin ItoIntegralL2 ItoIntegralProcessContinuousModification

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

variable (hW : IsPreBrownianReal W μ) (hWmeas : ∀ t, Measurable (W t))

/-- The Girsanov measure at horizon `H` of the constant market price of risk `θ`:
`Q = μ.withDensity(Z_H)`, `Z_H = exp(−∫₀ᴴ θ dW − ½∫₀ᴴ θ² ds)`
(`ZTpred` for the constant integrand). -/
noncomputable def constGirsanovMeasure (θ : ℝ) (H : ℝ≥0) : Measure Ω :=
  μ.withDensity fun ω ↦ ENNReal.ofReal
    (ZTpred hW H hWmeas (isStronglyPredictable_const hWmeas θ) (fun _ _ ↦ le_rfl) ω)

/-- The drift-corrected process `B^θ_u = W_u + driftContinuousMod θ̂ u` of the constant market
price of risk `θ` (`BthetaPred` for the constant integrand). -/
noncomputable def constBtheta (θ : ℝ) (H : ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ :=
  BthetaPred (μ := μ) H hWmeas (isStronglyPredictable_const hWmeas θ) (fun _ _ ↦ le_rfl) u ω

include hW in
/-- The constant-price-of-risk Girsanov measure is a probability measure. -/
lemma constGirsanovMeasure_isProbabilityMeasure (θ : ℝ) (H : ℝ≥0) :
    IsProbabilityMeasure (constGirsanovMeasure hW hWmeas θ H) := by
  obtain ⟨V, hV⟩ := exists_approxSeq (μ := μ) hWmeas H
    (isStronglyPredictable_const hWmeas θ) (fun _ _ ↦ le_rfl)
  exact isProbabilityMeasure_predGirsanov hW hWmeas H (isStronglyPredictable_const hWmeas θ)
    (fun _ _ ↦ le_rfl) V hV

include hW in
/-- **`B^θ` is a Brownian motion for the filtration under `Q`.** For the constant price of risk
`θ`, under `Q = Z_H·μ` the process `B^θ` is an `𝓕`-pre-Brownian motion on all of `ℝ≥0`
(`Btheta_isFilteredPreBrownian_predictable_of_bdd`). -/
theorem isFilteredPreBrownian_constBtheta (θ : ℝ) (H : ℝ≥0) :
    IsFilteredPreBrownian (constBtheta (μ := μ) hWmeas θ H) (natFiltration hWmeas)
      (constGirsanovMeasure hW hWmeas θ H) :=
  Btheta_isFilteredPreBrownian_predictable_of_bdd hW hWmeas
    (isStronglyPredictable_const hWmeas θ) (fun _ _ ↦ le_rfl) H

include hW in
/-- `B^θ` is a pre-Brownian motion under `Q`, the hypothesis the contract theorems take. -/
theorem isPreBrownianReal_constBtheta (θ : ℝ) (H : ℝ≥0) :
    IsPreBrownianReal (constBtheta (μ := μ) hWmeas θ H) (constGirsanovMeasure hW hWmeas θ H) :=
  (isFilteredPreBrownian_constBtheta hW hWmeas θ H).toIsPreBrownianReal

/-- **The drift of a constant integrand is `θu`.** For `u ≤ H`, almost surely
`B^θ_u = W_u + θu`: the limit drift `driftContinuousMod θ̂ u` is `∫₀ᵘ θ̂(s) ds`
(`driftContinuousMod_eq_setIntegral`) and the integrand `θ̂` is `θ` for almost every `s` on almost
every path (`processToLpPredictable_ae_slice`). -/
theorem constBtheta_drift_ae (θ : ℝ) (H : ℝ≥0) {u : ℝ≥0} (hu : u ≤ H) :
    ∀ᵐ ω ∂μ, constBtheta (μ := μ) hWmeas θ H u ω = W u ω + θ * (u : ℝ) := by
  filter_upwards [driftContinuousMod_eq_setIntegral H hWmeas
      (processToLpPredictable (μ := μ) H hWmeas (isStronglyPredictable_const hWmeas θ)
        (fun _ _ ↦ le_rfl)) hu,
    processToLpPredictable_ae_slice (μ := μ) H hWmeas (isStronglyPredictable_const hWmeas θ)
      (fun _ _ ↦ le_rfl)] with ω h1 h2
  have h3 : ∀ᵐ s ∂(ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) u)),
      processToLpPredictable (μ := μ) H hWmeas (isStronglyPredictable_const hWmeas θ)
        (fun _ _ ↦ le_rfl) (s, ω) = θ :=
    ae_mono (Measure.restrict_mono (Set.Ioc_subset_Ioc_right hu) le_rfl) h2
  simp only [constBtheta, BthetaPred]
  rw [h1, integral_congr_ae h3, setIntegral_const, smul_eq_mul, measureReal_def,
    ItoIntegralL2.timeMeasure_Ioc, ENNReal.toReal_ofReal (by simp), NNReal.coe_zero, sub_zero]
  ring

include hW in
/-- **The physical asset is the risk-neutral asset of `B^θ`.** For `σ ≠ 0`, `θ = (m − r)/σ`, and a
date `u ≤ H`, the physical price `S₀ exp((m − σ²/2)u + σ W_u)` is `Q`-almost surely
`S₀ exp((r − σ²/2)u + σ B^θ_u)`: the drift `m` is exactly `r + σθ`. -/
theorem pathAssets_physical_ae_eq {S_0 m r σ : ℝ} (hσ : σ ≠ 0) (H : ℝ≥0) {u : ℝ≥0} (hu : u ≤ H) :
    ∀ᵐ ω ∂(constGirsanovMeasure hW hWmeas ((m - r) / σ) H),
      pathAssets S_0 m σ W () u ω
        = pathAssets S_0 r σ (constBtheta (μ := μ) hWmeas ((m - r) / σ) H) () u ω := by
  have hac : constGirsanovMeasure hW hWmeas ((m - r) / σ) H ≪ μ :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [hac.ae_le (constBtheta_drift_ae (μ := μ) hWmeas ((m - r) / σ) H hu)] with ω hω
  simp only [pathAssets, hω]
  congr 2
  field_simp
  ring

/-! ### Contracts on the physical asset -/

/-- The European call's observations: its asset at maturity. -/
lemma obsList_europeanCall (K : ℝ) (T : ℝ≥0) : (europeanCall K T).obsList = [((), T)] := by
  simp [europeanCall, europeanCallPayoff, Contract.obsList, Payoff.obsList]

/-- The observations of `Payoff.obsProd` are the observed dates. -/
lemma obsList_obsProd {ι : Type*} (i : ι) (ts : List ℝ≥0) :
    (Payoff.obsProd i ts).obsList = ts.map fun t ↦ (i, t) := by
  induction ts with
  | nil => simp [Payoff.obsProd, Payoff.obsList]
  | cons t ts ih => simp [Payoff.obsProd, Payoff.obsList, ih]

include hW in
/-- **Physical value is risk-neutral value.** For `σ ≠ 0` and any fixed-dated contract `c` whose
observation dates lie in the horizon `[0, H]`, its value on the physical asset
`pathAssets S₀ m σ W` under the Girsanov measure `Q` of `θ = (m − r)/σ` is its value on the
risk-neutral asset `pathAssets S₀ r σ B^θ`, for any deflator `D`. The physical drift `m`
enters only through `Q`. -/
theorem value_physical_eq_riskNeutral {S_0 m r σ : ℝ} (hσ : σ ≠ 0) (H : ℝ≥0) {D : ℝ≥0 → Ω → ℝ}
    (c : Contract Unit) (hc : c.FixedDated) (hH : ∀ p ∈ c.obsList, p.2 ≤ H) :
    c.value (constGirsanovMeasure hW hWmeas ((m - r) / σ) H) D (pathAssets S_0 m σ W)
      = c.value (constGirsanovMeasure hW hWmeas ((m - r) / σ) H) D
          (pathAssets S_0 r σ (constBtheta (μ := μ) hWmeas ((m - r) / σ) H)) :=
  Contract.value_congr_ae c hc fun p hp ↦ pathAssets_physical_ae_eq hW hWmeas hσ H (hH p hp)

include hW in
/-- **The European call on the physical asset** is worth the Black–Scholes call price under the
Girsanov measure `Q` of the market price of risk `θ = (m − r)/σ`, for a maturity `T` in the
horizon `[0, H]`: `S₀ Φ(d₁) − K e^{−rT} Φ(d₂)`. The scenario is rewritten from the physical asset
`pathAssets S₀ m σ W` to `pathAssets S₀ r σ B^θ` (`Contract.value_congr_ae`) and the existing
`value_europeanCall` is applied. -/
theorem value_europeanCall_physical {S_0 K m r σ : ℝ} {T H : ℝ≥0} (hTH : T ≤ H)
    (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < (T : ℝ)) :
    (europeanCall K T).value (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (fun _ _ ↦ Real.exp (-r * T)) (pathAssets S_0 m σ W)
      = S_0 * Phi (bsd1 S_0 K r σ T) - K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) := by
  have := constGirsanovMeasure_isProbabilityMeasure hW hWmeas ((m - r) / σ) H
  have hB := isPreBrownianReal_constBtheta hW hWmeas ((m - r) / σ) H
  have hfix : (europeanCall K T).FixedDated := by simp [europeanCall, Contract.FixedDated]
  rw [value_physical_eq_riskNeutral hW hWmeas hσ.ne' H _ hfix (by simp [obsList_europeanCall, hTH]),
    Contract.value_congr_ae (Q := constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
      (X := pathAssets S_0 r σ (constBtheta (μ := μ) hWmeas ((m - r) / σ) H))
      (Y := assets S_0 r σ T
        (fun ω ↦ constBtheta (μ := μ) hWmeas ((m - r) / σ) H T ω / Real.sqrt T))
      (europeanCall K T) hfix (fun p hp ↦ by
        rw [obsList_europeanCall, List.mem_singleton] at hp
        subst hp
        exact .of_forall fun ω ↦ pathAssets_eq_bsTerminal _ hT S_0 r σ ω)]
  refine value_europeanCall ?_
  simpa using BSCallHyp.of_isPreBrownian (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
    (constBtheta (μ := μ) hWmeas ((m - r) / σ) H) hB hS₀ hK hσ hT

include hW in
/-- **The European put on the physical asset** is worth the Black–Scholes put price
`K e^{−rT} Φ(−d₂) − S₀ Φ(−d₁)` under the Girsanov measure `Q` of the market price of risk
`θ = (m − r)/σ`, for a maturity `T` in the horizon `[0, H]`. Same route as the call: the
scenario is rewritten from the physical asset to the risk-neutral one (`Contract.value_congr_ae`)
and the existing `value_europeanPut` is applied. -/
theorem value_europeanPut_physical {S_0 K m r σ : ℝ} {T H : ℝ≥0} (hTH : T ≤ H)
    (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < (T : ℝ)) :
    (europeanPut K T).value (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (fun _ _ ↦ Real.exp (-r * T)) (pathAssets S_0 m σ W)
      = K * Real.exp (-r * T) * Phi (-bsd2 S_0 K r σ T) - S_0 * Phi (-bsd1 S_0 K r σ T) := by
  have := constGirsanovMeasure_isProbabilityMeasure hW hWmeas ((m - r) / σ) H
  have hB := isPreBrownianReal_constBtheta hW hWmeas ((m - r) / σ) H
  have hfix : (europeanPut K T).FixedDated := by simp [europeanPut, Contract.FixedDated]
  rw [value_physical_eq_riskNeutral hW hWmeas hσ.ne' H _ hfix (by simp [europeanPut,
      Contract.obsList, Payoff.obsList, List.mem_singleton, hTH]),
    Contract.value_congr_ae (Q := constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
      (X := pathAssets S_0 r σ (constBtheta (μ := μ) hWmeas ((m - r) / σ) H))
      (Y := assets S_0 r σ T
        (fun ω ↦ constBtheta (μ := μ) hWmeas ((m - r) / σ) H T ω / Real.sqrt T))
      (europeanPut K T) hfix (fun p hp ↦ by
        simp only [europeanPut, Contract.obsList, Payoff.obsList, List.append_nil,
          List.nil_append, List.mem_append, List.mem_singleton] at hp
        obtain rfl := hp
        exact .of_forall fun ω ↦ pathAssets_eq_bsTerminal _ hT S_0 r σ ω)]
  refine value_europeanPut ?_
  simpa using BSCallHyp.of_isPreBrownian (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
    (constBtheta (μ := μ) hWmeas ((m - r) / σ) H) hB hS₀ hK hσ hT

include hW in
/-- **The chooser on the physical asset** is worth the chooser price
`bsV K r σ S₀ T + bsP (K e^{−r(T−t₁)}) r σ S₀ t₁` under the Girsanov measure `Q` of the market
price of risk `θ = (m − r)/σ`, for dates `T`, `t₁` in the horizon `[0, H]`. -/
theorem value_chooser_physical {S_0 K m r σ : ℝ} {T t₁ H : ℝ≥0} (hTH : T ≤ H) (ht₁H : t₁ ≤ H)
    (hT : 0 < (T : ℝ)) (ht₁ : 0 < (t₁ : ℝ)) (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) :
    (chooser K r T t₁).value (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (fun u _ ↦ Real.exp (-r * u)) (pathAssets S_0 m σ W)
      = chooserPrice S_0 K r σ T t₁ := by
  have := constGirsanovMeasure_isProbabilityMeasure hW hWmeas ((m - r) / σ) H
  have hB := isPreBrownianReal_constBtheta hW hWmeas ((m - r) / σ) H
  have hfix : (chooser K r T t₁).FixedDated := by
    simp [chooser, europeanCall, europeanPut, Contract.FixedDated]
  rw [value_physical_eq_riskNeutral hW hWmeas hσ.ne' H _ hfix fun p hp ↦ by
    simp only [chooser, europeanCall, europeanPut, Contract.obsList, Payoff.obsList,
      europeanCallPayoff, List.append_nil, List.nil_append, List.mem_append,
      List.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption]
  exact value_chooser hB hT ht₁ hS₀ hK hσ

include hW in
/-- **The geometric Asian call on the physical asset** is worth the call price at the effective
spot `geomAsianEffSpot` and volatility `geomAsianEffVol` under the Girsanov measure `Q` of the
market price of risk `θ = (m − r)/σ`, for averaging dates `τ i ≤ T` in the horizon `[0, H]`. -/
theorem value_geomAsianCall_physical {S_0 K m r σ : ℝ} {T H : ℝ≥0} {n : ℕ} (hn : 0 < n)
    (τ : Fin n → ℝ≥0) (hτT : ∀ i, τ i ≤ T) (hτH : ∀ i, τ i ≤ H) (hS₀ : 0 < S_0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < (T : ℝ)) (hV : 0 < geomAsianVar τ) :
    (geomAsianCall K T τ).value (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (fun _ _ ↦ Real.exp (-r * T)) (pathAssets S_0 m σ W)
      = geomAsianEffSpot S_0 r σ T τ *
          Phi (bsd1 (geomAsianEffSpot S_0 r σ T τ) K r (geomAsianEffVol σ T τ) T)
        - K * Real.exp (-r * T) *
          Phi (bsd2 (geomAsianEffSpot S_0 r σ T τ) K r (geomAsianEffVol σ T τ) T) := by
  have := constGirsanovMeasure_isProbabilityMeasure hW hWmeas ((m - r) / σ) H
  have hB := isPreBrownianReal_constBtheta hW hWmeas ((m - r) / σ) H
  have hfix : (geomAsianCall K T τ).FixedDated := by simp [geomAsianCall, Contract.FixedDated]
  rw [value_physical_eq_riskNeutral hW hWmeas hσ.ne' H _ hfix fun p hp ↦ by
    simp only [geomAsianCall, Contract.obsList, Payoff.obsList, obsList_obsProd,
      List.append_nil, List.nil_append, List.map_ofFn, List.mem_ofFn] at hp
    obtain ⟨j, rfl⟩ := hp
    exact hτH j]
  exact value_geomAsianCall hB hn τ hτT hS₀ hK hσ hT hV

end MathFin.Contracts.BlackScholes
