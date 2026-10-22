/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import Mathlib
public import MathFin.FixedIncome.HazardCurve
public import MathFin.BlackScholes.Bachelier
public import MathFin.FixedIncome.DefaultDensity

/-!
# CVA under independent exposure (no wrong-way risk)

Hull, *Options, Futures, and Other Derivatives* (CVA, in its credit-risk chapter). With
exposure independent of the counterparty's default time, CVA is the CDS protection-leg
integral of Bagaria eq. 16.2 with the discount curve `P(0,·)` replaced by `D·EE`:

  `CVA = LGD · E[D(τ) · V_τ⁺ · 1{τ ≤ T}] = LGD · ∫₀ᵀ D(s) · EE(s) · λ(s) · Q(s) ds`,

`EE(s) = E[V_s⁺]` the expected positive exposure.

Independence uses the same two-factor product-space layout as `MathFin.Cox.cox_mixing_survival`
(`FixedIncome/Cox.lean`), though not its mixing construction: the exposure lives on
`(Ω₁, ν)`, the default time on `(Ω₂, μ)`, and the pricing measure is `ν.prod μ`, so τ is
independent of the exposure by the product measure itself, with no mixing against the first
factor's randomness. The Fubini step reduces the claim to the kernel
`MathFin.DefaultDensity.integral_indicator_Iic_eq` with discount curve `D · EE`.

* `integral_exposure_eq` — the general reduction (joint integrability hypothesized).
* `expectedExposure_gaussian` — `E[(m + σ√s·Z)⁺] = m·Φ(m/(σ√s)) + σ√s·φ(m/(σ√s))` for
  `σ, s > 0`, from `bachelier_call_formula` with the strike shifted to `K = 1`, `S₀ = m + 1`.
* `cva_gaussian` — headline: Gaussian exposure, bounded `D, m, σ`, `σ > 0`: CVA as a
  one-dimensional time integral whose integrand (the expected exposure) is in closed form.
* `cva_one_eq_protectionLeg` — the CVA of a unit exposure discounted at a flat rate `r` is the CDS
  protection leg `Cox.protectionLeg` (Bagaria eq. 16.2), for any default time whose CDF on
  `[0, ∞)` is `1 − Q` (hypothesized, as above).
* `protectionLeg_eq_integral_coxDefaultTime` — for the Cox default time constructed in
  `FixedIncome/Cox.lean` (a unit-exponential clock inverted through `∫₀ᵗ h`), the protection leg is
  the expectation `(1 − R)·E[e^{−rτ}·1{τ ≤ T}]`; here the CDF is derived, not hypothesized.

## References

* J. C. Hull, *Options, Futures, and Other Derivatives* (the credit-risk chapter: CVA).
* S. Bagaria, *Notes on Fixed Income Derivative Pricing* (lecture notes), ch. 16.
-/

@[expose] public section

namespace MathFin.CVA

open MeasureTheory Real MathFin.DefaultDensity

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {ν : Measure Ω₁} {μ : Measure Ω₂}

/-- Expected positive exposure `EE(s) = E_ν[V_s⁺]`. -/
noncomputable def expectedExposure (V : ℝ → Ω₁ → ℝ) (ν : Measure Ω₁) (s : ℝ) : ℝ :=
  ∫ ω, max (V s ω) 0 ∂ν

/-- Unilateral CVA on the product space: `LGD · E[1{τ ≤ T} · D(τ) · V_τ⁺]`, exposure on the
first factor, default time on the second. -/
noncomputable def cva (LGD : ℝ) (D : ℝ → ℝ) (V : ℝ → Ω₁ → ℝ) (τ : Ω₂ → ℝ) (T : ℝ)
    (ν : Measure Ω₁) (μ : Measure Ω₂) : ℝ :=
  LGD * ∫ p, (Set.Iic T).indicator D (τ p.2) * max (V (τ p.2) p.1) 0 ∂(ν.prod μ)

/-- `EE` is measurable in `s` when `V` is jointly measurable (Fubini measurability of the
inner integral). -/
theorem measurable_expectedExposure [SFinite ν] {V : ℝ → Ω₁ → ℝ}
    (hV : Measurable (Function.uncurry V)) : Measurable (expectedExposure V ν) :=
  (hV.max measurable_const).stronglyMeasurable.integral_prod_right'.measurable

/-- **No-WWR reduction** (Hull's CVA; the protection-leg kernel of Bagaria eq. 16.2):
exposure independent of a default time with deterministic continuous hazard `h ≥ 0` gives
`E[1{τ ≤ T} D(τ) V_τ⁺] = ∫₀ᵀ D(s) · EE(s) · λ(s)Q(s) ds`, for measurable `D`, jointly
measurable `V`, `T ≥ 0`, and the left integrand jointly integrable (hypothesis `hint`). -/
theorem integral_exposure_eq [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {h : ℝ → ℝ} (hh : Continuous h) (hnn : ∀ s, 0 ≤ h s) {τ : Ω₂ → ℝ} (hτ : Measurable τ)
    (hcdf : ∀ a, 0 ≤ a → μ {ω | τ ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a))
    {D : ℝ → ℝ} (hD : Measurable D) {V : ℝ → Ω₁ → ℝ} (hV : Measurable (Function.uncurry V))
    {T : ℝ} (hT : 0 ≤ T)
    (hint : Integrable (fun p : Ω₁ × Ω₂ ↦ (Set.Iic T).indicator D (τ p.2) * max (V (τ p.2) p.1) 0)
      (ν.prod μ)) :
    ∫ p, (Set.Iic T).indicator D (τ p.2) * max (V (τ p.2) p.1) 0 ∂(ν.prod μ)
      = ∫ s in (0:ℝ)..T, D s * expectedExposure V ν s * defaultDensity h s := by
  rw [integral_prod_symm _ hint]
  simp_rw [integral_const_mul]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)).trans
    (integral_indicator_Iic_eq hh hnn hτ.aemeasurable hcdf
      (hD.mul (measurable_expectedExposure hV)) hT)
  exact (Set.indicator_mul_left _ D (expectedExposure V ν)).symm

open ProbabilityTheory in
/-- **Gaussian expected exposure**: for `Z ~ N(0,1)`, `s > 0`, `b > 0`,
`E[(a + b√s·Z)⁺] = a·Φ(d) + b√s·φ(d)` with `d = a/(b√s)`. The Bachelier call formula with
strike `K = 1` and spot `a + 1`, so no `K > 0` restriction is lost. -/
theorem expectedExposure_gaussian [IsProbabilityMeasure ν] {Z : Ω₁ → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) ν) {a b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    ∫ ω, max (a + b * √s * Z ω) 0 ∂ν
      = a * Phi (a / (b * √s)) + b * √s * gaussianPDFReal 0 1 (a / (b * √s)) := by
  have := bachelier_call_formula (S_0 := a + 1) ⟨one_pos, hb, hs, hZ⟩
  simp only [bachelierTerminal, bachelierD, add_sub_cancel_right] at this
  simpa only [add_right_comm a 1, add_sub_cancel_right] using this

open ProbabilityTheory in
/-- **CVA with Gaussian exposure, no wrong-way risk** (Hull's CVA; the protection-leg kernel
of Bagaria eq. 16.2). Exposure `V_s = m(s) + σ(s)√s·Z`, `Z ~ N(0,1)` on the exposure factor,
independent (product measure) of a default time with continuous hazard `h ≥ 0`; `D`, `m`, `σ`
measurable and bounded, `σ > 0`, `T ≥ 0`. By `integral_exposure_eq` a CVA under independence
depends on `V` only through `EE(s)`, so only the marginal laws `V_s ~ N(m(s), σ(s)²s)` enter
it and one driver `Z` for all `s` loses nothing for this value; no exposure dynamics are
modelled. Then

  `CVA = LGD · ∫₀ᵀ D(s) · [m(s)Φ(d_s) + σ(s)√s·φ(d_s)] · λ(s)Q(s) ds`, `d_s = m(s)/(σ(s)√s)`. -/
theorem cva_gaussian [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {h : ℝ → ℝ} (hh : Continuous h) (hnn : ∀ s, 0 ≤ h s) {τ : Ω₂ → ℝ} (hτ : Measurable τ)
    (hcdf : ∀ a, 0 ≤ a → μ {ω | τ ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a))
    {D : ℝ → ℝ} (hD : Measurable D) {C : ℝ} (hDb : ∀ s, |D s| ≤ C)
    {m σ : ℝ → ℝ} (hm : Measurable m) (hσ : Measurable σ) {M S : ℝ} (hmb : ∀ s, |m s| ≤ M)
    (hσpos : ∀ s, 0 < σ s) (hσb : ∀ s, σ s ≤ S)
    {Z : Ω₁ → ℝ} (hZm : Measurable Z) (hZ : HasLaw Z (gaussianReal 0 1) ν) (LGD : ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    cva LGD D (fun s ω ↦ m s + σ s * √s * Z ω) τ T ν μ
      = LGD * ∫ s in (0:ℝ)..T, D s * (m s * Phi (m s / (σ s * √s))
          + σ s * √s * gaussianPDFReal 0 1 (m s / (σ s * √s))) * defaultDensity h s := by
  have hV : Measurable (Function.uncurry fun s ω ↦ m s + σ s * √s * Z ω) :=
    (hm.comp measurable_fst).add (((hσ.comp measurable_fst).mul
      (measurable_fst.sqrt)).mul (hZm.comp measurable_snd))
  have hZint : Integrable Z ν := by
    have : Integrable id (ν.map Z) := hZ.map_eq ▸ (memLp_id_gaussianReal 1).integrable le_rfl
    exact (integrable_map_measure aestronglyMeasurable_id hZm.aemeasurable).mp this
  have hC : 0 ≤ C := (abs_nonneg _).trans (hDb 0)
  have hS : 0 ≤ S := (hσpos 0).le.trans (hσb 0)
  have hg : ∀ x : ℝ, 0 ≤ M + S * √T * |x| := fun x ↦
    add_nonneg ((abs_nonneg _).trans (hmb 0)) (by positivity)
  have hint : Integrable (fun p : Ω₁ × Ω₂ ↦ (Set.Iic T).indicator D (τ p.2) *
      max (m (τ p.2) + σ (τ p.2) * √(τ p.2) * Z p.1) 0) (ν.prod μ) := by
    refine Integrable.mono' ((((integrable_const M).add
      (hZint.abs.const_mul (S * √T))).const_mul C).comp_fst μ) ?_
      (Filter.Eventually.of_forall fun p ↦ ?_)
    · exact (((hD.indicator measurableSet_Iic).comp (hτ.comp measurable_snd)).mul
        ((hV.comp ((hτ.comp measurable_snd).prodMk measurable_fst)).max
          measurable_const)).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_mul]
      by_cases hs : τ p.2 ∈ Set.Iic T
      · rw [Set.indicator_of_mem hs]
        have hsq : √(τ p.2) ≤ √T := Real.sqrt_le_sqrt hs
        have h1 : |max (m (τ p.2) + σ (τ p.2) * √(τ p.2) * Z p.1) 0|
            ≤ M + S * √T * |Z p.1| := by
          rw [abs_of_nonneg (le_max_right _ _)]
          refine max_le ?_ (hg _)
          -- `hσ0` is not referenced by name below: `gcongr`'s side-condition discharger
          -- finds it in context to prove `0 ≤ σ (τ p.2)` for the `mul_le_mul'`-style step.
          have hσ0 : 0 ≤ σ (τ p.2) := (hσpos (τ p.2)).le
          have hσS : σ (τ p.2) ≤ S := hσb (τ p.2)
          calc m (τ p.2) + σ (τ p.2) * √(τ p.2) * Z p.1
              ≤ |m (τ p.2)| + σ (τ p.2) * √(τ p.2) * |Z p.1| := by
                rw [mul_assoc, mul_assoc]
                gcongr
                · exact le_abs_self _
                exact le_abs_self _
            _ ≤ M + S * √T * |Z p.1| := add_le_add (hmb _)
                (mul_le_mul_of_nonneg_right (mul_le_mul hσS hsq (Real.sqrt_nonneg _) hS)
                  (abs_nonneg _))
        exact mul_le_mul (hDb _) h1 (abs_nonneg _) hC
      · rw [Set.indicator_of_notMem hs, abs_zero, zero_mul]
        exact mul_nonneg hC (hg _)
  unfold cva
  rw [integral_exposure_eq hh hnn hτ hcdf hD hV hT hint]
  congr 1
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hs ↦ ?_)
  rw [Set.uIoc_of_le hT] at hs
  simp only [expectedExposure]
  rw [expectedExposure_gaussian hZ (hσpos s) hs.1]

/-- **The protection leg is the CVA of a unit exposure.** For a default time `τ` with continuous
hazard `h ≥ 0` (CDF `1 − Q` on `[0, ∞)`, hypothesized), recovery `R`, flat rate `r` and `T ≥ 0`,
the CVA of the constant exposure `V ≡ 1` discounted by `e^{−rs}` is
`(1 − R)·E[e^{−rτ}·1{τ ≤ T}] = (1 − R)·∫₀ᵀ e^{−rs} h(s) Q(s) ds = Cox.protectionLeg R r h T`. -/
theorem cva_one_eq_protectionLeg [IsProbabilityMeasure ν] [IsFiniteMeasure μ] {h : ℝ → ℝ}
    (hh : Continuous h) (hnn : ∀ s, 0 ≤ h s) {τ : Ω₂ → ℝ} (hτ : AEMeasurable τ μ)
    (hcdf : ∀ a, 0 ≤ a → μ {ω | τ ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a))
    (R r : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    cva (1 - R) (fun s ↦ rexp (-(r * s))) (fun _ _ ↦ 1) τ T ν μ = Cox.protectionLeg R r h T := by
  simp only [cva, max_eq_left (zero_le_one : (0 : ℝ) ≤ 1), mul_one]
  rw [integral_fun_snd (f := fun ω ↦ (Set.Iic T).indicator (fun s ↦ rexp (-(r * s))) (τ ω)),
    probReal_univ, one_smul,
    integral_indicator_Iic_eq hh hnn hτ hcdf (by fun_prop) hT, Cox.protectionLeg, Cox.cdsLosses]
  congr 1
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  simp only [defaultDensity]
  ring

/-- **The Cox protection leg is an expectation over the constructed default time.** For `h`
continuous and positive with `∫₀ᵗ h → ∞`, `ξ` a unit-exponential clock and
`τ = Cox.coxDefaultTime h ξ` (the clock inverted through `∫₀ᵗ h`), the CDS protection leg
`(1 − R)·∫₀ᵀ e^{−rs} h(s) e^{−∫₀ˢ h} ds` (`Cox.protectionLeg`) equals
`(1 − R)·E[e^{−rτ}·1{τ ≤ T}]` for `T ≥ 0`. The CDF of `τ` is `Cox.cox_cdf_timeVarying` and its
measurability is `Cox.measurable_coxDefaultTime`. -/
theorem protectionLeg_eq_integral_coxDefaultTime [IsFiniteMeasure μ] {h : ℝ → ℝ}
    (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop) {ξ : Ω₂ → ℝ}
    (hξmeas : Measurable ξ) (hξlaw : μ.map ξ = ProbabilityTheory.expMeasure 1) (R r : ℝ) {T : ℝ}
    (hT : 0 ≤ T) :
    Cox.protectionLeg R r h T =
      (1 - R) * ∫ ω, (Set.Iic T).indicator (fun s ↦ rexp (-(r * s)))
        (Cox.coxDefaultTime h ξ ω) ∂μ := by
  rw [integral_indicator_Iic_eq hh (fun s ↦ (hpos s).le)
    (Cox.measurable_coxDefaultTime hh hpos hξmeas).aemeasurable
    (fun _ ha ↦ Cox.cox_cdf_timeVarying hh hpos hdiv hξmeas hξlaw ha) (by fun_prop) hT,
    Cox.protectionLeg, Cox.cdsLosses]
  congr 1
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  simp only [defaultDensity]
  ring

end MathFin.CVA
