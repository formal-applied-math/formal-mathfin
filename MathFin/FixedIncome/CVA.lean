/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.FixedIncome.HazardCurve
public import MathFin.BlackScholes.Bachelier
public import MathFin.FixedIncome.DefaultDensity

/-!
# CVA under independent exposure (no wrong-way risk)

Hull, *Options, Futures and Other Derivatives* ch. 24 (CVA, sl. 25–28) and Bagaria ch. 16
(eq. 16.2): with exposure independent of the counterparty's default time,

  `CVA = LGD · E[D(τ) · V_τ⁺ · 1{τ ≤ T}] = LGD · ∫₀ᵀ D(s) · EE(s) · λ(s) · Q(s) ds`,

`EE(s) = E[V_s⁺]` the expected positive exposure.

Independence uses the same two-factor product-space layout as `MathFin.Cox.cox_mixing_survival`
(mathfin `FixedIncome/Cox.lean`), though not its mixing construction: the exposure lives on
`(Ω₁, ν)`, the default time on `(Ω₂, μ)`, and the pricing measure is `ν.prod μ`, so τ is
independent of the exposure by the product measure itself, with no mixing against the first
factor's randomness. The Fubini step reduces the claim to the kernel
`MathFin.DefaultDensity.integral_indicator_Iic_eq` with discount curve `D · EE`.

* `integral_exposure_eq` — the general reduction (joint integrability hypothesized).
* `expectedExposure_gaussian` — `E[(m + σ√s·Z)⁺] = m·Φ(m/(σ√s)) + σ√s·φ(m/(σ√s))`,
  from `bachelier_call_formula` with the strike shifted to `K = 1`, `S₀ = m + 1`.
* `cva_gaussian` — headline: Gaussian exposure, bounded `D, m, σ`, CVA in closed form.
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

theorem measurable_expectedExposure [SFinite ν] {V : ℝ → Ω₁ → ℝ}
    (hV : Measurable (Function.uncurry V)) : Measurable (expectedExposure V ν) :=
  (hV.max measurable_const).stronglyMeasurable.integral_prod_right'.measurable

/-- **No-WWR reduction** (Hull ch. 24; Bagaria eq. 16.2): exposure independent of a default
time with deterministic continuous hazard `h ≥ 0` gives
`E[1{τ ≤ T} D(τ) V_τ⁺] = ∫₀ᵀ D(s) · EE(s) · λ(s)Q(s) ds`. -/
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
/-- **CVA with Gaussian exposure, no wrong-way risk** (Hull ch. 24, sl. 25–28 and sl. 38;
Bagaria eq. 16.2). Exposure `V_s = m(s) + σ(s)√s·Z`, `Z ~ N(0,1)` on the exposure factor,
independent (product measure) of a default time with continuous hazard `h ≥ 0`; `D`, `m`, `σ`
measurable and bounded, `σ > 0`. Then

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
          have := hσpos (τ p.2)
          have := hσb (τ p.2)
          calc m (τ p.2) + σ (τ p.2) * √(τ p.2) * Z p.1
              ≤ |m (τ p.2)| + σ (τ p.2) * √(τ p.2) * |Z p.1| := by
                rw [mul_assoc, mul_assoc]
                gcongr
                · exact le_abs_self _
                exact le_abs_self _
            _ ≤ M + S * √T * |Z p.1| := add_le_add (hmb _)
                (mul_le_mul_of_nonneg_right (mul_le_mul this hsq (Real.sqrt_nonneg _) hS)
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

end MathFin.CVA
