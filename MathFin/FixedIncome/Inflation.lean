/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
import Mathlib
import MathFin.Foundations.Numeraire
import MathFin.Foundations.BrownianMartingale

/-!
# Inflation is FX: the zero-coupon inflation swap and the YoY convexity

The Jarrow–Yildirim identification reads the price index `I_t` as an exchange rate
(nominal currency per real good) and the index-linked bond as a bond denominated in
goods. Under that identification the modelling content is one postulate — the
index-linked bond `I_t·Pʳ(t,T)` is a nominal tradable, priced on the real curve — and
everything else in the zero-coupon inflation swap is change-of-numéraire bookkeeping
(`forwardIndex_eq`, `breakeven_eq`: eqs. 17.6/17.7 of the chapter).

The year-on-year convexity is the quanto correction one dimension up: with both rates
Gaussian, the expectation of the exponential of the two-rate deviation is computed by
the same ρ-decomposition of a correlated driver into independent normals that powers
`MathFin.quantoForward_of_gaussian` (`QuantoGrounding.lean:65`), with the 1-D Gaussian
MGF `integral_exp_mul_gaussianReal_zero` (`BrownianMartingale.lean:49`) applied twice
(`yoyRatioExp_gaussian`). Composing with the Hull–White bond-reconstitution
deterministics `Dⁱ = −½Bⁱ²Vⁱ` collapses the exponent — the real-variance halves cancel,
the nominal halves double — to the chapter's eq. (17.10) (`yoyConvexity_eq`), with the
naive ratio of forwards carried as an explicit multiplicative constant.
-/

open MeasureTheory ProbabilityTheory

/-! ## The zero-coupon inflation swap (eqs. 17.6/17.7)

`Qⁿ` is the nominal pricing measure (probability), `B_T` the money-market account at
`T` (a strictly positive random variable), `Pⁿ₀T = Pⁿ(0,T)` and `Pʳ₀T = Pʳ(0,T)` the
nominal and real T-bond prices, `I₀` today's index and `I_T` the terminal index. The
**identification hypothesis** `hident` is the chapter's postulate verbatim: the
index-linked bond, paying `I_T` at `T`, is priced on the real curve, `𝔼^{Qⁿ}[I_T/B_T]
= I₀·Pʳ(0,T)`. -/
namespace MathFin.Inflation.ZCSwap

variable {Ω : Type*} [MeasurableSpace Ω] {Qn : Measure Ω} [IsProbabilityMeasure Qn]

omit [IsProbabilityMeasure Qn] in
/-- **The forward index (eq. 17.6).** Under the Jarrow–Yildirim identification
(`hident`: the index-linked bond priced on the real curve), the index under the
nominal T-forward measure — the numéraire measure of the T-bond, whose terminal value
is `1` and whose initial price is `Pⁿ(0,T)` — is the real-curve/nominal-curve ratio:

  `𝔼^{Q^{n,T}}[I_T] = I₀ · Pʳ(0,T) / Pⁿ(0,T)`.

The proof is `changeOfNumeraire` (`Numeraire.lean:124`) at `X := I_T`, `N_T ≡ 1`,
`N₀ = Pⁿ₀T`, `B₀ = 1`, plus field algebra; no integrability hypothesis is needed. -/
theorem forwardIndex_eq (BT : Ω → ℝ) (Pn0T Pr0T I0 : ℝ) (IT : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hident : ∫ ω, IT ω / BT ω ∂Qn = I0 * Pr0T) :
    ∫ ω, IT ω ∂(MathFin.numeraireMeasure Qn BT (fun _ ↦ 1) 1 Pn0T) = I0 * Pr0T / Pn0T := by
  have h := MathFin.changeOfNumeraire (Q := Qn) (BT := BT) (NT := fun _ ↦ 1) (B0 := 1)
    (N0 := Pn0T) IT measurable_const hBTmeas (fun _ ↦ zero_lt_one) hBTpos zero_le_one hPn0T
  simp only [div_one, one_mul] at h
  rw [hident] at h
  rw [eq_div_iff hPn0T.ne', mul_comm]
  exact h


omit [IsProbabilityMeasure Qn] in
/-- **The spot price of the index-linked bond** — for contrast with
`forwardIndex_eq`. The numéraire-measure instantiation
`numeraireMeasure Qn BT (fun _ ↦ Pn0T) 1 Pn0T` has density `Pⁿ₀T/(Pⁿ₀T·B_T) = 1/B_T`
(the `N_T` and `N₀` slots cancel), so it is the spot pricing measure itself, not the
T-forward measure: the same identification `hident` prices the bond at `I₀·Pʳ(0,T)`
with **no** division by `Pⁿ₀T`. Recorded to document the B1 spec correction in the file
header — eq. (17.6)'s forward needs `forwardIndex_eq`'s instantiation instead. -/
theorem indexLinkedPrice_eq (BT : Ω → ℝ) (Pn0T Pr0T I0 : ℝ) (IT : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hident : ∫ ω, IT ω / BT ω ∂Qn = I0 * Pr0T) :
    ∫ ω, IT ω ∂(MathFin.numeraireMeasure Qn BT (fun _ ↦ Pn0T) 1 Pn0T) = I0 * Pr0T := by
  have h := MathFin.changeOfNumeraire (Q := Qn) (BT := BT) (NT := fun _ ↦ Pn0T) (B0 := 1)
    (N0 := Pn0T) IT measurable_const hBTmeas (fun _ ↦ hPn0T) hBTpos zero_le_one hPn0T
  simp only [one_mul] at h
  have hX : (fun ω ↦ IT ω / Pn0T) = fun ω ↦ (1 / Pn0T) * IT ω := by
    funext ω
    rw [div_eq_mul_one_div]
    ring
  rw [hX, integral_const_mul, hident] at h
  field_simp at h
  exact h


omit [IsProbabilityMeasure Qn] in
/-- **The breakeven inflation rate (eq. 17.7).** A zero-coupon inflation swap pays
`I_T/I₀ − (1+b)^T` at `T`; `b` is quoted as the breakeven. Fairness (`hfair`: under the
nominal T-forward measure the fixed leg `I₀(1+b)^T` matches the floating leg `I_T`)
combined with eq. (17.6) gives the curve-only breakeven identity

  `(1+b)^T = Pʳ(0,T) / Pⁿ(0,T)`,

with `T` the swap's maturity in years. The breakeven is a *ratio of bond prices*, not an
expectation of inflation — the chapter's central warning. -/
theorem breakeven_eq (BT : Ω → ℝ) (Pn0T Pr0T I0 b : ℝ) (T : ℕ) (IT : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T) (hI0 : 0 < I0)
    (hident : ∫ ω, IT ω / BT ω ∂Qn = I0 * Pr0T)
    (hfair : ∫ ω, IT ω ∂(MathFin.numeraireMeasure Qn BT (fun _ ↦ 1) 1 Pn0T)
      = I0 * (1 + b) ^ T) :
    (1 + b) ^ T = Pr0T / Pn0T := by
  have hf := forwardIndex_eq BT Pn0T Pr0T I0 IT hBTpos hBTmeas hPn0T hident
  rw [hfair, mul_div_assoc] at hf
  exact mul_left_cancel₀ (ne_of_gt hI0) hf


end MathFin.Inflation.ZCSwap

/-! ## The YoY Gaussian core (eq. 17.10's expectation layer)

With both rates Gaussian, the year-on-year ratio's convexity is an expectation of an
exponential of a normal. `yoyRatioExp_gaussian` computes it: two rate deviations
`yⁿ = mⁿ + √Vⁿ·Z₁` and `yʳ = mʳ + √Vʳ·(ρ·Z₁ + √(1−ρ²)·Z₂)` from independent standard
normals — the ρ-decomposition of the correlated two-rate driver, exactly the shape of
`MathFin.quantoForward_of_gaussian` (`QuantoGrounding.lean:65`) one dimension up — with
means `mⁿ, mʳ`, variances `Vⁿ, Vʳ`, correlation `ρ`, and Hull–White factors `Bⁿ, Bʳ`
over `[S, T]`. -/
namespace MathFin.Inflation.Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- **Standard-normal MGF** via `HasLaw` transfer: `𝔼[exp(a·Z)] = exp(a²/2)` for
`Z ~ N(0,1)` — the mirror of `QuantoGrounding.lean:50`'s private helper, backed by
`integral_exp_mul_gaussianReal_zero` (`BrownianMartingale.lean:49`). -/
private lemma integral_exp_mul_stdNormal {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) μ) (a : ℝ) :
    ∫ ω, Real.exp (a * Z ω) ∂μ = Real.exp (a ^ 2 / 2) := by
  have h := hZ.integral_comp
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (a * x)) (gaussianReal 0 1))
  simp only [Function.comp] at h
  rw [h, integral_exp_mul_gaussianReal_zero a 1]
  simp

omit [IsProbabilityMeasure μ] in
/-- **The two-rate exponential moment (eq. 17.10's Gaussian core).** For independent
standard normals `Z₁, Z₂` and Gaussian rate deviations `yⁿ = mⁿ + √Vⁿ·Z₁` and
`yʳ = mʳ + √Vʳ·(ρ·Z₁ + √(1−ρ²)·Z₂)` (so `Cov(yⁿ, yʳ) = ρ·√(Vⁿ·Vʳ)`),

  `𝔼[exp(Bⁿ·yⁿ − Bʳ·yʳ)] = exp(Bⁿ·mⁿ − Bʳ·mʳ + ½(Bⁿ²Vⁿ + Bʳ²Vʳ − 2·Bⁿ·Bʳ·ρ·√(VⁿVʳ)))`.

The proof is the `quantoForward_of_gaussian` pattern one dimension up: pointwise
factorization into `exp(const)·exp(a·Z₁)·exp(b·Z₂)` with `a = Bⁿ√Vⁿ − Bʳρ√Vʳ` and
`b = −Bʳ√(1−ρ²)√Vʳ`, independence factorization of the integral, and two applications
of the 1-D Gaussian MGF; the cross term `−2BⁿBʳρ√(VⁿVʳ)` is the `a²` algebra. -/
theorem yoyRatioExp_gaussian (mn mr Vn Vr ρ Bn Br : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1)
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hZ1m : Measurable Z1) (hZ2m : Measurable Z2) (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, Real.exp (Bn * (mn + Real.sqrt Vn * Z1 ω)
        - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))) ∂μ
      = Real.exp (Bn * mn - Br * mr
          + (Bn ^ 2 * Vn + Br ^ 2 * Vr - 2 * Bn * Br * ρ * Real.sqrt (Vn * Vr)) / 2) := by
  have h1r2 : (0 : ℝ) ≤ 1 - ρ ^ 2 := by linarith
  set E : ℝ := Bn * mn - Br * mr with hE
  set a : ℝ := Bn * Real.sqrt Vn - Br * ρ * Real.sqrt Vr with ha
  set b : ℝ := -(Br * Real.sqrt (1 - ρ ^ 2)) * Real.sqrt Vr with hb
  -- Pointwise: the integrand is the constant `exp E` times the two single-driver exponentials.
  have hpt : (fun ω ↦ Real.exp (Bn * (mn + Real.sqrt Vn * Z1 ω)
        - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))))
      = fun ω ↦ Real.exp E * (Real.exp (a * Z1 ω) * Real.exp (b * Z2 ω)) := by
    funext ω
    have hR : Real.exp E * (Real.exp (a * Z1 ω) * Real.exp (b * Z2 ω))
        = Real.exp (E + (a * Z1 ω + b * Z2 ω)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    rw [hR, hE, ha, hb]
    congr 1
    ring
  -- Independence factorization of the two single-driver exponentials.
  have hindep_exp : IndepFun (fun ω ↦ Real.exp (a * Z1 ω)) (fun ω ↦ Real.exp (b * Z2 ω)) μ :=
    hindep.comp (by fun_prop : Measurable fun x ↦ Real.exp (a * x))
      (by fun_prop : Measurable fun x ↦ Real.exp (b * x))
  have hprod : ∫ ω, Real.exp (a * Z1 ω) * Real.exp (b * Z2 ω) ∂μ
      = Real.exp (a ^ 2 / 2) * Real.exp (b ^ 2 / 2) := by
    rw [← integral_exp_mul_stdNormal hZ1 a, ← integral_exp_mul_stdNormal hZ2 b]
    exact hindep_exp.integral_mul_eq_mul_integral (by fun_prop) (by fun_prop)
  rw [hpt, integral_const_mul, hprod, ← Real.exp_add, ← Real.exp_add]
  -- The `a²` algebra: the cross term `−2·Bⁿ·B⁳·ρ·√(VⁿVʳ)` emerges from `(Bⁿ√Vⁿ − Bʳρ√Vʳ)²`.
  have hcross : Bn * Real.sqrt Vn * (Br * ρ * Real.sqrt Vr)
      = Bn * Br * ρ * Real.sqrt (Vn * Vr) := by
    rw [show Bn * Real.sqrt Vn * (Br * ρ * Real.sqrt Vr)
        = (Bn * ρ * Br) * (Real.sqrt Vn * Real.sqrt Vr) from by ring,
      ← Real.sqrt_mul hVn Vr]
    ring
  have ha2 : a ^ 2 = Bn ^ 2 * Vn + Br ^ 2 * ρ ^ 2 * Vr
      - 2 * (Bn * Real.sqrt Vn * (Br * ρ * Real.sqrt Vr)) := by
    have h1 : (Bn * Real.sqrt Vn) ^ 2 = Bn ^ 2 * Vn := by
      rw [mul_pow, Real.sq_sqrt hVn]
    have h2 : (Br * ρ * Real.sqrt Vr) ^ 2 = Br ^ 2 * ρ ^ 2 * Vr := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hVr]
    rw [ha, sub_sq, h1, h2]
    ring
  have hb2 : b ^ 2 = Br ^ 2 * (1 - ρ ^ 2) * Vr := by
    have h1 : (Br * Real.sqrt (1 - ρ ^ 2)) ^ 2 = Br ^ 2 * (1 - ρ ^ 2) := by
      rw [mul_pow, Real.sq_sqrt h1r2]
    have h2 : (Real.sqrt Vr) ^ 2 = Vr := Real.sq_sqrt hVr
    rw [hb, show (-(Br * Real.sqrt (1 - ρ ^ 2)) * Real.sqrt Vr) ^ 2
        = (Br * Real.sqrt (1 - ρ ^ 2)) ^ 2 * (Real.sqrt Vr) ^ 2 from by ring,
      h1, h2]
  have hsum : E + (a ^ 2 / 2 + b ^ 2 / 2)
      = E + (Bn ^ 2 * Vn + Br ^ 2 * Vr - 2 * Bn * Br * ρ * Real.sqrt (Vn * Vr)) / 2 := by
    rw [ha2, hb2, hcross]
    ring
  rw [hsum]


omit [IsProbabilityMeasure μ] in
/-- **Covariance form of the two-rate exponential moment.** The same conclusion with the
correlation slot replaced by the covariance `Cov = ρ·√(Vⁿ·Vʳ)` of the two rate deviations
(the form in which eq. 17.10 is stated in the chapter). -/
theorem yoyRatioExp_gaussian_cov (mn mr Vn Vr ρ Bn Br Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hZ1m : Measurable Z1) (hZ2m : Measurable Z2) (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, Real.exp (Bn * (mn + Real.sqrt Vn * Z1 ω)
        - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))) ∂μ
      = Real.exp (Bn * mn - Br * mr
          + (Bn ^ 2 * Vn + Br ^ 2 * Vr - 2 * Bn * Br * Cov) / 2) := by
  rw [hCov]
  have h := yoyRatioExp_gaussian mn mr Vn Vr ρ Bn Br hVn hVr hρ hZ1 hZ2 hZ1m hZ2m hindep
  rw [h]
  congr 1
  ring


end MathFin.Inflation.Gaussian

/-! ## The YoY convexity closed form (eq. 17.10)

The Hull–White bond-reconstitution formula (chapter 8, quoted at p. 295) expresses the
real/nominal bond-price ratio `Pʳ(S,T)/Pⁿ(S,T)` as the naive ratio of forwards
`Pʳ(0,T)·Pⁿ(0,S)/(Pʳ(0,S)·Pⁿ(0,T))` times the stochastic factor
`e^{Dʳ−Dⁿ}·e^{−Bʳyʳ+Bⁿyⁿ}`, with deterministic parts `Dⁱ = −½Bⁱ²Vⁱ`. Composing
`yoyRatioExp_gaussian_cov` with those deterministics collapses the exponent — the
real-variance halves cancel, the nominal halves double — to the chapter's eq. (17.10). -/
namespace MathFin.Inflation.Convexity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The reconstitution deterministic** `Dⁱ = −½·Bⁱ²·Vⁱ` of the Hull–White bond
reconstitution formula: the deterministic part of bond `i`'s [S,T]-factor, with `Bⁱ`
the Hull–White factor and `Vⁱ` the integrated variance. That `Dʳ − Dⁿ` *exactly* cancels
half of each variance in `yoyRatioExp_gaussian_cov`'s exponent is the collapse
mechanism of `yoyConvexity_eq`. -/
noncomputable def hwD (B V : ℝ) : ℝ := -(B ^ 2 * V) / 2


omit [IsProbabilityMeasure μ] in
/-- **The year-on-year convexity closed form (eq. 17.10, exact chapter shape).** With
the reconstituted bond-ratio factor — the naive ratio of forwards
`Pʳ₀T·Pⁿ₀S/(Pʳ₀S·Pⁿ₀T)` times `e^{Dʳ−Dⁿ−Bʳyʳ+Bⁿyⁿ}` with `Dⁱ = −½Bⁱ²Vⁱ` (the `hwD`
below) — the Gaussian expectation collapses to the naive ratio times the correction

  `C = exp(Bⁿ·mⁿ − Bʳ·mʳ + Bⁿ²·Vⁿ − Bʳ·Bⁿ·Cov)`,

the chapter's eq. (17.10) verbatim, with `Cov = ρ·√(VⁿVʳ)` the covariance of the two
rate deviations. The exponent's composition is pure algebra on
`yoyRatioExp_gaussian_cov`: `(Dʳ−Dⁿ) = (Bⁿ²Vⁿ − Bʳ²Vʳ)/2` cancels the *real*
variance's half exactly and doubles the *nominal* variance's half — the halves are the
whole content of the convexity. The means `mⁿ, mʳ`, variances and `Cov` are inputs:
where they come from (two correlated Hull–White fits, the quanto parent `−ρ_{rI}σ_rσ_I`
and the forward-measure parent `−ρ_{nr}σ_nσ_rBⁿ` inside them) is chapter-sourced
interpretation, not proved here. -/
theorem yoyConvexity_eq (mn mr Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hZ1m : Measurable Z1) (hZ2m : Measurable Z2) (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (hwD Br Vr - hwD Bn Vn
        + (Bn * (mn + Real.sqrt Vn * Z1 ω)
          - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω)))) ∂μ
      = (Pr0T * Pn0S / (Pr0S * Pn0T))
        * Real.exp (Bn * mn - Br * mr + Bn ^ 2 * Vn - Br * Bn * Cov) := by
  have hkey := Gaussian.yoyRatioExp_gaussian_cov mn mr Vn Vr ρ Bn Br Cov hVn hVr hρ hCov
    hZ1 hZ2 hZ1m hZ2m hindep
  -- Pointwise: the naive ratio times the full factor = (ratio · e^{Dʳ−Dⁿ}) · e^{−Bʳyʳ+Bⁿyⁿ}.
  have hpt : (fun ω ↦ (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (hwD Br Vr - hwD Bn Vn
          + (Bn * (mn + Real.sqrt Vn * Z1 ω)
            - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω)))))
      = fun ω ↦ ((Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (hwD Br Vr - hwD Bn Vn))
          * Real.exp (Bn * (mn + Real.sqrt Vn * Z1 ω)
            - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))) := by
    funext ω
    rw [mul_assoc, ← Real.exp_add]
  rw [hpt, integral_const_mul, hkey, mul_assoc, ← Real.exp_add]
  -- The `Dⁱ`-collapse: `Dʳ − Dⁿ = (Bⁿ²Vⁿ − Bʳ²Vʳ)/2` cancels the real halves, doubles the nominal.
  have hex : hwD Br Vr - hwD Bn Vn
      + (Bn * mn - Br * mr + (Bn ^ 2 * Vn + Br ^ 2 * Vr - 2 * Bn * Br * Cov) / 2)
      = Bn * mn - Br * mr + Bn ^ 2 * Vn - Br * Bn * Cov := by
    simp only [hwD]
    ring
  rw [hex]


omit [IsProbabilityMeasure μ] in
/-- **The quanto seat of the mean (the `Δ`-linearity).** The real rate's T-forward mean
carries the quanto parent `Δ` (chapter p. 295: the `−ρ_{rI}σ_rσ_I` piece of eq. 17.9's
drift, sitting inside `mʳ` under the Jarrow–Yildirim identification). Writing
`mʳ = mʳbase + Δ`, the correction exponent carries `Δ` **exactly** as the additive
piece `−Bʳ·Δ` and in no other way — pure specialization of `yoyConvexity_eq`. -/
theorem yoyConvexity_delta (mn mrBase Δ Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hZ1m : Measurable Z1) (hZ2m : Measurable Z2) (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (hwD Br Vr - hwD Bn Vn
        + (Bn * (mn + Real.sqrt Vn * Z1 ω)
          - Br * (mrBase + Δ + Real.sqrt Vr * (ρ * Z1 ω
            + Real.sqrt (1 - ρ ^ 2) * Z2 ω)))) ∂μ
      = (Pr0T * Pn0S / (Pr0S * Pn0T))
        * Real.exp (Bn * mn - Br * mrBase + Bn ^ 2 * Vn - Br * Bn * Cov - Br * Δ) := by
  have h := yoyConvexity_eq mn (mrBase + Δ) Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov
    hVn hVr hρ hCov hZ1 hZ2 hZ1m hZ2m hindep
  rw [h]
  have hex : Bn * mn - Br * (mrBase + Δ) + Bn ^ 2 * Vn - Br * Bn * Cov
      = Bn * mn - Br * mrBase + Bn ^ 2 * Vn - Br * Bn * Cov - Br * Δ := by ring
  rw [hex]


omit [IsProbabilityMeasure μ] in
/-- **`ρ_{rI} = 0` deletes exactly the quanto piece** (the chapter's reading remark,
p. 296). When the index/real-rate correlation vanishes, the quanto parent `Δ` is zero,
and by `yoyConvexity_delta` it leaves the correction exponent **only** through the
additive `−Bʳ·Δ` seat — so the correction with `Δ = 0` is exactly the correction
without the quanto parent: nothing else moves. -/
theorem yoyConvexity_quanto_deleted (mn mrBase Δ Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    (hΔ : Δ = 0)
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hZ1m : Measurable Z1) (hZ2m : Measurable Z2) (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (hwD Br Vr - hwD Bn Vn
        + (Bn * (mn + Real.sqrt Vn * Z1 ω)
          - Br * (mrBase + Δ + Real.sqrt Vr * (ρ * Z1 ω
            + Real.sqrt (1 - ρ ^ 2) * Z2 ω)))) ∂μ
      = (Pr0T * Pn0S / (Pr0S * Pn0T))
        * Real.exp (Bn * mn - Br * mrBase + Bn ^ 2 * Vn - Br * Bn * Cov) := by
  have h := yoyConvexity_delta mn mrBase Δ Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov
    hVn hVr hρ hCov hZ1 hZ2 hZ1m hZ2m hindep
  rw [h, hΔ]
  have hex : Bn * mn - Br * mrBase + Bn ^ 2 * Vn - Br * Bn * Cov - Br * 0
      = Bn * mn - Br * mrBase + Bn ^ 2 * Vn - Br * Bn * Cov := by ring
  rw [hex]


end MathFin.Inflation.Convexity
