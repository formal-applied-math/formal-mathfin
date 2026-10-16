/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.Numeraire
public import MathFin.Foundations.BrownianMartingale

/-!
# Inflation is FX: the zero-coupon inflation swap and the YoY convexity

The Jarrow–Yildirim identification reads the price index `I_t` as an exchange rate
(nominal currency per real good) and the index-linked bond as a bond denominated in
goods. Under that identification the modelling content is one postulate — the
index-linked bond `I_t·Pʳ(t,T)` is a nominal tradable, priced on the real curve — and
everything else in the zero-coupon inflation swap is change-of-numéraire bookkeeping
(`forwardIndex_eq`, `breakeven_eq`: eqs. 17.6/17.7 of the chapter).

The year-on-year convexity is the quanto correction transplanted to the nominal/real
rate pair: with both rates Gaussian, the expectation of the exponential of the two-rate
deviation is computed by the same ρ-decomposition of a correlated driver into
independent normals that powers `MathFin.quantoForward_of_gaussian`
(`MathFin.BlackScholes.QuantoGrounding`), with the 1-D Gaussian MGF
`integral_exp_mul_gaussianReal_zero` (`MathFin.Foundations.BrownianMartingale`) applied
twice (`yoyRatioExp_gaussian`).
Composing with the Hull–White bond-reconstitution deterministics `Dⁱ = −½Bⁱ²Vⁱ`
collapses the exponent — the real-variance halves cancel, the nominal halves double — to
the chapter's eq. (17.10) (`yoyConvexity_eq`), with the naive ratio of forwards carried
as an explicit multiplicative constant.

## Scope

Out of scope, and not claimed: eq. (17.8)'s conditional identity as a named lemma (the
landed anchor is `MathFin.changeOfNumeraire_setIntegral_eq`); eq. (17.9)'s SDE-level
drift-shift derivation `δ = −ρ_{rI}σ_rσ_I`; the two-correlated-Hull–White dynamics (the
means, variances and covariance of the rate deviations are explicit inputs here); and the
chapter's numeric tables. The Jarrow–Yildirim identification is a hypothesis (`hident`),
never derived.

## References

* A. Bagaria, *Fixed Income & Derivative Pricing* (lecture notes), ch. 17 §§17.3–17.4
  ("the chapter" throughout); the Hull–White reconstitution formula is from its ch. 8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

/-! ## The zero-coupon inflation swap (eqs. 17.6/17.7)

`Qⁿ` is the nominal pricing measure, `B_T` the money-market account at
`T` (a strictly positive random variable), `Pⁿ₀T = Pⁿ(0,T)` and `Pʳ₀T = Pʳ(0,T)` the
nominal and real T-bond prices, `I₀` today's index and `I_T` the terminal index. The
**identification hypothesis** `hident` is the chapter's postulate verbatim: the
index-linked bond, paying `I_T` at `T`, is priced on the real curve, `𝔼^{Qⁿ}[I_T/B_T]
= I₀·Pʳ(0,T)`.

In `forwardIndex_eq` and `breakeven_eq`, `Pⁿ₀T` enters only as the normalising constant
`N₀` of the tilted measure `numeraireMeasure Qⁿ B_T 1 1 Pⁿ₀T`; the statements do **not**
tie it to `𝔼^{Qⁿ}[1/B_T]`. When they agree and `1/B_T` is integrable, that measure is a
probability measure — the nominal T-forward measure
(`MathFin.numeraireMeasure_isProbabilityMeasure`); the identities themselves hold for any
`Pⁿ₀T > 0`. -/
namespace MathFin.Inflation.ZCSwap

variable {Ω : Type*} [MeasurableSpace Ω] {Qn : Measure Ω}

/-- **The forward index (eq. 17.6).** Under the Jarrow–Yildirim identification
(`hident`: the index-linked bond priced on the real curve), the index under the
numéraire measure of the T-bond — terminal value `1`, initial price `Pⁿ₀T` — is the
real-curve/nominal-curve ratio:

  `𝔼^{Q^{n,T}}[I_T] = I₀ · Pʳ(0,T) / Pⁿ(0,T)`.

That measure is the nominal T-forward measure when `Pⁿ₀T = 𝔼^{Qⁿ}[1/B_T]`, which the
statement does not assume (see the section note). The proof is
`MathFin.changeOfNumeraire` at `X := I_T`, `N_T ≡ 1`, `N₀ = Pⁿ₀T`, `B₀ = 1`, plus field
algebra; no integrability hypothesis is needed. -/
theorem forwardIndex_eq (BT : Ω → ℝ) (Pn0T Pr0T I0 : ℝ) (IT : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hident : ∫ ω, IT ω / BT ω ∂Qn = I0 * Pr0T) :
    ∫ ω, IT ω ∂(MathFin.numeraireMeasure Qn BT (fun _ ↦ 1) 1 Pn0T) = I0 * Pr0T / Pn0T := by
  have h := MathFin.changeOfNumeraire (Q := Qn) (BT := BT) (NT := fun _ ↦ 1) (B0 := 1)
    (N0 := Pn0T) IT measurable_const hBTmeas (fun _ ↦ zero_lt_one) hBTpos zero_le_one hPn0T
  rw [eq_div_iff hPn0T.ne', mul_comm]
  simpa [hident] using h

/-- **The spot price of the index-linked bond** — for contrast with
`forwardIndex_eq`. The numéraire-measure instantiation
`numeraireMeasure Qn BT (fun _ ↦ Pn0T) 1 Pn0T` has density `Pⁿ₀T/(Pⁿ₀T·B_T) = 1/B_T`
(the `N_T` and `N₀` slots cancel), so it is the discount-weighted measure
`Qⁿ.withDensity(1/B_T)`, not the T-forward measure: its `I_T`-integral is, by the
identification `hident`, the spot price `I₀·Pʳ(0,T)` — with **no** division by `Pⁿ₀T`.
Eq. (17.6)'s forward needs `forwardIndex_eq`'s instantiation instead. -/
theorem indexLinkedPrice_eq (BT : Ω → ℝ) (Pn0T Pr0T I0 : ℝ) (IT : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hident : ∫ ω, IT ω / BT ω ∂Qn = I0 * Pr0T) :
    ∫ ω, IT ω ∂(MathFin.numeraireMeasure Qn BT (fun _ ↦ Pn0T) 1 Pn0T) = I0 * Pr0T := by
  have h := MathFin.changeOfNumeraire (Q := Qn) (BT := BT) (NT := fun _ ↦ Pn0T) (B0 := 1)
    (N0 := Pn0T) IT measurable_const hBTmeas (fun _ ↦ hPn0T) hBTpos zero_le_one hPn0T
  simp only [one_mul, div_eq_inv_mul (IT _) Pn0T, integral_const_mul, hident] at h
  field_simp at h
  exact h

/-- **The breakeven inflation rate (eq. 17.7).** A zero-coupon inflation swap pays
`I_T/I₀ − (1+b)^T` at `T`; `b` is quoted as the breakeven. Fairness (`hfair`: under the
T-bond numéraire measure — the nominal T-forward measure under the section's
normalisation — the fixed leg `I₀(1+b)^T` matches the floating leg `I_T`)
combined with eq. (17.6) — so under the identification `hident` — gives the curve-only
breakeven identity

  `(1+b)^T = Pʳ(0,T) / Pⁿ(0,T)`,

with `T : ℕ` the swap's maturity in whole years (only the `(1+b)^T` exponent; `B_T`, `I_T`
are simply terminal random variables). The breakeven is a *ratio of bond prices*, not a
physical-measure expectation of inflation — the chapter's central warning. -/
theorem breakeven_eq (BT : Ω → ℝ) (Pn0T Pr0T I0 b : ℝ) (T : ℕ) (IT : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T) (hI0 : 0 < I0)
    (hident : ∫ ω, IT ω / BT ω ∂Qn = I0 * Pr0T)
    (hfair : ∫ ω, IT ω ∂(MathFin.numeraireMeasure Qn BT (fun _ ↦ 1) 1 Pn0T)
      = I0 * (1 + b) ^ T) :
    (1 + b) ^ T = Pr0T / Pn0T := by
  have hf := forwardIndex_eq BT Pn0T Pr0T I0 IT hBTpos hBTmeas hPn0T hident
  rw [hfair, mul_div_assoc] at hf
  exact mul_left_cancel₀ hI0.ne' hf

end MathFin.Inflation.ZCSwap

/-! ## The YoY Gaussian core (eq. 17.10's expectation layer)

With both rates Gaussian, the year-on-year ratio's convexity is an expectation of an
exponential of a normal. `yoyRatioExp_gaussian` computes it: two rate deviations
`yⁿ = mⁿ + √Vⁿ·Z₁` and `yʳ = mʳ + √Vʳ·(ρ·Z₁ + √(1−ρ²)·Z₂)` from independent standard
normals — the ρ-decomposition of the correlated two-rate driver, exactly the shape of
`MathFin.quantoForward_of_gaussian` — with means `mⁿ, mʳ`, variances `Vⁿ, Vʳ`,
correlation `ρ`, and Hull–White factors `Bⁿ, Bʳ` over `[S, T]`. -/
namespace MathFin.Inflation.Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Standard-normal MGF** via `HasLaw` transfer: `𝔼[exp(a·Z)] = exp(a²/2)` for
`Z ~ N(0,1)` — the mirror of `MathFin.BlackScholes.QuantoGrounding`'s private helper,
backed by `integral_exp_mul_gaussianReal_zero`. -/
private lemma integral_exp_mul_stdNormal {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) μ) (a : ℝ) :
    ∫ ω, Real.exp (a * Z ω) ∂μ = Real.exp (a ^ 2 / 2) := by
  simpa using (hZ.integral_comp (f := fun x : ℝ ↦ Real.exp (a * x)) (by fun_prop)).trans
    (integral_exp_mul_gaussianReal_zero a 1)

/-- **The two-rate exponential moment (eq. 17.10's Gaussian core).** For independent
standard normals `Z₁, Z₂` and Gaussian rate deviations `yⁿ = mⁿ + √Vⁿ·Z₁` and
`yʳ = mʳ + √Vʳ·(ρ·Z₁ + √(1−ρ²)·Z₂)` (so `Cov(yⁿ, yʳ) = ρ·√(Vⁿ·Vʳ)`),

  `𝔼[exp(Bⁿ·yⁿ − Bʳ·yʳ)] = exp(Bⁿ·mⁿ − Bʳ·mʳ + ½(Bⁿ²Vⁿ + Bʳ²Vʳ − 2·Bⁿ·Bʳ·ρ·√(VⁿVʳ)))`.

The proof is the `quantoForward_of_gaussian` pattern: pointwise
factorization into `exp(const)·exp(a·Z₁)·exp(b·Z₂)` with `a = Bⁿ√Vⁿ − Bʳρ√Vʳ` and
`b = −Bʳ√(1−ρ²)√Vʳ`, independence factorization of the integral, and two applications
of the 1-D Gaussian MGF; the cross term `−2BⁿBʳρ√(VⁿVʳ)` is the `a²` algebra. -/
theorem yoyRatioExp_gaussian (mn mr Vn Vr ρ Bn Br : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1)
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, Real.exp (Bn * (mn + Real.sqrt Vn * Z1 ω)
        - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))) ∂μ
      = Real.exp (Bn * mn - Br * mr
          + (Bn ^ 2 * Vn + Br ^ 2 * Vr - 2 * Bn * Br * ρ * Real.sqrt (Vn * Vr)) / 2) := by
  have h1r2 : (0 : ℝ) ≤ 1 - ρ ^ 2 := by linarith
  set E : ℝ := Bn * mn - Br * mr
  set a : ℝ := Bn * Real.sqrt Vn - Br * ρ * Real.sqrt Vr with ha
  set b : ℝ := -(Br * Real.sqrt (1 - ρ ^ 2)) * Real.sqrt Vr with hb
  -- Pointwise: the integrand is the constant `exp E` times the two single-driver exponentials.
  have hpt : (fun ω ↦ Real.exp (Bn * (mn + Real.sqrt Vn * Z1 ω)
        - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))))
      = fun ω ↦ Real.exp E * (Real.exp (a * Z1 ω) * Real.exp (b * Z2 ω)) := by
    funext ω
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [E, a, b]
    ring
  -- Independence factorization of the two single-driver exponentials.
  have hindep_exp : IndepFun (fun ω ↦ Real.exp (a * Z1 ω)) (fun ω ↦ Real.exp (b * Z2 ω)) μ :=
    hindep.comp (by fun_prop : Measurable fun x ↦ Real.exp (a * x))
      (by fun_prop : Measurable fun x ↦ Real.exp (b * x))
  have hprod : ∫ ω, Real.exp (a * Z1 ω) * Real.exp (b * Z2 ω) ∂μ
      = Real.exp (a ^ 2 / 2) * Real.exp (b ^ 2 / 2) := by
    rw [← integral_exp_mul_stdNormal hZ1 a, ← integral_exp_mul_stdNormal hZ2 b]
    exact hindep_exp.integral_mul_eq_mul_integral
      (by have := hZ1.aemeasurable; fun_prop) (by have := hZ2.aemeasurable; fun_prop)
  rw [hpt, integral_const_mul, hprod, ← Real.exp_add, ← Real.exp_add]
  -- The `a²` algebra: the cross term `−2·Bⁿ·Bʳ·ρ·√(VⁿVʳ)` emerges from `(Bⁿ√Vⁿ − Bʳρ√Vʳ)²`.
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

/-- **Covariance form of the two-rate exponential moment.** The same conclusion with the
correlation slot replaced by the covariance `Cov = ρ·√(Vⁿ·Vʳ)` of the two rate deviations
(the form in which eq. 17.10 is stated in the chapter). -/
theorem yoyRatioExp_gaussian_cov (mn mr Vn Vr ρ Bn Br Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, Real.exp (Bn * (mn + Real.sqrt Vn * Z1 ω)
        - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))) ∂μ
      = Real.exp (Bn * mn - Br * mr
          + (Bn ^ 2 * Vn + Br ^ 2 * Vr - 2 * Bn * Br * Cov) / 2) := by
  rw [hCov, yoyRatioExp_gaussian mn mr Vn Vr ρ Bn Br hVn hVr hρ hZ1 hZ2 hindep]
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

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The reconstitution deterministic** `Dⁱ = −½·Bⁱ²·Vⁱ` of the Hull–White bond
reconstitution formula: the deterministic part of bond `i`'s [S,T]-factor, with `Bⁱ`
the Hull–White factor and `Vⁱ` the integrated variance. That `Dʳ − Dⁿ = (Bⁿ²Vⁿ − Bʳ²Vʳ)/2`
exactly cancels the real variance's half and doubles the nominal variance's half in
`yoyRatioExp_gaussian_cov`'s exponent is the collapse mechanism of `yoyConvexity_eq`. -/
noncomputable def hwD (B V : ℝ) : ℝ := -(B ^ 2 * V) / 2

/-- **The year-on-year convexity closed form (eq. 17.10, exact chapter shape).** With
the reconstituted bond-ratio factor — the naive ratio of forwards
`Pʳ₀T·Pⁿ₀S/(Pʳ₀S·Pⁿ₀T)` times `e^{Dʳ−Dⁿ−Bʳyʳ+Bⁿyⁿ}` with `Dⁱ = −½Bⁱ²Vⁱ` (the `hwD`
below) — the Gaussian expectation collapses to the naive ratio times the correction

  `C = exp(Bⁿ·mⁿ − Bʳ·mʳ + Bⁿ²·Vⁿ − Bʳ·Bⁿ·Cov)`,

the chapter's eq. (17.10) verbatim, with `Cov = ρ·√(VⁿVʳ)` the covariance of the two
rate deviations. The exponent's composition is pure algebra on
`yoyRatioExp_gaussian_cov`: `(Dʳ−Dⁿ) = (Bⁿ²Vⁿ − Bʳ²Vʳ)/2` cancels the *real*
variance's half exactly and doubles the *nominal* variance's half. The means `mⁿ, mʳ`,
variances and `Cov` are inputs: where they come from (two correlated Hull–White fits, the
quanto parent `−ρ_{rI}σ_rσ_I` and the forward-measure parent `−ρ_{nr}σ_nσ_rBⁿ` inside
them) is chapter-sourced interpretation, not proved here. -/
theorem yoyConvexity_eq (mn mr Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (hwD Br Vr - hwD Bn Vn
        + (Bn * (mn + Real.sqrt Vn * Z1 ω)
          - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω)))) ∂μ
      = (Pr0T * Pn0S / (Pr0S * Pn0T))
        * Real.exp (Bn * mn - Br * mr + Bn ^ 2 * Vn - Br * Bn * Cov) := by
  have hkey := Gaussian.yoyRatioExp_gaussian_cov mn mr Vn Vr ρ Bn Br Cov hVn hVr hρ hCov
    hZ1 hZ2 hindep
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

/-- **The quanto seat of the mean (the `Δ`-linearity).** Writing the real rate's mean as
`mʳ = mʳbase + Δ`, the correction exponent carries `Δ` **exactly** as the additive piece
`−Bʳ·Δ` and in no other way — pure specialization of `yoyConvexity_eq`. Reading `Δ` as
the quanto parent's contribution to `mʳ` (the mean shift induced by the `−ρ_{rI}σ_rσ_I`
piece of eq. 17.9's drift, which the chapter, p. 295, places inside `mʳ` under the
Jarrow–Yildirim identification) is chapter-sourced interpretation; `Δ` is an arbitrary
real here. -/
theorem yoyConvexity_delta (mn mrBase Δ Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (hwD Br Vr - hwD Bn Vn
        + (Bn * (mn + Real.sqrt Vn * Z1 ω)
          - Br * (mrBase + Δ + Real.sqrt Vr * (ρ * Z1 ω
            + Real.sqrt (1 - ρ ^ 2) * Z2 ω)))) ∂μ
      = (Pr0T * Pn0S / (Pr0S * Pn0T))
        * Real.exp (Bn * mn - Br * mrBase + Bn ^ 2 * Vn - Br * Bn * Cov - Br * Δ) := by
  rw [yoyConvexity_eq mn (mrBase + Δ) Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov
    hVn hVr hρ hCov hZ1 hZ2 hindep]
  congr 2
  ring

/-- **`Δ = 0` deletes exactly the quanto seat.** By `yoyConvexity_delta`, `Δ` enters the
correction exponent only through the additive `−Bʳ·Δ`, so at `Δ = 0` the correction is
exactly the one computed from `mʳbase`: nothing else moves. The chapter's reading remark
(p. 296) is that `ρ_{rI} = 0` (index/real-rate correlation) gives `Δ = 0`; that link is
chapter-sourced and not modelled here — the hypothesis is `Δ = 0` itself. -/
theorem yoyConvexity_quanto_deleted (mn mrBase Δ Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    (hΔ : Δ = 0)
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (hwD Br Vr - hwD Bn Vn
        + (Bn * (mn + Real.sqrt Vn * Z1 ω)
          - Br * (mrBase + Δ + Real.sqrt Vr * (ρ * Z1 ω
            + Real.sqrt (1 - ρ ^ 2) * Z2 ω)))) ∂μ
      = (Pr0T * Pn0S / (Pr0S * Pn0T))
        * Real.exp (Bn * mn - Br * mrBase + Bn ^ 2 * Vn - Br * Bn * Cov) := by
  rw [yoyConvexity_delta mn mrBase Δ Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov
    hVn hVr hρ hCov hZ1 hZ2 hindep, hΔ, mul_zero, sub_zero]

end MathFin.Inflation.Convexity
