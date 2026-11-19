/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.Forward
public import MathFin.Models.BlackScholes.Put
public import MathFin.Models.Forwards.Black76
public import MathFin.Models.Rates.Inflation
public import MathFin.Models.Rates.VasicekBondPrice

/-!
# Jarrow–Yildirim: the index variance, the zero-coupon caplet and the YoY forward

In the Jarrow–Yildirim model the nominal and real short rates are Gaussian (Hull–White) and
the price index is a geometric Brownian motion, with three pairwise correlations. The forward
index `F(t,T) = I_t·Pʳ(t,T)/Pⁿ(t,T)` is a martingale under the nominal `T`-forward measure.
This module records what follows from that structure without the SDE calculus.

## Main definitions

* `jyVarIntegrand`: the variance integrand of `log F(·,T)` with constant parameters.
* `jyVariance`: its integral `V(0,T)`.
* `jyCorrDet`: the determinant of the `(I, r, n)` correlation matrix.

## Main results

* The variance integrand of `log F(·,T)` for constant parameters (`jyVarIntegrand`) and its
  integral `V(0,T)` (`jyVariance`). The integrand is the quadratic form of the vector
  `(σ_I, −σ_r·B_r, σ_n·B_n)` against the `(I, r, n)` correlation matrix
  (`jyVarIntegrand_eq_quadForm`), hence non-negative when that matrix is positive
  semidefinite (`jyVarIntegrand_nonneg`). Pairwise `|ρ| ≤ 1` is not enough for three factors;
  the condition used is the determinant form `jyCorrDet ≥ 0`. Degenerate reductions:
  `jyVariance_eq_of_zero_rate_vols` and `jyVariance_eq_zero_of_zero_vols`.
* The zero-coupon inflation caplet and floorlet (`jyZcCaplet_eq_black`, `jyZcFloorlet_eq_black`,
  `jyZcCaplet_floorlet_parity`): if the index under the nominal `T`-forward measure is lognormal
  with log-variance `V` and the index-linked bond is priced on the real curve, the caplet is
  the library's Black caplet on the curve forward `I₀·Pʳ(0,T)/Pⁿ(0,T)` at total variance `V`.
* The year-on-year forward (`jyYoyForward_eq_bondRatio`, `jyYoyForward_eq_convexity`): from
  the martingale property of `F(·,T)` under the `T`-forward measure, `𝔼^T[I_T/I_S]` is the
  expectation of the bond-price ratio `Pʳ(S,T)/Pⁿ(S,T)`, which `yoyConvexity_eq` evaluates as
  the naive ratio of forwards times the convexity factor. `jyYoyPayment_price` is the time-0
  value of that payment (`MathFin.forwardMeasure_price`).

## What is not proved

The SDE-level derivation of the `−ρ_{rI}σ_rσ_I` drift of the real rate and of `V` from the
three SDEs is not claimed: `V` is defined, and the lognormality of the index (`hT`), the
martingale property of the forward index (`hmart`) and the Hull–White bond-reconstitution form
of the bond ratio (`hR`) are hypotheses. The paper itself was not available to the author; the
model form follows the secondary sources below. The exact YoY caplet, calibration,
seasonality and Monte Carlo are out of scope.

## References

* [R. Jarrow and Y. Yildirim, *Pricing Treasury Inflation Protected Securities and Related
  Derivatives using an HJM Model*, J. Financial and Quantitative Analysis 38(2) (2003),
  337–358][JarrowYildirim2003]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  2nd ed. (2006), ch. 15
* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 17 §17.3, eq. 17.10

## Tags

Jarrow–Yildirim, inflation model, zero-coupon inflation cap, year-on-year inflation,
convexity adjustment, Hull–White, MSC 91G30, MSC 91G20, JEL E31
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathFin.Inflation.JarrowYildirim

/-! ### The variance integrand -/

/-- The Jarrow–Yildirim variance integrand at time `t` for the forward index `F(·,T)`, with
constant parameters: `a_r, a_n` mean reversions, `σ_I, σ_r, σ_n` volatilities, `ρ_{rI}, ρ_{nI},
ρ_{nr}` correlations. The Hull–White loadings are the library's `vasicekBondB` at the
remaining maturity `T − t`:

  `σ_I² + σ_r²B_r² + σ_n²B_n² − 2ρ_{rI}σ_Iσ_rB_r + 2ρ_{nI}σ_Iσ_nB_n − 2ρ_{nr}σ_nσ_rB_nB_r`. -/
noncomputable def jyVarIntegrand (ar an σI σr σn ρrI ρnI ρnr T t : ℝ) : ℝ :=
  σI ^ 2 + σr ^ 2 * vasicekBondB ar (T - t) ^ 2 + σn ^ 2 * vasicekBondB an (T - t) ^ 2
    - 2 * ρrI * σI * σr * vasicekBondB ar (T - t)
    + 2 * ρnI * σI * σn * vasicekBondB an (T - t)
    - 2 * ρnr * σn * σr * vasicekBondB an (T - t) * vasicekBondB ar (T - t)

/-- The integrated variance `V(0,T) = ∫₀ᵀ jyVarIntegrand dt`. -/
noncomputable def jyVariance (ar an σI σr σn ρrI ρnI ρnr T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, jyVarIntegrand ar an σI σr σn ρrI ρnI ρnr T t

/-- The determinant of the `(I, r, n)` correlation matrix
`[[1, ρ_{rI}, ρ_{nI}], [ρ_{rI}, 1, ρ_{nr}], [ρ_{nI}, ρ_{nr}, 1]]`. Together with
`ρ_{rI}² ≤ 1` it is the positive-semidefiniteness condition. -/
def jyCorrDet (ρrI ρnI ρnr : ℝ) : ℝ :=
  1 + 2 * ρrI * ρnI * ρnr - ρrI ^ 2 - ρnI ^ 2 - ρnr ^ 2

/-- The `2×2` quadratic form `A y² + 2B yz + C z²` is non-negative when `A, C ≥ 0` and
`B² ≤ A·C`. -/
theorem quad2_nonneg {A B C y z : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : B ^ 2 ≤ A * C) :
    0 ≤ A * y ^ 2 + 2 * B * y * z + C * z ^ 2 := by
  rcases hA.eq_or_lt with h0 | hpos
  · subst h0
    have hB0 : B = 0 := by nlinarith [sq_nonneg B]
    subst hB0
    nlinarith [mul_nonneg hC (sq_nonneg z)]
  · have h : 0 ≤ A * (A * y ^ 2 + 2 * B * y * z + C * z ^ 2) := by
      nlinarith [sq_nonneg (A * y + B * z), mul_nonneg (sub_nonneg.2 hB) (sq_nonneg z)]
    exact nonneg_of_mul_nonneg_right h hpos

/-- **Three-factor quadratic form.** For correlations with `ρ_{rI}² ≤ 1`, `ρ_{nI}² ≤ 1`
and `jyCorrDet ≥ 0`, `x² + y² + z² + 2ρ_{rI}xy + 2ρ_{nI}xz + 2ρ_{nr}yz ≥ 0`. -/
theorem quad3_nonneg {a b c x y z : ℝ} (ha : a ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1)
    (hdet : 0 ≤ jyCorrDet a b c) :
    0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + 2 * a * x * y + 2 * b * x * z + 2 * c * y * z := by
  have key := quad2_nonneg (A := 1 - a ^ 2) (B := c - a * b) (C := 1 - b ^ 2) (y := y) (z := z)
    (by linarith) (by linarith) (by unfold jyCorrDet at hdet; nlinarith)
  nlinarith [sq_nonneg (x + a * y + b * z)]

/-- The integrand is the quadratic form of `(σ_I, −σ_r·B_r, σ_n·B_n)` against the
`(I, r, n)` correlation matrix: the variance of `σ_I dW_I − σ_rB_r dW_r + σ_nB_n dW_n`. -/
theorem jyVarIntegrand_eq_quadForm (ar an σI σr σn ρrI ρnI ρnr T t : ℝ) :
    jyVarIntegrand ar an σI σr σn ρrI ρnI ρnr T t
      = σI ^ 2 + (-(σr * vasicekBondB ar (T - t))) ^ 2 + (σn * vasicekBondB an (T - t)) ^ 2
        + 2 * ρrI * σI * (-(σr * vasicekBondB ar (T - t)))
        + 2 * ρnI * σI * (σn * vasicekBondB an (T - t))
        + 2 * ρnr * (-(σr * vasicekBondB ar (T - t))) * (σn * vasicekBondB an (T - t)) := by
  unfold jyVarIntegrand
  ring

/-- **The variance integrand is non-negative** under the correlation PSD condition
(`ρ_{rI}² ≤ 1`, `ρ_{nI}² ≤ 1`, `jyCorrDet ≥ 0`), for every `t`. -/
theorem jyVarIntegrand_nonneg {ar an σI σr σn ρrI ρnI ρnr : ℝ} (T t : ℝ)
    (hrI : ρrI ^ 2 ≤ 1) (hnI : ρnI ^ 2 ≤ 1) (hdet : 0 ≤ jyCorrDet ρrI ρnI ρnr) :
    0 ≤ jyVarIntegrand ar an σI σr σn ρrI ρnI ρnr T t := by
  rw [jyVarIntegrand_eq_quadForm]
  exact quad3_nonneg hrI hnI hdet

/-- **The integrated variance `V(0,T)` is non-negative** for `0 ≤ T` under the PSD condition. -/
theorem jyVariance_nonneg {ar an σI σr σn ρrI ρnI ρnr : ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hrI : ρrI ^ 2 ≤ 1) (hnI : ρnI ^ 2 ≤ 1) (hdet : 0 ≤ jyCorrDet ρrI ρnI ρnr) :
    0 ≤ jyVariance ar an σI σr σn ρrI ρnI ρnr T :=
  intervalIntegral.integral_nonneg hT fun t _ => jyVarIntegrand_nonneg T t hrI hnI hdet

/-- **Zero rate volatilities.** With `σ_r = σ_n = 0` only the index volatility remains:
`V(0,T) = σ_I²·T`. -/
theorem jyVariance_eq_of_zero_rate_vols (ar an σI ρrI ρnI ρnr T : ℝ) :
    jyVariance ar an σI 0 0 ρrI ρnI ρnr T = σI ^ 2 * T := by
  unfold jyVariance jyVarIntegrand
  simp
  ring

/-- **All volatilities zero** gives `V(0,T) = 0`. -/
theorem jyVariance_eq_zero_of_zero_vols (ar an ρrI ρnI ρnr T : ℝ) :
    jyVariance ar an 0 0 0 ρrI ρnI ρnr T = 0 := by
  simp [jyVariance_eq_of_zero_rate_vols]


/-! ### The zero-coupon inflation caplet and floorlet

`Qn` is the nominal pricing measure with money-market account `BT`, and `Q^T` its nominal
`T`-forward measure (`MathFin.forwardMeasure`). The hypotheses are: the index-linked bond is
priced on the real curve (`hident`, as in `ZCSwap.forwardIndex_eq`), and under `Q^T` the index
is lognormal, `I_T = F₀·exp(−V/2 + √V·Z)` with `Z ~ N(0,1)` — the log-variance `V` being
`jyVariance` when the SDE-level derivation is granted (not derived here). The caplet pays
`(I_T − K)⁺` at `T` and is priced with the nominal bond `Pⁿ(0,T)` as numéraire. -/

section Caplet

variable {Ω : Type*} [MeasurableSpace Ω] {Qn : Measure Ω}

/-- **The lognormal forward index sits on the curve forward.** If `I_T = F₀·exp(−V/2 + √V·Z)`
with `Z ~ N(0,1)` under the nominal `T`-forward measure, then the index-linked-bond
identification forces `F₀ = I₀·Pʳ(0,T)/Pⁿ(0,T)` (`ZCSwap.forwardIndex_eq`). -/
theorem jyForwardIndex_lognormal_eq_curves (BT : Ω → ℝ) (Pn0T Pr0T I0 F0 V : ℝ) (Z : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hP : Pn0T = ∫ ω, 1 / BT ω ∂Qn)
    (hident : ∫ ω, (fun ω => bsTerminal F0 0 (Real.sqrt V) 1 (Z ω)) ω / BT ω ∂Qn = I0 * Pr0T)
    (hZ : HasLaw Z (gaussianReal 0 1) (MathFin.forwardMeasure Qn BT)) :
    F0 = I0 * Pr0T / Pn0T := by
  have h := ZCSwap.forwardIndex_eq (Qn := Qn) BT Pn0T Pr0T I0
    (fun ω => bsTerminal F0 0 (Real.sqrt V) 1 (Z ω)) hBTpos hBTmeas hPn0T hP hident
  have hmeas : AEStronglyMeasurable (fun z => bsTerminal F0 0 (Real.sqrt V) 1 z)
      (gaussianReal 0 1) := by
    unfold bsTerminal; fun_prop
  rw [show (fun ω => bsTerminal F0 0 (Real.sqrt V) 1 (Z ω))
      = (fun z => bsTerminal F0 0 (Real.sqrt V) 1 z) ∘ Z from rfl,
    hZ.integral_comp hmeas] at h
  have h2 := integral_bsTerminal_eq_forward F0 0 (Real.sqrt V) 1 zero_le_one
  simp only [Real.exp_zero, mul_one] at h2
  rw [← h]
  simpa [bsTerminal] using h2.symm

/-- **ZC inflation caplet = Black caplet on the curve forward.** Under `hident` and a
lognormal index under `Q^T` with log-variance `V > 0`, positive `F₀`-curve forward and `K > 0`,

  `Pⁿ(0,T)·𝔼^{Q^T}[(I_T − K)⁺] = blackCaplet (I₀Pʳ(0,T)/Pⁿ(0,T)) K √V 1 Pⁿ(0,T)`,

i.e. `Pⁿ·[F Φ(d₁) − K Φ(d₂)]` with `d_i = bsd_i F K 0 √V 1`. The index law is a hypothesis;
that its log-variance is `jyVariance` is the SDE-level content, not proved. -/
theorem jyZcCaplet_eq_black (BT : Ω → ℝ) [IsProbabilityMeasure (MathFin.forwardMeasure Qn BT)]
    (Pn0T Pr0T I0 F0 V K : ℝ) (Z : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hP : Pn0T = ∫ ω, 1 / BT ω ∂Qn)
    (hident : ∫ ω, (fun ω => bsTerminal F0 0 (Real.sqrt V) 1 (Z ω)) ω / BT ω ∂Qn = I0 * Pr0T)
    (hZ : HasLaw Z (gaussianReal 0 1) (MathFin.forwardMeasure Qn BT))
    (hF0 : 0 < F0) (hV : 0 < V) (hK : 0 < K) :
    Pn0T * ∫ ω, max (bsTerminal F0 0 (Real.sqrt V) 1 (Z ω) - K) 0
        ∂(MathFin.forwardMeasure Qn BT)
      = blackCaplet (I0 * Pr0T / Pn0T) K (Real.sqrt V) 1 Pn0T := by
  have hF := jyForwardIndex_lognormal_eq_curves BT Pn0T Pr0T I0 F0 V Z hBTpos hBTmeas hPn0T hP
    hident hZ
  have hyp : BSCallHyp (MathFin.forwardMeasure Qn BT) F0 K 0 (Real.sqrt V) 1 Z :=
    ⟨hF0, hK, Real.sqrt_pos.2 hV, one_pos, hZ⟩
  have h := black_futures_formula hyp 0
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at h
  rw [h, ← hF]
  unfold blackCaplet
  ring

/-- **ZC inflation floorlet = Black floorlet on the curve forward**, the put counterpart of
`jyZcCaplet_eq_black` under the same hypotheses. -/
theorem jyZcFloorlet_eq_black (BT : Ω → ℝ) [IsProbabilityMeasure (MathFin.forwardMeasure Qn BT)]
    (Pn0T Pr0T I0 F0 V K : ℝ) (Z : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hP : Pn0T = ∫ ω, 1 / BT ω ∂Qn)
    (hident : ∫ ω, (fun ω => bsTerminal F0 0 (Real.sqrt V) 1 (Z ω)) ω / BT ω ∂Qn = I0 * Pr0T)
    (hZ : HasLaw Z (gaussianReal 0 1) (MathFin.forwardMeasure Qn BT))
    (hF0 : 0 < F0) (hV : 0 < V) (hK : 0 < K) :
    Pn0T * ∫ ω, max (K - bsTerminal F0 0 (Real.sqrt V) 1 (Z ω)) 0
        ∂(MathFin.forwardMeasure Qn BT)
      = blackFloorlet (I0 * Pr0T / Pn0T) K (Real.sqrt V) 1 Pn0T := by
  have hF := jyForwardIndex_lognormal_eq_curves BT Pn0T Pr0T I0 F0 V Z hBTpos hBTmeas hPn0T hP
    hident hZ
  have hyp : BSCallHyp (MathFin.forwardMeasure Qn BT) F0 K 0 (Real.sqrt V) 1 Z :=
    ⟨hF0, hK, Real.sqrt_pos.2 hV, one_pos, hZ⟩
  have h := bs_put_formula hyp
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at h
  rw [h, ← hF]
  unfold blackFloorlet
  ring

/-- **Caplet–floorlet parity** for the ZC inflation options: the Black caplet minus floorlet
is `Pⁿ(0,T)·(I₀Pʳ(0,T)/Pⁿ(0,T) − K) = I₀Pʳ(0,T) − K·Pⁿ(0,T)`, the price of the
zero-coupon inflation swap with fixed leg `K`. Pure algebra on `caplet_floorlet_parity`. -/
theorem jyZcCaplet_floorlet_parity (Pn0T Pr0T I0 V K : ℝ) (hPn0T : 0 < Pn0T) :
    blackCaplet (I0 * Pr0T / Pn0T) K (Real.sqrt V) 1 Pn0T
      - blackFloorlet (I0 * Pr0T / Pn0T) K (Real.sqrt V) 1 Pn0T = I0 * Pr0T - K * Pn0T := by
  rw [caplet_floorlet_parity]
  field_simp

end Caplet

/-! ### The year-on-year forward

`μ` is the nominal `T`-forward measure and `m_S ≤ m` the information at `S`. The forward index
`F(S,T) = I_S·Pʳ(S,T)/Pⁿ(S,T)` is a `μ`-martingale (`hmart`: `𝔼^T[I_T | m_S] = I_S·R_S` with
`R_S = Pʳ(S,T)/Pⁿ(S,T)`, using `F(T,T) = I_T`). This is the modelling hypothesis, disclosed
as such; the tower property does the rest. -/

section Yoy

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- **YoY forward = bond-ratio expectation.** If `I_S > 0` and `R_S` are `m_S`-measurable,
`I_T` and `I_T/I_S` are integrable and `𝔼^T[I_T | m_S] = I_S·R_S` a.e. (the martingale
property of `F(·,T)`), then `𝔼^T[I_T/I_S] = 𝔼^T[R_S]`. -/
theorem jyYoyForward_eq_bondRatio {mS : MeasurableSpace Ω} (hmS : mS ≤ m)
    [SigmaFinite (μ.trim hmS)] (IS IT RS : Ω → ℝ)
    (hIS : StronglyMeasurable[mS] IS) (hISpos : ∀ ω, 0 < IS ω)
    (hIT : Integrable IT μ) (hITS : Integrable (fun ω => IT ω / IS ω) μ)
    (hmart : μ[IT | mS] =ᵐ[μ] fun ω => IS ω * RS ω) :
    ∫ ω, IT ω / IS ω ∂μ = ∫ ω, RS ω ∂μ := by
  have hinv : StronglyMeasurable[mS] fun ω => (IS ω)⁻¹ := hIS.measurable.inv.stronglyMeasurable
  have hprod : Integrable (fun ω => (IS ω)⁻¹ * IT ω) μ := by
    simpa [div_eq_inv_mul] using hITS
  have hpull : μ[fun ω => (IS ω)⁻¹ * IT ω | mS]
      =ᵐ[μ] fun ω => (IS ω)⁻¹ * (μ[IT | mS]) ω :=
    condExp_mul_of_stronglyMeasurable_left hinv hprod hIT
  have h1 : ∫ ω, IT ω / IS ω ∂μ = ∫ ω, (μ[fun ω => (IS ω)⁻¹ * IT ω | mS]) ω ∂μ := by
    rw [integral_condExp hmS]
    simp [div_eq_inv_mul]
  rw [h1, integral_congr_ae hpull]
  refine integral_congr_ae ?_
  filter_upwards [hmart] with ω hω
  simp only [hω]
  field_simp [(hISpos ω).ne']

/-- **YoY forward in the printed convexity shape (Bagaria ch. 17 eq. 17.10; Brigo–Mercurio
ch. 15).** Under the hypotheses of `jyYoyForward_eq_bondRatio`, and with the bond ratio in
Hull–White reconstitution form (`hR`: `R_S` is the naive ratio of forwards
`Pʳ(0,T)·Pⁿ(0,S)/(Pʳ(0,S)·Pⁿ(0,T))` times `exp(Dʳ − Dⁿ + Bⁿyⁿ − Bʳyʳ)` with the two
Gaussian rate deviations of `yoyConvexity_eq`),

  `𝔼^T[I_T/I_S] = (Pʳ(0,T)·Pⁿ(0,S)/(Pʳ(0,S)·Pⁿ(0,T)))·exp(Bⁿmⁿ − Bʳmʳ + Bⁿ²Vⁿ − BʳBⁿ·Cov)`,

i.e. the naive ratio times the convexity factor. The means, variances, covariance, `hR`
and `hmart` are hypotheses; they are not derived from the SDEs here. -/
theorem jyYoyForward_eq_convexity {mS : MeasurableSpace Ω} (hmS : mS ≤ m)
    [SigmaFinite (μ.trim hmS)] (IS IT RS : Ω → ℝ)
    (hIS : StronglyMeasurable[mS] IS) (hISpos : ∀ ω, 0 < IS ω)
    (hIT : Integrable IT μ) (hITS : Integrable (fun ω => IT ω / IS ω) μ)
    (hmart : μ[IT | mS] =ᵐ[μ] fun ω => IS ω * RS ω)
    (mn mr Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hindep : IndepFun Z1 Z2 μ)
    (hR : ∀ ω, RS ω = (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (Convexity.hwD Br Vr
        - Convexity.hwD Bn Vn + (Bn * (mn + Real.sqrt Vn * Z1 ω)
          - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))))) :
    ∫ ω, IT ω / IS ω ∂μ
      = (Pr0T * Pn0S / (Pr0S * Pn0T))
        * Real.exp (Bn * mn - Br * mr + Bn ^ 2 * Vn - Br * Bn * Cov) := by
  rw [jyYoyForward_eq_bondRatio hmS IS IT RS hIS hISpos hIT hITS hmart]
  simp_rw [hR]
  exact @Convexity.yoyConvexity_eq Ω m μ mn mr Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov hVn hVr hρ
    hCov Z1 Z2 hZ1 hZ2 hindep

end Yoy

section YoyPrice

/-- **Time-0 price of a year-on-year payment.** Under the nominal `T`-forward measure
`Q^T = forwardMeasure Qn BT` and the hypotheses of `jyYoyForward_eq_convexity`, with
`Pⁿ(0,T) = 𝔼^{Qn}[1/B_T] > 0`, the time-0 value of the payment `I_T/I_S` at `T` is

  `𝔼^{Qn}[(I_T/I_S)/B_T] = Pⁿ(0,T)·(naive ratio of forwards)·exp(Bⁿmⁿ − Bʳmʳ + Bⁿ²Vⁿ − BʳBⁿ·Cov)`.

It is `MathFin.forwardMeasure_price` composed with `jyYoyForward_eq_convexity`; the
hypotheses of the latter are not derived. -/
theorem jyYoyPayment_price {Ω : Type*} {mS m : MeasurableSpace Ω} {Qn : Measure Ω} (BT : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (Pn0T' : ℝ)
    (hP : Pn0T' = ∫ ω, 1 / BT ω ∂Qn) (hPpos : 0 < Pn0T')
    (hmS : mS ≤ m)
    [SigmaFinite ((MathFin.forwardMeasure Qn BT).trim hmS)] (IS IT RS : Ω → ℝ)
    (hIS : StronglyMeasurable[mS] IS) (hISpos : ∀ ω, 0 < IS ω)
    (hIT : Integrable IT (MathFin.forwardMeasure Qn BT))
    (hITS : Integrable (fun ω => IT ω / IS ω) (MathFin.forwardMeasure Qn BT))
    (hmart : (MathFin.forwardMeasure Qn BT)[IT | mS]
      =ᵐ[MathFin.forwardMeasure Qn BT] fun ω => IS ω * RS ω)
    (mn mr Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) (MathFin.forwardMeasure Qn BT))
    (hZ2 : HasLaw Z2 (gaussianReal 0 1) (MathFin.forwardMeasure Qn BT))
    (hindep : IndepFun Z1 Z2 (MathFin.forwardMeasure Qn BT))
    (hR : ∀ ω, RS ω = (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (Convexity.hwD Br Vr
        - Convexity.hwD Bn Vn + (Bn * (mn + Real.sqrt Vn * Z1 ω)
          - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))))) :
    ∫ ω, IT ω / IS ω / BT ω ∂Qn
      = Pn0T' * ((Pr0T * Pn0S / (Pr0S * Pn0T))
        * Real.exp (Bn * mn - Br * mr + Bn ^ 2 * Vn - Br * Bn * Cov)) := by
  have hprice := MathFin.forwardMeasure_price (Q := Qn) (fun ω => IT ω / IS ω) hBTmeas hBTpos
    (hP ▸ hPpos)
  rw [← hP] at hprice
  rw [← hprice]
  congr 1
  exact jyYoyForward_eq_convexity hmS IS IT RS hIS hISpos hIT hITS hmart mn mr Vn Vr ρ Bn Br
    Pn0T Pn0S Pr0T Pr0S Cov hVn hVr hρ hCov hZ1 hZ2 hindep hR

end YoyPrice

end MathFin.Inflation.JarrowYildirim
