/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.Put
public import MathFin.Models.Rates.Caplet
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

* `quad2_nonneg`, `quad3_nonneg`: the `2×2` and `3×3` quadratic-form lemmas behind the
  non-negativity of the integrand.
* The variance integrand of `log F(·,T)` for constant parameters (`jyVarIntegrand`) and its
  integral `V(0,T)` (`jyVariance`). The integrand is the quadratic form of the vector
  `(σ_I, −σ_r·B_r, σ_n·B_n)` against the `(I, r, n)` correlation matrix
  (`jyVarIntegrand_eq_quadForm`), hence non-negative when that matrix is positive
  semidefinite (`jyVarIntegrand_nonneg`, and for `V(0,T)` with `T ≥ 0`, `jyVariance_nonneg`).
  Pairwise `|ρ| ≤ 1` is not enough for three factors;
  the condition used is `ρ_{rI}² ≤ 1`, `ρ_{nI}² ≤ 1` and the determinant form
  `jyCorrDet ≥ 0`. Degenerate reduction: `jyVariance_zero_rate_vols`.
* The zero-coupon inflation caplet and floorlet (`jyZcCaplet_price`, `jyZcFloorlet_price`):
  if the index under the nominal `T`-forward measure is lognormal
  with log-variance `V` and the index-linked bond is priced on the real curve, the priced caplet
  payoff `𝔼^{Qn}[(I_T − K)⁺/B_T]` is the library's Black caplet on the curve forward
  `I₀·Pʳ(0,T)/Pⁿ(0,T)` at total variance `V` (the caplet is the contract value of
  `MathFin.Contracts.value_caplet_black76`). `jyForwardIndex_lognormal_eq_curves` puts the
  lognormal index on that curve forward.
* `jyZcCaplet_price_deterministic_rates`: with `σ_r = σ_n = 0` the integrated variance is `σ_I²T`
  and the priced caplet is `blackCaplet (I₀Pʳ/Pⁿ) K σ_I T Pⁿ` (by `blackCaplet_sqrt_variance`: Black
  at total variance `σ²T` and maturity 1 is Black at volatility `σ` and maturity `T`).
* The year-on-year forward: `jyYoyForward_eq_bondRatio` is the tower-property step (Bagaria
  eq. 17.8) from the martingale property of `F(·,T)` under the `T`-forward measure to
  `𝔼^T[I_T/I_S] = 𝔼^T[Pʳ(S,T)/Pⁿ(S,T)]`; `jyYoyForward_eq_convexity` evaluates that expectation by
  `yoyConvexity_eq` as the naive ratio of forwards times the convexity factor; and
  `jyYoyPayment_price` is the time-0 value of the payment (`MathFin.forwardMeasure_price`).

## Scope

The SDE-level derivation of the `−ρ_{rI}σ_rσ_I` drift of the real rate and of `V` from the
three SDEs is not claimed: `V` is defined, and the lognormality of the index
(`hZ`: `Z ~ N(0,1)` under `Q^T` with `I_T = bsTerminal F₀ 0 √V 1 Z`), the
martingale property of the forward index (`hmart`) and the Hull–White bond-reconstitution form
of the bond ratio (`hR`) are hypotheses. The paper itself was not available to the author; the
model form follows the secondary sources below. The exact YoY caplet, calibration,
seasonality and Monte Carlo are out of scope. `Inflation.lean`'s remark that eq. (17.8) is not a
named lemma is superseded by `jyYoyForward_eq_bondRatio` below.

## References

* [R. Jarrow and Y. Yildirim, *Pricing Treasury Inflation Protected Securities and Related
  Derivatives using an HJM Model*, J. Financial and Quantitative Analysis 38(2) (2003),
  337–358][JarrowYildirim2003]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  2nd ed. (2006), §15.3 (the JY model), §16.3 (YYIIS with the JY model), §17.1 (the JY
  caplet; the zero-coupon caplet is its first-period case)
* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 17 §17.3, eq. 17.6 (the
  forward index) and §17.4 (eqs. 17.8, 17.10)

## Tags

Jarrow–Yildirim, inflation model, zero-coupon inflation cap, year-on-year inflation,
convexity adjustment, Hull–White, MSC 91G30, MSC 91G20, JEL E31
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin.Inflation.JarrowYildirim

/-! ### The variance integrand -/

/-- The Jarrow–Yildirim variance integrand at time `t` for the forward index `F(·,T)`, with
constant parameters: `a_r, a_n` mean reversions, `σ_I, σ_r, σ_n` volatilities, `ρ_{rI}, ρ_{nI},
ρ_{nr}` correlations. The Hull–White loadings are the library's `vasicekBondB` at the
remaining maturity `T − t`. Nonzero mean reversions `a_r, a_n ≠ 0` are implicit in this reading:
`vasicekBondB 0 τ = 0` by Lean's division convention, not the Ho–Lee limit `τ`.
The integrand is:

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
`[[1, ρ_{rI}, ρ_{nI}], [ρ_{rI}, 1, ρ_{nr}], [ρ_{nI}, ρ_{nr}, 1]]`. Positive
semidefiniteness of the matrix needs `ρ_{rI}² ≤ 1`, `ρ_{nI}² ≤ 1` and this determinant `≥ 0`
(the hypotheses of `quad3_nonneg`); the determinant alone does not suffice. -/
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
theorem quad3_nonneg {ρrI ρnI ρnr x y z : ℝ} (hrI : ρrI ^ 2 ≤ 1) (hnI : ρnI ^ 2 ≤ 1)
    (hdet : 0 ≤ jyCorrDet ρrI ρnI ρnr) :
    0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + 2 * ρrI * x * y + 2 * ρnI * x * z + 2 * ρnr * y * z := by
  have key := quad2_nonneg (A := 1 - ρrI ^ 2) (B := ρnr - ρrI * ρnI) (C := 1 - ρnI ^ 2)
    (y := y) (z := z)
    (by linarith) (by linarith) (by unfold jyCorrDet at hdet; nlinarith)
  nlinarith [sq_nonneg (x + ρrI * y + ρnI * z)]

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
`V(0,T) = σ_I²·T`; in particular `V(0,T) = 0` when `σ_I = 0` as well. -/
theorem jyVariance_zero_rate_vols (ar an σI ρrI ρnI ρnr T : ℝ) :
    jyVariance ar an σI 0 0 ρrI ρnI ρnr T = σI ^ 2 * T := by
  unfold jyVariance jyVarIntegrand
  simp only [mul_zero, zero_mul, zero_pow two_ne_zero, add_zero, sub_zero,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-! ### The zero-coupon inflation caplet and floorlet

`Qn` is the nominal pricing measure with money-market account `BT`, and `Q^T` its nominal
`T`-forward measure (`MathFin.forwardMeasure`). The hypotheses are: the index-linked bond is
priced on the real curve (`hident`, as in `ZCSwap.forwardIndex_eq`), and under `Q^T` the index
is lognormal, `I_T = bsTerminal F₀ 0 √V 1 Z` (`= F₀·exp(−V/2 + √V·Z)` for `V ≥ 0`) with
`Z ~ N(0,1)` — the log-variance `V` being
`jyVariance` when the SDE-level derivation is granted (not derived here). The caplet pays
`(I_T − K)⁺` at `T` and is priced with the nominal bond `Pⁿ(0,T)` as numéraire. -/

section Caplet

variable {Ω : Type*} [MeasurableSpace Ω] {Qn : Measure Ω}

/-- **The lognormal forward index sits on the curve forward.** If `I_T = bsTerminal F₀ 0 √V 1 Z`
(`= F₀·exp(−V/2 + √V·Z)` for `V ≥ 0`) with `Z ~ N(0,1)` under the nominal `T`-forward
measure, then the index-linked-bond
identification forces `F₀ = I₀·Pʳ(0,T)/Pⁿ(0,T)` (`ZCSwap.forwardIndex_eq`). Hypotheses: `hBTpos`
(`B_T > 0`), `hBTmeas` (`B_T` measurable), `hPn0T` (`0 < Pⁿ(0,T)`), `hP`
(`Pⁿ(0,T) = 𝔼^{Qn}[1/B_T]`), `hident` (`𝔼^{Qn}[I_T/B_T] = I₀·Pʳ(0,T)`) and `hZ`. It needs no
`IsProbabilityMeasure Qn`. -/
theorem jyForwardIndex_lognormal_eq_curves (BT : Ω → ℝ) (Pn0T Pr0T I0 F0 V : ℝ) (Z : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hP : Pn0T = ∫ ω, 1 / BT ω ∂Qn)
    (hident : ∫ ω, bsTerminal F0 0 (Real.sqrt V) 1 (Z ω) / BT ω ∂Qn = I0 * Pr0T)
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

/-- **ZC inflation caplet: the priced payoff is the Black caplet on the curve forward.** The
zero-coupon inflation caplet is the contract `caplet () 0 0 1 K` in
`MathFin.Contracts.value_caplet_black76`, instantiated with the time-constant deflator
`fun _ => 1/B_T` and the time-constant observed index `fun _ _ => I_T` (the contract's time
indices are dummies); `Pⁿ(0,T)` plays the role of `zeroCurve Qn D 0`. The forward is pinned to the
curve by `jyForwardIndex_lognormal_eq_curves`. Under `hident` and a
lognormal index under `Q^T` with log-variance `V`, and `F₀ > 0`, `V > 0`, `K > 0`,

  `𝔼^{Qn}[(I_T − K)⁺/B_T] = blackCaplet (I₀Pʳ(0,T)/Pⁿ(0,T)) K √V 1 Pⁿ(0,T)`,

i.e. `Pⁿ·[F Φ(d₁) − K Φ(d₂)]` with `d_i = bsd_i F K 0 √V 1`. Further hypotheses: `Qn` is a
probability measure (inherited from the section variable of `value_caplet_black76`; the
floorlet, proved directly, does not need it), `B_T > 0` is measurable and
`Pⁿ(0,T) = 𝔼^{Qn}[1/B_T] > 0`; that `Q^T` is a probability measure follows from `hZ`. The index
law is a hypothesis; that its log-variance is `jyVariance` is the SDE-level content, not
proved. -/
theorem jyZcCaplet_price [IsProbabilityMeasure Qn] (BT : Ω → ℝ)
    (Pn0T Pr0T I0 F0 V K : ℝ) (Z : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hP : Pn0T = ∫ ω, 1 / BT ω ∂Qn)
    (hident : ∫ ω, bsTerminal F0 0 (Real.sqrt V) 1 (Z ω) / BT ω ∂Qn = I0 * Pr0T)
    (hZ : HasLaw Z (gaussianReal 0 1) (MathFin.forwardMeasure Qn BT))
    (hF0 : 0 < F0) (hV : 0 < V) (hK : 0 < K) :
    ∫ ω, max (bsTerminal F0 0 (Real.sqrt V) 1 (Z ω) - K) 0 / BT ω ∂Qn
      = blackCaplet (I0 * Pr0T / Pn0T) K (Real.sqrt V) 1 Pn0T := by
  have hF := jyForwardIndex_lognormal_eq_curves BT Pn0T Pr0T I0 F0 V Z hBTpos hBTmeas hPn0T hP
    hident hZ
  have hQ' : IsProbabilityMeasure (MathFin.forwardMeasure Qn BT) :=
    hZ.isProbabilityMeasure_iff.2 inferInstance
  have hint : Integrable (fun ω => 1 / BT ω) Qn :=
    Integrable.of_integral_ne_zero (by rw [← hP]; exact hPn0T.ne')
  have hyp : BSCallHyp (MathFin.forwardMeasure Qn BT) F0 K 0 (Real.sqrt V) 1 Z :=
    ⟨hF0, hK, Real.sqrt_pos.2 hV, one_pos, hZ⟩
  have hfm : (MathFin.forwardMeasure Qn BT)
      = MathFin.forwardMeasure Qn fun ω => 1 / (fun (_ : ℝ≥0) ω => 1 / BT ω) 0 ω := by
    congr 1
    funext ω
    simp
  have key := Contracts.value_caplet_black76 (Q := Qn)
    (D := fun (_ : ℝ≥0) ω => 1 / BT ω) (X := fun (_ : Unit) (_ : ℝ≥0) ω =>
      bsTerminal F0 0 (Real.sqrt V) 1 (Z ω)) (ℓ := ()) (T₀ := 0) (T₁ := 0) (δ := 1)
    (hQ' := hfm) (fun ω => by simpa using hBTpos ω) (measurable_const.div hBTmeas) hint hyp
    (Filter.Eventually.of_forall fun _ => rfl)
  have hz : Contracts.zeroCurve Qn (fun (_ : ℝ≥0) ω => 1 / BT ω) 0 = Pn0T := by
    simp [Contracts.zeroCurve, hP]
  simp only [Contracts.caplet, Contracts.Contract.value_pay, Contracts.capletPayoff,
    Contracts.Payoff.eval, Contracts.scenarioAt, hz] at key
  rw [← hF]
  have key' : ∫ ω, max (bsTerminal F0 0 (Real.sqrt V) 1 (Z ω) - K) 0 / BT ω ∂Qn
      = Pn0T * blackCaplet F0 K (Real.sqrt V) 1 1 := by
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [div_eq_inv_mul]
  rw [key']
  simp only [blackCaplet, one_mul]

/-- **ZC inflation floorlet: the priced payoff is the Black floorlet on the curve forward.** The
put counterpart of `jyZcCaplet_price` under its hypotheses except `IsProbabilityMeasure Qn` (the
floorlet is proved directly and does not need it), by `forwardMeasure_price` and
`bs_put_formula`. -/
theorem jyZcFloorlet_price (BT : Ω → ℝ)
    (Pn0T Pr0T I0 F0 V K : ℝ) (Z : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hP : Pn0T = ∫ ω, 1 / BT ω ∂Qn)
    (hident : ∫ ω, bsTerminal F0 0 (Real.sqrt V) 1 (Z ω) / BT ω ∂Qn = I0 * Pr0T)
    (hZ : HasLaw Z (gaussianReal 0 1) (MathFin.forwardMeasure Qn BT))
    (hF0 : 0 < F0) (hV : 0 < V) (hK : 0 < K) :
    ∫ ω, max (K - bsTerminal F0 0 (Real.sqrt V) 1 (Z ω)) 0 / BT ω ∂Qn
      = blackFloorlet (I0 * Pr0T / Pn0T) K (Real.sqrt V) 1 Pn0T := by
  have hF := jyForwardIndex_lognormal_eq_curves BT Pn0T Pr0T I0 F0 V Z hBTpos hBTmeas hPn0T hP
    hident hZ
  have hQ' : IsProbabilityMeasure (MathFin.forwardMeasure Qn BT) :=
    hZ.isProbabilityMeasure_iff.2 inferInstance
  have hyp : BSCallHyp (MathFin.forwardMeasure Qn BT) F0 K 0 (Real.sqrt V) 1 Z :=
    ⟨hF0, hK, Real.sqrt_pos.2 hV, one_pos, hZ⟩
  have hprice := MathFin.forwardMeasure_price (Q := Qn)
    (fun ω => max (K - bsTerminal F0 0 (Real.sqrt V) 1 (Z ω)) 0) hBTmeas hBTpos (hP ▸ hPn0T)
  rw [← hP] at hprice
  rw [← hprice]
  have h := bs_put_formula hyp
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at h
  rw [h, ← hF]
  unfold blackFloorlet
  ring

/-- **Black caplet at total variance.** At maturity `1`, the Black caplet at total variance `σ²T`
is the Black caplet at volatility `σ` and maturity `T` (`σ ≥ 0`, `T ≥ 0`): `√(σ²T) = σ√T`, and
`bsd₁`, `bsd₂` depend on `(σ, T)` only through `σ√T` and `σ²T`. A general Black-76 fact (`σ` and
`T` enter only through `σ√T`); it is stated here to keep this module self-contained, its natural
home is next to `blackCaplet` in `Models/Forwards/Black76.lean`, and the same step appears inline
in `bsV_eq_totalVarianceCall`. -/
theorem blackCaplet_sqrt_variance (F K σ T α : ℝ) (hσ : 0 ≤ σ) (hT : 0 ≤ T) :
    blackCaplet F K (Real.sqrt (σ ^ 2 * T)) 1 α = blackCaplet F K σ T α := by
  have hs : Real.sqrt (σ ^ 2 * T) = σ * Real.sqrt T := by
    rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ]
  have hsq : (σ * Real.sqrt T) ^ 2 = σ ^ 2 * T := by
    rw [mul_pow, Real.sq_sqrt hT]
  have hd1 : bsd1 F K 0 (Real.sqrt (σ ^ 2 * T)) 1 = bsd1 F K 0 σ T := by
    rw [hs]
    unfold bsd1
    rw [Real.sqrt_one, mul_one, hsq]
    ring_nf
  have hd2 : bsd2 F K 0 (Real.sqrt (σ ^ 2 * T)) 1 = bsd2 F K 0 σ T := by
    unfold bsd2
    rw [hd1, hs, Real.sqrt_one, mul_one]
  unfold blackCaplet
  rw [hd1, hd2]

/-- **Deterministic rates reduce the zero-coupon inflation caplet to Black at the index
volatility.** With `σ_r = σ_n = 0`, `σ_I > 0` and `T > 0`, the integrated variance is
`jyVariance … = σ_I²T` (`jyVariance_zero_rate_vols`), and the priced caplet of
`jyZcCaplet_price` at `V := jyVariance …` is `blackCaplet (I₀Pʳ/Pⁿ) K σ_I T Pⁿ`: Black on the
curve forward at the index volatility and maturity `T`. Hypotheses: all those of
`jyZcCaplet_price`, including `[IsProbabilityMeasure Qn]`, except `hV`, which follows from
`σ_I > 0` and `T > 0`; `hident` and `hZ` are stated at
`V := jyVariance ar an σI 0 0 ρrI ρnI ρnr T`. None is derived from the SDEs. -/
theorem jyZcCaplet_price_deterministic_rates [IsProbabilityMeasure Qn] (BT : Ω → ℝ)
    (ar an σI ρrI ρnI ρnr T : ℝ) (Pn0T Pr0T I0 F0 K : ℝ) (Z : Ω → ℝ)
    (hσI : 0 < σI) (hT : 0 < T)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hP : Pn0T = ∫ ω, 1 / BT ω ∂Qn)
    (hident : ∫ ω, bsTerminal F0 0
      (Real.sqrt (jyVariance ar an σI 0 0 ρrI ρnI ρnr T)) 1 (Z ω) / BT ω ∂Qn = I0 * Pr0T)
    (hZ : HasLaw Z (gaussianReal 0 1) (MathFin.forwardMeasure Qn BT))
    (hF0 : 0 < F0) (hK : 0 < K) :
    ∫ ω, max (bsTerminal F0 0
        (Real.sqrt (jyVariance ar an σI 0 0 ρrI ρnI ρnr T)) 1 (Z ω) - K) 0 / BT ω ∂Qn
      = blackCaplet (I0 * Pr0T / Pn0T) K σI T Pn0T := by
  have hV : 0 < jyVariance ar an σI 0 0 ρrI ρnI ρnr T := by
    rw [jyVariance_zero_rate_vols]
    positivity
  rw [jyZcCaplet_price BT Pn0T Pr0T I0 F0 _ K Z hBTpos hBTmeas hPn0T hP hident hZ hF0 hV hK,
    jyVariance_zero_rate_vols, blackCaplet_sqrt_variance _ _ _ _ _ hσI.le hT.le]

end Caplet

/-! ### The year-on-year forward

`μ` is the nominal `T`-forward measure and `m_S ≤ m` the information at `S`. The forward index
`F(S,T) = I_S·Pʳ(S,T)/Pⁿ(S,T)` is a `μ`-martingale (`hmart`: `𝔼^T[I_T | m_S] = I_S·R_S` with
`R_S = Pʳ(S,T)/Pⁿ(S,T)`, using `F(T,T) = I_T`). This is the modelling hypothesis, disclosed
as such; the tower property does the rest. -/

section Yoy

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- **YoY forward = bond-ratio expectation** (Bagaria ch. 17 §17.4, eq. 17.8).
Hypotheses: `hmS : m_S ≤ m` with `μ.trim hmS`
σ-finite; `I_S` is `m_S`-measurable and positive; `I_T` and `I_T/I_S` are `μ`-integrable; and
`𝔼^T[I_T | m_S] = I_S·R_S` a.e. (`hmart`, the martingale property of `F(·,T)`). Then
`𝔼^T[I_T/I_S] = 𝔼^T[R_S]`. -/
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

/-- **YoY forward in the printed convexity shape (Bagaria ch. 17 §17.4, eq. 17.10;
Brigo–Mercurio §16.3).** Under the hypotheses of `jyYoyForward_eq_bondRatio`, and with the
bond ratio in Hull–White reconstitution form (`hR`: `R_S` is the naive ratio of forwards
`Pʳ(0,T)·Pⁿ(0,S)/(Pʳ(0,S)·Pⁿ(0,T))` times `exp(Dʳ − Dⁿ − Bʳyʳ + Bⁿyⁿ)` with the two
Gaussian rate deviations of `yoyConvexity_eq`),

  `𝔼^T[I_T/I_S] = (Pʳ(0,T)·Pⁿ(0,S)/(Pʳ(0,S)·Pⁿ(0,T)))·exp(−Bʳmʳ + Bⁿmⁿ + Bⁿ²Vⁿ − BʳBⁿ·Cov)`,

i.e. the naive ratio times the convexity factor. The exponent is the same quantity as in
`yoyConvexity_eq`, with its terms in Bagaria's printed order (equal by `ring`). Further hypotheses:
`Z1, Z2` independent standard normals under `μ` (`hZ1`, `hZ2`, `hindep`), `0 ≤ Vⁿ`, `0 ≤ Vʳ`,
`ρ² ≤ 1` and
`hCov : Cov = ρ·√(Vⁿ·Vʳ)`. The means, variances, covariance, `hR` and `hmart` are hypotheses;
they are not derived from the SDEs here. -/
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
        - Convexity.hwD Bn Vn
        - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))
        + Bn * (mn + Real.sqrt Vn * Z1 ω))) :
    ∫ ω, IT ω / IS ω ∂μ
      = (Pr0T * Pn0S / (Pr0S * Pn0T))
        * Real.exp (-(Br * mr) + Bn * mn + Bn ^ 2 * Vn - Br * Bn * Cov) := by
  have hR' : ∀ ω, RS ω = (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (Convexity.hwD Br Vr
        - Convexity.hwD Bn Vn + (Bn * (mn + Real.sqrt Vn * Z1 ω)
          - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω)))) := fun ω => by
    rw [hR ω]
    congr 2
    ring
  rw [jyYoyForward_eq_bondRatio hmS IS IT RS hIS hISpos hIT hITS hmart]
  simp_rw [hR']
  rw [@Convexity.yoyConvexity_eq Ω m μ mn mr Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov hVn hVr hρ
    hCov Z1 Z2 hZ1 hZ2 hindep]
  congr 2
  ring

end Yoy

/-- **Time-0 price of a year-on-year payment.** Under the nominal `T`-forward measure
`Q^T = forwardMeasure Qn BT` and the hypotheses of `jyYoyForward_eq_convexity` (all stated under
`Q^T`), with `B_T > 0` measurable (`hBTpos`, `hBTmeas`) and
`Pⁿ(0,T) = 𝔼^{Qn}[1/B_T] > 0` (`hP`, `hPn0T`; the single variable `Pn0T`, also the one in the
naive ratio), the time-0 value of the payment `I_T/I_S` at `T` is

  `𝔼^{Qn}[(I_T/I_S)/B_T] = Pⁿ(0,T)·(naive ratio of forwards)·exp(−Bʳmʳ + Bⁿmⁿ + Bⁿ²Vⁿ − BʳBⁿ·Cov)`.

It is `MathFin.forwardMeasure_price` composed with `jyYoyForward_eq_convexity`; the
hypotheses of the latter are not derived. -/
theorem jyYoyPayment_price {Ω : Type*} {mS m : MeasurableSpace Ω} {Qn : Measure Ω} (BT : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (Pn0T : ℝ)
    (hPn0T : 0 < Pn0T) (hP : Pn0T = ∫ ω, 1 / BT ω ∂Qn)
    (hmS : mS ≤ m)
    [SigmaFinite ((MathFin.forwardMeasure Qn BT).trim hmS)] (IS IT RS : Ω → ℝ)
    (hIS : StronglyMeasurable[mS] IS) (hISpos : ∀ ω, 0 < IS ω)
    (hIT : Integrable IT (MathFin.forwardMeasure Qn BT))
    (hITS : Integrable (fun ω => IT ω / IS ω) (MathFin.forwardMeasure Qn BT))
    (hmart : (MathFin.forwardMeasure Qn BT)[IT | mS]
      =ᵐ[MathFin.forwardMeasure Qn BT] fun ω => IS ω * RS ω)
    (mn mr Vn Vr ρ Bn Br Pn0S Pr0T Pr0S Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) (MathFin.forwardMeasure Qn BT))
    (hZ2 : HasLaw Z2 (gaussianReal 0 1) (MathFin.forwardMeasure Qn BT))
    (hindep : IndepFun Z1 Z2 (MathFin.forwardMeasure Qn BT))
    (hR : ∀ ω, RS ω = (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (Convexity.hwD Br Vr
        - Convexity.hwD Bn Vn
        - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))
        + Bn * (mn + Real.sqrt Vn * Z1 ω))) :
    ∫ ω, IT ω / IS ω / BT ω ∂Qn
      = Pn0T * ((Pr0T * Pn0S / (Pr0S * Pn0T))
        * Real.exp (-(Br * mr) + Bn * mn + Bn ^ 2 * Vn - Br * Bn * Cov)) := by
  have hprice := MathFin.forwardMeasure_price (Q := Qn) (fun ω => IT ω / IS ω) hBTmeas hBTpos
    (hP ▸ hPn0T)
  rw [← hP] at hprice
  rw [← hprice]
  congr 1
  exact jyYoyForward_eq_convexity hmS IS IT RS hIS hISpos hIT hITS hmart mn mr Vn Vr ρ Bn Br
    Pn0T Pn0S Pr0T Pr0S Cov hVn hVr hρ hCov hZ1 hZ2 hindep hR

end MathFin.Inflation.JarrowYildirim
