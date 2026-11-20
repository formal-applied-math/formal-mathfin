/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.Rates.Caplet
public import MathFin.Models.Rates.Inflation
public import MathFin.Models.Rates.VasicekBondPrice

/-!
# Jarrow–Yildirim: the ZC inflation caplet and the YoY forward

Notation. Time `t` runs on `[0,T]`, where `T` is the payment date (the caplet maturity, or for the
year-on-year payment (the index ratio over `[S,T]`) the end of `[S,T]`, with start `S < T`). The
nominal and real short rates are Gaussian (Hull–White) and the price index `I_t` is a geometric
Brownian motion, with values `I₀`, `I_S`, `I_T` at times `0`, `S`, `T`. `σ_I, σ_r, σ_n` are the
volatilities of the index and of the real and nominal short rates, `a_r, a_n` their mean reversions,
`ρ_{rI}, ρ_{nI}, ρ_{nr}` the correlations of the driving Brownian motions (real rate–index, nominal
rate–index, nominal–real rate), and `B_x(t,T) = (1 − e^{−a_x(T−t)})/a_x` (`x ∈ {r, n}`) the
Hull–White loadings (not to be confused with the money-market account `B_T`). `Qn` is the nominal
pricing measure with money-market account `B_T` and expectation `𝔼^{Qn}`; `Q^T` and `𝔼^T` are the
nominal `T`-forward measure and its expectation. `Pⁿ(t,T)` and `Pʳ(t,T)` are the nominal and real
zero-coupon bond prices, `F(t,T) = I_t·Pʳ(t,T)/Pⁿ(t,T)` is the forward index (a `Q^T`-martingale in
`t`) and `F = F(0,T)` its time-0 value, the curve forward. `jyVariance` is the integrated
log-variance `V(0,T)` of `F(·,T)` (defined below); `V` is a log-variance (a free input of the caplet
statement), `F₀` the `Q^T`-mean of the lognormal index law `I_T = F₀·exp(−V/2 + √V·Z)`, `Z ~ N(0,1)`
under `Q^T`, `K` a caplet strike, `Φ` the standard normal distribution function and
`d_{1,2} = (log(F/K) ± V/2)/√V`. These symbols (`t`, `T`, `S`, `I_t`, `I₀`, `I_S`, `I_T`, `σ_·`,
`a_·`, `ρ_{··}`, `B_x(t,T)`, `Qn`, `B_T`, `𝔼^{Qn}`, `Q^T`, `𝔼^T`, `Pⁿ(t,T)`, `Pʳ(t,T)`, `F(t,T)`,
`F`, `V`, `V(0,T)`, `F₀`, `Z`, `K`, `Φ`, `d_{1,2}`) keep these meanings in every docstring below,
except in the general lemmas `quad2_nonneg`, `quad3_nonneg` and `blackCaplet_sqrt_variance`, whose
letters are free arguments; hypothesis names (`hident`, `hZ`, `hmart`, `hR`) and local symbols (`μ`,
`m`, `m_S`, `R_S`, `yⁱ`, `Dⁱ`, ...) are introduced where first used. This module records what
follows without the SDE calculus.

## Main definitions

* `jyVarIntegrand`: the variance integrand of `log F(·,T)` with constant parameters.
* `jyVariance`: its integral `V(0,T)`.
* `jyCorrDet`: the determinant of the `(I, r, n)` correlation matrix.

## Main results

* `quad2_nonneg`, `quad3_nonneg`: the `2×2` and `3×3` quadratic-form lemmas behind the next item.
* `jyVarIntegrand_nonneg`, `jyVariance_nonneg` (for `T ≥ 0`): the integrand is the quadratic form of
  `(σ_I, −σ_r·B_r, σ_n·B_n)` against the `(I, r, n)` correlation matrix, non-negative when
  `ρ_{rI}² ≤ 1`, `ρ_{nI}² ≤ 1` and `jyCorrDet ≥ 0` (pairwise `|ρ| ≤ 1` is not enough for three
  factors). `jyVariance_zero_rate_vols`: `V(0,T) = σ_I²T` when `σ_r = σ_n = 0`.
* `jyZcCaplet_price`: if the index-linked bond is priced on the real curve and the index is
  lognormal under `Q^T`, the priced caplet payoff `𝔼^{Qn}[(I_T − K)⁺/B_T]` is `Pⁿ(0,T)` times the
  Black caplet on the curve forward `F` at total variance `V` (by
  `MathFin.Contracts.value_caplet_black76`; the strike convention is in `jyZcCaplet_price`'s
  docstring).
  `jyForwardIndex_lognormal_eq_curves` puts the lognormal index on `F`.
  `jyZcCaplet_price_deterministic_rates`: for `σ_r = σ_n = 0` it is `Pⁿ(0,T)` times the Black caplet
  at volatility `σ_I` and maturity `T` (by `blackCaplet_sqrt_variance`).
* The year-on-year forward: `jyYoyForward_eq_bondRatio` is the tower step (Bagaria ch. 17 §17.4, eq.
  17.8) from the martingale property of `F(·,T)` to `𝔼^T[I_T/I_S] = 𝔼^T[Pʳ(S,T)/Pⁿ(S,T)]`;
  `jyYoyForward_eq_convexity` evaluates it by `yoyConvexity_eq` as the naive ratio of forwards times
  the convexity factor; `jyYoyPayment_price` is the time-0 value of the payment
  (`MathFin.forwardMeasure_price`).

## Scope

The SDE-level derivation of the `−ρ_{rI}σ_rσ_I` drift of the real rate and of the log-variance
`V(0,T)` is not claimed: the index-linked-bond pricing (`hident`), the lognormality of the index
(`hZ`), the martingale property of the forward index (`hmart`) and the Hull–White reconstitution
form of the bond ratio (`hR`) are hypotheses. The three-SDE form (Hull–White nominal and real short
rates, lognormal index, dependent Brownian motions) and the real-rate drift shift `−ρ_{rI}σ_rσ_I`
are those of Dam–Macrina–Skovmand–Sloth, §2.2 of the arXiv version 1801.08804 (who cite
Brigo–Mercurio ch. 15 for the form), and of Bagaria §17.4 (Calculation 17.7, eq. 17.9, with
correlations `ρ_{nr}`, `ρ_{rI}`); the nominal-rate–index correlation `ρ_{nI}` is named in neither,
and the correlation structure of the variance integrand is this module's reading. This module uses
only eqs. 17.6, 17.8 and 17.10 of Bagaria ch. 17, and the caplet rests on Brigo–Mercurio §17.1.
Jarrow–Yildirim (2003) itself was not consulted. The exact YoY caplet, calibration, seasonality and
Monte Carlo are out of scope.

## References

* [R. Jarrow and Y. Yildirim, *Pricing Treasury Inflation Protected Securities and Related
  Derivatives using an HJM Model*, J. Financial and Quantitative Analysis 38(2) (2003),
  337–358][JarrowYildirim2003]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006], 2nd
  ed. (2006), §15.3 (the JY model), §16.3 (YYIIS with the JY model), §17.1 (the JY caplet; the
  zero-coupon caplet is its first-period case)
* [H. Dam, A. Macrina, D. Skovmand and D. Sloth, *Rational Models for Inflation-Linked Derivatives*,
  SIAM J. Financial Mathematics 11(4) (2020), 974–1006][DamMacrinaSkovmandSloth2020], §2.2 of the
  arXiv version 1801.08804
* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 17 §17.3, eq. 17.6 (the
  forward index), and §17.4, eqs. 17.8, 17.10

## Tags

Jarrow–Yildirim, inflation model, zero-coupon inflation cap, year-on-year inflation, convexity
adjustment, Hull–White, MSC 91G30, MSC 91G20, JEL E31
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin.Inflation.JarrowYildirim

/-! ### The variance integrand -/

/-- The Jarrow–Yildirim variance integrand at time `t` for the forward index `F(·,T)`, with constant
parameters: `a_r, a_n` mean reversions, `σ_I, σ_r, σ_n` volatilities, `ρ_{rI}, ρ_{nI}, ρ_{nr}`
correlations. The Hull–White loadings are `B_x = vasicekBondB a_x (T − t)`, `x ∈ {r, n}` (the
library's function at the remaining maturity `T − t`). Nonzero mean reversions `a_r, a_n ≠ 0` are
implicit in this reading: `vasicekBondB 0 τ = 0` by Lean's division convention, not the Ho–Lee limit
`τ`. The integrand is:

  `σ_I² + σ_r²B_r² + σ_n²B_n² − 2ρ_{rI}σ_Iσ_rB_r + 2ρ_{nI}σ_Iσ_nB_n − 2ρ_{nr}σ_nσ_rB_nB_r`. -/
noncomputable def jyVarIntegrand (ar an σI σr σn ρrI ρnI ρnr T t : ℝ) : ℝ :=
  σI ^ 2 + σr ^ 2 * vasicekBondB ar (T - t) ^ 2 + σn ^ 2 * vasicekBondB an (T - t) ^ 2
    - 2 * ρrI * σI * σr * vasicekBondB ar (T - t)
    + 2 * ρnI * σI * σn * vasicekBondB an (T - t)
    - 2 * ρnr * σn * σr * vasicekBondB an (T - t) * vasicekBondB ar (T - t)

/-- The integrated variance `V(0,T) = ∫₀ᵀ jyVarIntegrand dt`. Junk value: where `a_r = 0` or
`a_n = 0` the loading `vasicekBondB 0 τ` is `0` by Lean's division convention, not the Ho–Lee limit
`τ`, so `V(0,T)` has its meaning only for nonzero mean reversions (or zero rate volatilities, as in
`jyVariance_zero_rate_vols`). `V(0,T)` is a variance only for `T ≥ 0` (for `T < 0` the integral is
oriented backwards and the value is not a variance); `jyVariance_nonneg` assumes `0 ≤ T`. -/
noncomputable def jyVariance (ar an σI σr σn ρrI ρnI ρnr T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, jyVarIntegrand ar an σI σr σn ρrI ρnI ρnr T t

/-- The determinant of the `(I, r, n)` correlation matrix
`[[1, ρ_{rI}, ρ_{nI}], [ρ_{rI}, 1, ρ_{nr}], [ρ_{nI}, ρ_{nr}, 1]]`. Positive semidefiniteness of the
matrix needs `ρ_{rI}² ≤ 1`, `ρ_{nI}² ≤ 1` and this determinant `≥ 0` (the hypotheses of
`quad3_nonneg`); the determinant alone does not suffice. -/
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

/-- **Three-factor quadratic form.** For correlations with `ρ_{rI}² ≤ 1`, `ρ_{nI}² ≤ 1` and
`jyCorrDet ≥ 0`, `x² + y² + z² + 2ρ_{rI}xy + 2ρ_{nI}xz + 2ρ_{nr}yz ≥ 0`. -/
theorem quad3_nonneg {ρrI ρnI ρnr x y z : ℝ} (hrI : ρrI ^ 2 ≤ 1) (hnI : ρnI ^ 2 ≤ 1)
    (hdet : 0 ≤ jyCorrDet ρrI ρnI ρnr) :
    0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + 2 * ρrI * x * y + 2 * ρnI * x * z + 2 * ρnr * y * z := by
  have key := quad2_nonneg (A := 1 - ρrI ^ 2) (B := ρnr - ρrI * ρnI) (C := 1 - ρnI ^ 2)
    (y := y) (z := z)
    (by linarith) (by linarith) (by unfold jyCorrDet at hdet; nlinarith)
  nlinarith [sq_nonneg (x + ρrI * y + ρnI * z)]

/-- The integrand is the quadratic form of `(σ_I, −σ_r·B_r, σ_n·B_n)` against the `(I, r, n)`
correlation matrix: the variance of `σ_I dW_I − σ_rB_r dW_r + σ_nB_n dW_n`. -/
private theorem jyVarIntegrand_eq_quadForm (ar an σI σr σn ρrI ρnI ρnr T t : ℝ) :
    jyVarIntegrand ar an σI σr σn ρrI ρnI ρnr T t
      = σI ^ 2 + (-(σr * vasicekBondB ar (T - t))) ^ 2 + (σn * vasicekBondB an (T - t)) ^ 2
        + 2 * ρrI * σI * (-(σr * vasicekBondB ar (T - t)))
        + 2 * ρnI * σI * (σn * vasicekBondB an (T - t))
        + 2 * ρnr * (-(σr * vasicekBondB ar (T - t))) * (σn * vasicekBondB an (T - t)) := by
  unfold jyVarIntegrand
  ring

/-- **The variance integrand is non-negative** under the correlation PSD condition (`ρ_{rI}² ≤ 1`,
`ρ_{nI}² ≤ 1`, `jyCorrDet ≥ 0`), for every `t`. -/
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

/-! ### The zero-coupon inflation caplet

`BT` is the money-market account `B_T`. The hypotheses are `hZ` (under `Q^T`,
`I_T = bsTerminal F₀ 0 √V 1 Z` with `Z ~ N(0,1)`, which is `F₀·exp(−V/2 + √V·Z)` for `V ≥ 0`) and
`hident` (the index-linked bond is priced on the real curve, `𝔼^{Qn}[I_T/B_T] = I₀·Pʳ(0,T)`, the
time-0 case of the forward-index martingale, Bagaria ch. 17 §17.3, eq. 17.6). The caplet pays
`(I_T − K)⁺` at `T` and is priced with the nominal bond `Pⁿ(0,T)` as numéraire. -/

section Caplet

variable {Ω : Type*} [MeasurableSpace Ω] {Qn : Measure Ω}

/-- **The lognormal index sits on the curve forward.** Under `hZ` (`I_T = bsTerminal F₀ 0 √V 1 Z`,
`Z ~ N(0,1)` under `Q^T`), `hident` (`𝔼^{Qn}[I_T/B_T] = I₀·Pʳ(0,T)`) and
`0 < Pⁿ(0,T) = 𝔼^{Qn}[1/B_T]` (`hPn0T`, `hP`) with `B_T` positive and measurable (`hBTpos`,
`hBTmeas`), `F₀ = I₀·Pʳ(0,T)/Pⁿ(0,T)` (`ZCSwap.forwardIndex_eq`). No `IsProbabilityMeasure Qn` is
needed. Junk corner: for `V < 0` Lean's `√V = 0`, so the hypotheses describe the constant index
`F₀`; the pricing theorems assume `V > 0`. -/
theorem jyForwardIndex_lognormal_eq_curves (BT : Ω → ℝ) (Pn0T Pr0T I0 F0 V : ℝ) (Z : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hP : Pn0T = ∫ ω, 1 / BT ω ∂Qn)
    (hident : ∫ ω, bsTerminal F0 0 (Real.sqrt V) 1 (Z ω) / BT ω ∂Qn = I0 * Pr0T)
    (hZ : HasLaw Z (gaussianReal 0 1) (MathFin.forwardMeasure Qn BT)) :
    F0 = I0 * Pr0T / Pn0T := by
  have h := ZCSwap.forwardIndex_eq (Qn := Qn) BT Pn0T Pr0T I0
    (fun ω => bsTerminal F0 0 (Real.sqrt V) 1 (Z ω)) hBTpos hBTmeas hPn0T hP hident
  have h2 := integral_discounted_bsTerminal hZ F0 0 (Real.sqrt V) (T := 1) zero_le_one
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at h2
  rw [← h]
  exact h2.symm

/-- **ZC inflation caplet: the priced payoff is `Pⁿ(0,T)` times the Black caplet on the curve
forward.** For `F₀ > 0` (the `Q^T`-mean of the lognormal index law), `V > 0`, `K > 0`, under `hZ`
(`I_T = bsTerminal F₀ 0 √V 1 Z` with `Z ~ N(0,1)` under `Q^T`), `hident`
(`𝔼^{Qn}[I_T/B_T] = I₀·Pʳ(0,T)`) and `0 < Pⁿ(0,T) = 𝔼^{Qn}[1/B_T]` with `B_T` positive and
measurable, and `Qn` a probability measure (inherited from the section variable of
`value_caplet_black76`): `𝔼^{Qn}[(I_T − K)⁺/B_T] = Pⁿ(0,T)·blackCaplet F K √V 1 1` with
`F = I₀·Pʳ(0,T)/Pⁿ(0,T)` the curve forward, i.e. `Pⁿ(0,T)·[F Φ(d₁) − K Φ(d₂)]` with
`d₁ = bsd1 F K 0 √V 1`, `d₂ = bsd2 F K 0 √V 1`. That `Q^T` is a probability measure follows from
`hZ`. The caplet is the contract `caplet () 0 0 1 K` of `MathFin.Contracts.value_caplet_black76`
with deflator `D = fun _ => 1/B_T` and observed index `fun _ _ => I_T`; both are time-constant, so
the contract's reset and payment dates `0, 0` are placeholders and the payment date `T` enters only
through `B_T`, hence `zeroCurve Qn D 0 = Pⁿ(0,T)`; `jyForwardIndex_lognormal_eq_curves` gives
`F₀ = F`. Strike convention: the market payoff `N[(I_T/I₀ − 1) − κ]⁺` (notional `N`, `κ` the total,
non-annualised strike over `[0,T]`) is `(N/I₀)·(I_T − K)⁺` with `K = I₀(1+κ)`; an annual quoted
strike `k` is `K = I₀(1+k)^T`. `V` is a free input here; the statement does not identify it with
`jyVariance`. -/
theorem jyZcCaplet_price [IsProbabilityMeasure Qn] (BT : Ω → ℝ)
    (Pn0T Pr0T I0 F0 V K : ℝ) (Z : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hP : Pn0T = ∫ ω, 1 / BT ω ∂Qn)
    (hident : ∫ ω, bsTerminal F0 0 (Real.sqrt V) 1 (Z ω) / BT ω ∂Qn = I0 * Pr0T)
    (hZ : HasLaw Z (gaussianReal 0 1) (MathFin.forwardMeasure Qn BT))
    (hF0 : 0 < F0) (hV : 0 < V) (hK : 0 < K) :
    ∫ ω, max (bsTerminal F0 0 (Real.sqrt V) 1 (Z ω) - K) 0 / BT ω ∂Qn
      = Pn0T * blackCaplet (I0 * Pr0T / Pn0T) K (Real.sqrt V) 1 1 := by
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

/-- **Black caplet at total variance.** (Here `F, K, σ, T, α` are free arguments of `blackCaplet`.)
At maturity `1`, the Black caplet at total variance `σ²T` is the Black caplet at volatility `σ` and
maturity `T` (`σ > 0`, `T > 0`): `√(σ²T) = σ√T`, and `bsd1`, `bsd2` depend on `(σ, T)` only through
`σ√T` and `σ²T`. A general Black-76 fact (`σ` and `T` enter only through `σ√T`); it is stated here
to keep this module self-contained, its natural home is next to `blackCaplet` in
`Models/Forwards/Black76.lean`, and the same step appears inline in `bsV_eq_totalVarianceCall`. This
is an identity of the total function `blackCaplet`: it has a financial meaning only for `F, K > 0`
(`log(F/K)` is junk otherwise). `σ > 0` excludes `σ ≤ 0` (for `σ < 0`, `√(σ²T) = |σ|√T ≠ σ√T`; at
`σ = 0` both sides are junk `x/0`), and `T > 0` excludes the corner `T = 0`, where both sides are
junk `x/0` rather than the intrinsic value. -/
theorem blackCaplet_sqrt_variance (F K σ T α : ℝ) (hσ : 0 < σ) (hT : 0 < T) :
    blackCaplet F K (Real.sqrt (σ ^ 2 * T)) 1 α = blackCaplet F K σ T α := by
  have hs : Real.sqrt (σ ^ 2 * T) = σ * Real.sqrt T := by
    rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le]
  have hsq : (σ * Real.sqrt T) ^ 2 = σ ^ 2 * T := by
    rw [mul_pow, Real.sq_sqrt hT.le]
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

/-- **Deterministic rates reduce the caplet to `Pⁿ(0,T)` times the Black caplet at the index
volatility.** With `σ_r = σ_n = 0`, `σ_I > 0` and `T > 0`, `jyVariance … = σ_I²T`
(`jyVariance_zero_rate_vols`) and `jyZcCaplet_price` at `V := jyVariance …` gives
`Pⁿ(0,T)·blackCaplet F K σ_I T 1`. Hypotheses: those of `jyZcCaplet_price` (including
`[IsProbabilityMeasure Qn]`) except `hV` (`0 < V`), which follows from `σ_I > 0` and `T > 0`;
`hident` is stated at `V := jyVariance ar an σI 0 0 ρrI ρnI ρnr T`. -/
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
      = Pn0T * blackCaplet (I0 * Pr0T / Pn0T) K σI T 1 := by
  have hV : 0 < jyVariance ar an σI 0 0 ρrI ρnI ρnr T := by
    rw [jyVariance_zero_rate_vols]
    positivity
  rw [jyZcCaplet_price BT Pn0T Pr0T I0 F0 _ K Z hBTpos hBTmeas hPn0T hP hident hZ hF0 hV hK,
    jyVariance_zero_rate_vols, blackCaplet_sqrt_variance _ _ _ _ _ hσI hT]

end Caplet

/-! ### The year-on-year forward

`μ` is the nominal `T`-forward measure `Q^T`, `m` the full σ-algebra on `Ω` and `m_S ≤ m` the
information at time `S`. The forward index is a `μ`-martingale (`hmart`: `𝔼^T[I_T | m_S] = I_S·R_S`
with `R_S = Pʳ(S,T)/Pⁿ(S,T)`, using `F(T,T) = I_T`); this is the modelling hypothesis, and the tower
property does the rest. -/

section Yoy

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- **YoY forward = bond-ratio expectation** (Bagaria ch. 17 §17.4, eq. 17.8). Let `μ = Q^T`,
`m_S ≤ m` the information at `S` (`hmS`, with `μ.trim hmS` σ-finite), `R_S = Pʳ(S,T)/Pⁿ(S,T)`, and
assume `hmart` (`𝔼^T[I_T | m_S] = I_S·R_S`, the martingale property of `F(·,T)`), that `I_S` is
`m_S`-measurable and positive, and that `I_T` and `I_T/I_S` are `μ`-integrable. Then
`𝔼^T[I_T/I_S] = 𝔼^T[R_S]`. The proof pulls the factor `1/I_S` through the conditional expectation
(`condExp_mul_of_stronglyMeasurable_left`, `integral_condExp`); the same pull-out is
`MathFin.integral_mul_condExp` (`Pricing/FTAP/OneAssetDMW.lean`), not imported here to keep this
module's import closure free of the FTAP chain. -/
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
  have h1 : ∫ ω, IT ω / IS ω ∂μ = ∫ ω, (IS ω)⁻¹ * (μ[IT | mS]) ω ∂μ := by
    have := (integral_condExp hmS (f := fun ω => (IS ω)⁻¹ * IT ω)).symm.trans
      (integral_congr_ae hpull)
    simpa [div_eq_inv_mul] using this
  rw [h1]
  refine integral_congr_ae ?_
  filter_upwards [hmart] with ω hω
  simp only [hω]
  field_simp [(hISpos ω).ne']

/-- **YoY forward in the printed convexity shape (Bagaria ch. 17 §17.4, eq. 17.10; Brigo–Mercurio
§16.3).** Let `μ = Q^T`, and `Z1, Z2` independent standard normals under `μ` (`hZ1`, `hZ2`,
`hindep`), `ρ` a correlation of the two rate deviations at `S` (a free parameter of the statement;
it equals `ρ_{nr}` when `a_n = a_r` and in general differs from it), and `yⁿ = mⁿ + √Vⁿ·Z1`,
`yʳ = mʳ + √Vʳ·(ρ·Z1 + √(1−ρ²)·Z2)` the two Gaussian rate deviations of `yoyConvexity_eq` (the
deviation of each short rate at `S` from its time-0 forward rate `fⁱ(0,S)`, as in
`integral_exp_hwD_forwardMeasure`), with means `mⁱ` and variances `Vⁱ` (`0 ≤ Vⁿ`, `0 ≤ Vʳ`,
`ρ² ≤ 1`) and covariance `Cov = ρ·√(Vⁿ·Vʳ)` (`hCov`). `Bⁿ = B_n(S,T)` and `Bʳ = B_r(S,T)` are the
Hull–White loadings over `[S,T]` (free reals here; they enter only through `hR`), and
`Dⁱ = hwD Bⁱ Vⁱ = −Bⁱ²Vⁱ/2`. Under the hypotheses of `jyYoyForward_eq_bondRatio` (including
`hmart`), and assuming the bond ratio `R_S = Pʳ(S,T)/Pⁿ(S,T)` has the Hull–White reconstitution form
`hR` (`R_S` is the naive ratio of forwards `Pʳ(0,T)·Pⁿ(0,S)/(Pʳ(0,S)·Pⁿ(0,T))` times
`exp(Dʳ − Dⁿ − Bʳyʳ + Bⁿyⁿ)`),

  `𝔼^T[I_T/I_S] = (Pʳ(0,T)·Pⁿ(0,S)/(Pʳ(0,S)·Pⁿ(0,T)))·exp(−Bʳmʳ + Bⁿmⁿ + Bⁿ²Vⁿ − BʳBⁿ·Cov)`,

the naive ratio times the convexity factor, the exponent being that of `yoyConvexity_eq` with its
terms in Bagaria's printed order (equal by `ring`). The means, variances, covariance, `Bⁿ`, `Bʳ`,
`hR` and `hmart` are hypotheses or inputs, not derived from the SDEs here. Junk corner: the naive
ratio is `0` by Lean's division convention if `Pʳ(0,S)` or `Pⁿ(0,T)` is `0`; the bond prices are
positive in the model, and the statement is an identity about `hR`, so it carries no such guard. -/
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

/-- **Time-0 price of a year-on-year payment.** Under `Q^T = forwardMeasure Qn BT`, the hypotheses
of `jyYoyForward_eq_convexity` (all stated under `Q^T`, with its symbols `mⁱ, Vⁱ, Bⁱ, Cov`), `B_T`
positive and measurable (`hBTpos`, `hBTmeas`) and `0 < Pⁿ(0,T) = 𝔼^{Qn}[1/B_T]` (`hPn0T`, `hP`; the
single variable `Pn0T`, also the one in the naive ratio), the time-0 value of the payment `I_T/I_S`
at `T` is

  `𝔼^{Qn}[(I_T/I_S)/B_T] = Pⁿ(0,T)·(naive ratio of forwards)·exp(−Bʳmʳ + Bⁿmⁿ + Bⁿ²Vⁿ − BʳBⁿ·Cov)`.

It is `MathFin.forwardMeasure_price` composed with `jyYoyForward_eq_convexity`; the junk corner is
that of the latter (`Pʳ(0,S) = 0`). -/
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
