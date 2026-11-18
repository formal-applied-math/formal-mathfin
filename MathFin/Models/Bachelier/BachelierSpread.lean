/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Probability.Gaussian.GaussianPairLinearLaw
public import MathFin.Probability.Gaussian.GaussianPartialMoments
public import MathFin.Probability.Gaussian.GaussianMoments

/-!
# Bachelier spread options: the difference reduction

A spread option pays `max(F₁ − F₂ − K, 0)` — the right to deliver asset 2 plus the cash
amount `K` and receive asset 1. In the Bachelier (normal) model each forward is an
arithmetic Brownian motion `Fᵢ = fᵢ + σᵢ · Zᵢ`, so pricing reduces to the law of the
*difference* of two Gaussians. This file establishes the two halves of that reduction
and their composition:

* the **difference reduction** (`hasLaw_sub_gaussianPair`): the spread
  `(f₁ + σ₁·U) − (f₂ + σ₂·V)` of a jointly Gaussian standard pair `(U, V)` with
  `cov(U, V) = ρ` is Gaussian with mean `f₁ − f₂` and the **effective variance**
  `σ₁² + σ₂² − 2ρσ₁σ₂` — the same combination as the Margrabe effective volatility of
  the log-spread, carried by the spread itself rather than its logarithm. The
  independent case appears in law form as `hasLaw_sub_indepGaussian`.
* the **stop-loss transform of a general Gaussian law** (`gaussian_call_formula`,
  `gaussian_put_formula`): `E[(W − K)⁺] = (m − K)·Φ(d) + √v·ϕ(d)` with
  `d = (m − K)/√v`, for any `W ~ N(m, v)` with `v ≠ 0` and any strike sign — the
  model-free form of `bachelier_call_formula`, proved by the same standard-normal
  reduction (standardize `W`, then `integral_max_sub_mul_gaussianPDFReal`).

Composing the two (`bachelier_spread_call`, `bachelier_spread_put`), the spread option
collapses to a single-name Bachelier formula at the effective standard deviation
`√(σ₁² + σ₂² − 2ρσ₁σ₂)`: a two-asset normal-model problem that is exactly a one-asset
one. This is the normal-model analogue of the reduction
`MathFin/Models/BlackScholes/ExchangeOption.lean` performs for lognormal marginals.

## Main definitions

* `bachelierSpreadVariance`: the effective variance `σ₁² + σ₂² − 2ρσ₁σ₂` of the spread
  `F₁ − F₂`.
* `bachelierSpreadD`: the dimensionless distance of the spread mean to the strike,
  `(f₁ − f₂ − K) / √(σ₁² + σ₂² − 2ρσ₁σ₂)`.
* `BachelierSpreadHyp`: the Bachelier spread hypothesis: `0 < σ₁`, `0 < σ₂`,
  `ρ² < 1` and `(U, V)` a jointly Gaussian standard pair with covariance `ρ`.

## Main results

* `bachelierSpreadVariance_pos`: the effective variance is positive when the second
  volatility is nonzero and the correlation is sub-unit.
* `hasLaw_sub_gaussianPair`: the difference reduction, `(f₁ + σ₁·U) − (f₂ + σ₂·V) ~
  N(f₁ − f₂, σ₁² + σ₂² − 2ρσ₁σ₂)`.
* `hasLaw_sub_indepGaussian`: the difference of two independent Gaussians is Gaussian
  with mean `μ₁ − μ₂` and variance `v₁ + v₂`.
* `gaussian_call_formula` / `gaussian_put_formula`: the stop-loss transform of an
  arbitrary Gaussian law, `E[(W − K)⁺] = (m − K)·Φ(d) + √v·ϕ(d)` and its put mirror.
* `bachelier_spread_call`: under `BachelierSpreadHyp`, the expected spread-call payoff
  equals `(f₁ − f₂ − K)·Φ(d) + √(σ₁² + σ₂² − 2ρσ₁σ₂)·ϕ(d)` with `d = bachelierSpreadD`.
* `bachelier_spread_put`: the put mirror, priced at the same effective standard
  deviation.

## References

* [L. Bachelier, *Théorie de la spéculation*][Bachelier1900]
* [W. Margrabe, *The value of an option to exchange one asset for another*][Margrabe1978]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006]

## Tags

Bachelier model, spread option, exchange option, normal model, difference of Gaussians,
effective variance, stop-loss transform, MSC 91G20, MSC 60E05, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal

/-! ### The effective variance of a Bachelier spread -/

/-- **Effective variance of a Bachelier spread**: the variance of the difference
`σ₁·U − σ₂·V` of a correlated standard Gaussian pair, `σ₁² + σ₂² − 2ρσ₁σ₂`. This is the
same combination as the Margrabe effective volatility of the log-spread
(`margrabe_effective_variance`), carried by the spread itself rather than its
logarithm. -/
def bachelierSpreadVariance (σ₁ σ₂ ρ : ℝ) : ℝ :=
  σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂

/-- The effective variance of a Bachelier spread is positive when the second volatility
is nonzero and the correlation is sub-unit, since
`σ₁² + σ₂² − 2ρσ₁σ₂ = (σ₁ − ρσ₂)² + (1 − ρ²)σ₂² > 0`; no condition on `σ₁` is needed.
Under `BachelierSpreadHyp` both volatilities are positive. -/
theorem bachelierSpreadVariance_pos (σ₁ σ₂ ρ : ℝ)
    (h₂ : 0 < σ₂) (hρ : ρ ^ 2 < 1) :
    0 < bachelierSpreadVariance σ₁ σ₂ ρ := by
  have hring : bachelierSpreadVariance σ₁ σ₂ ρ
      = (σ₁ - ρ * σ₂) ^ 2 + (1 - ρ ^ 2) * σ₂ ^ 2 := by
    unfold bachelierSpreadVariance; ring
  have hlt : 0 < (1 - ρ ^ 2) * σ₂ ^ 2 := mul_pos (by linarith) (by positivity)
  have hnn : 0 ≤ (σ₁ - ρ * σ₂) ^ 2 := sq_nonneg _
  rw [hring]; linarith

/-- Bachelier spread `d`: the dimensionless distance of the spread mean `f₁ − f₂` to
the strike, normalized by the effective standard deviation. -/
noncomputable def bachelierSpreadD (f₁ f₂ K σ₁ σ₂ ρ : ℝ) : ℝ :=
  (f₁ - f₂ - K) / Real.sqrt (bachelierSpreadVariance σ₁ σ₂ ρ)

/-! ### The difference reduction -/

/-- **The difference reduction (correlated Gaussian pair)**: if `(U, V)` is a jointly
Gaussian pair of standard normals with `cov(U, V) = ρ`, then the spread of the shifted,
scaled forwards `(f₁ + σ₁·U) − (f₂ + σ₂·V)` is Gaussian with mean `f₁ − f₂` and the
effective variance `σ₁² + σ₂² − 2ρσ₁σ₂` — the linear law `hasLaw_linear_gaussianPair`
at coefficients `σ₁, −σ₂`, recentred by `f₁ − f₂`. -/
theorem hasLaw_sub_gaussianPair {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {U V : Ω → ℝ} {ρ : ℝ}
    (hUV : HasGaussianLaw (fun ω ↦ (U ω, V ω)) P)
    (hU : HasLaw U (gaussianReal 0 1) P) (hV : HasLaw V (gaussianReal 0 1) P)
    (hcov : cov[U, V; P] = ρ) (f₁ f₂ σ₁ σ₂ : ℝ) :
    HasLaw (fun ω ↦ (f₁ + σ₁ * U ω) - (f₂ + σ₂ * V ω))
      (gaussianReal (f₁ - f₂) (bachelierSpreadVariance σ₁ σ₂ ρ).toNNReal) P := by
  have hlin := hasLaw_linear_gaussianPair hUV hU hV hcov σ₁ (-σ₂)
  have hvar : (σ₁ ^ 2 + 2 * σ₁ * (-σ₂) * ρ + (-σ₂) ^ 2).toNNReal
      = (bachelierSpreadVariance σ₁ σ₂ ρ).toNNReal :=
    congrArg Real.toNNReal (by unfold bachelierSpreadVariance; ring)
  rw [hvar] at hlin
  have hfun : (fun ω ↦ (f₁ + σ₁ * U ω) - (f₂ + σ₂ * V ω))
      = fun ω ↦ σ₁ * U ω + -σ₂ * V ω + (f₁ - f₂) := by
    funext ω; ring
  rw [hfun]
  simpa only [zero_add] using gaussianReal_add_const hlin (f₁ - f₂)

/-- **The difference of independent Gaussians is Gaussian**: if `X ~ N(μ₁, v₁)` and
`Y ~ N(μ₂, v₂)` are independent, then `X − Y ~ N(μ₁ − μ₂, v₁ + v₂)` — the spread of two
independent normal forwards is itself normal, with the variances adding. This is the
`ρ = 0` instance of the difference reduction, stated for arbitrary Gaussian laws through
the convolution `gaussianReal_conv_gaussianReal`. -/
theorem hasLaw_sub_indepGaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : Ω → ℝ} {μ₁ μ₂ : ℝ} {v₁ v₂ : ℝ≥0}
    (hX : HasLaw X (gaussianReal μ₁ v₁) P) (hY : HasLaw Y (gaussianReal μ₂ v₂) P)
    (h : IndepFun X Y P) :
    HasLaw (fun ω ↦ X ω - Y ω) (gaussianReal (μ₁ - μ₂) (v₁ + v₂)) P := by
  have hY' : HasLaw (-Y) (gaussianReal (-μ₂) v₂) P := gaussianReal_neg hY
  have h' : IndepFun X (-Y) P := h.neg_right
  have hsum := h'.hasLaw_add hX hY'
  rw [gaussianReal_conv_gaussianReal] at hsum
  exact hsum

/-! ### The stop-loss transform of a Gaussian law -/

/-- **Call payoff under a Gaussian law**: if `W ~ N(m, v)` with `v ≠ 0`, then for any
strike `K` (of either sign),

    E[(W − K)⁺] = (m − K)·Φ(d) + √v·ϕ(d),   d = (m − K)/√v.

This is the model-free form of `bachelier_call_formula` (which transcribes it for the
Bachelier terminal price with a positive strike): standardize `W` to
`Z = (W − m)/√v ~ N(0, 1)` (`hasLaw_sub_div_of_gaussianReal`), where the payoff is
`√v·(Z + d)⁺`, and read the integral off the standard-normal stop-loss transform
`integral_max_sub_mul_gaussianPDFReal` at `−d`. -/
theorem gaussian_call_formula {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {W : Ω → ℝ} {m : ℝ} {v : ℝ≥0}
    (hW : HasLaw W (gaussianReal m v) P) (hv : v ≠ 0) (K : ℝ) :
    ∫ ω, max (W ω - K) 0 ∂P
      = (m - K) * Phi ((m - K) / Real.sqrt (v : ℝ))
        + Real.sqrt (v : ℝ) * gaussianPDFReal 0 1 ((m - K) / Real.sqrt (v : ℝ)) := by
  have hvpos : 0 < (v : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg v) (by exact_mod_cast hv.symm)
  set s : ℝ := Real.sqrt (v : ℝ) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hvpos
  set d : ℝ := (m - K) / s with hd_def
  have hsd : s * d = m - K := by rw [hd_def]; field_simp
  have hZ : HasLaw (fun ω ↦ (W ω - m) / s) (gaussianReal 0 1) P :=
    hasLaw_sub_div_of_gaussianReal hW hs (by rw [hs_def]; exact (Real.sq_sqrt
      (NNReal.coe_nonneg v)).symm)
  have hWcomp : (fun ω ↦ max (W ω - K) 0)
      = (fun z ↦ max (m + s * z - K) 0) ∘ (fun ω ↦ (W ω - m) / s) := by
    funext ω
    have hWω : W ω - K = m + s * ((W ω - m) / s) - K := by
      field_simp
      ring
    rw [Function.comp_apply, hWω]
  have h_payoff_meas : Measurable fun z : ℝ ↦ max (m + s * z - K) 0 := by fun_prop
  -- The payoff is `s · (z + d)⁺`, so the integral is `s` times the stop-loss transform.
  have hpt (z : ℝ) : gaussianPDFReal 0 1 z • max (m + s * z - K) 0
      = s * (max (z - -d) 0 * gaussianPDFReal 0 1 z) := by
    have h : m + s * z - K = s * (z - -d) := by linear_combination -hsd
    have hmax := mul_max_of_nonneg (z - -d) 0 hs.le
    rw [mul_zero] at hmax
    rw [smul_eq_mul, h, ← hmax]; ring
  rw [hWcomp, hZ.integral_comp h_payoff_meas.aestronglyMeasurable,
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_max_sub_mul_gaussianPDFReal, gaussianPDFReal_zero_one_neg, Phi_neg]
  linear_combination Phi d * hsd

/-- **Put payoff under a Gaussian law**: if `W ~ N(m, v)` with `v ≠ 0`, then for any
strike `K`,

    E[(K − W)⁺] = (K − m)·Φ((K − m)/√v) + √v·ϕ((K − m)/√v),

the put mirror of `gaussian_call_formula`: `(K − W)⁺` is the call `(-W − (-K))⁺` on the
negated Gaussian `−W ~ N(−m, v)`, so the call formula applies verbatim (the normal-model
put-call parity `put = call − forward` in disguise). -/
theorem gaussian_put_formula {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {W : Ω → ℝ} {m : ℝ} {v : ℝ≥0}
    (hW : HasLaw W (gaussianReal m v) P) (hv : v ≠ 0) (K : ℝ) :
    ∫ ω, max (K - W ω) 0 ∂P
      = (K - m) * Phi ((K - m) / Real.sqrt (v : ℝ))
        + Real.sqrt (v : ℝ) * gaussianPDFReal 0 1 ((K - m) / Real.sqrt (v : ℝ)) := by
  have hcall := gaussian_call_formula (gaussianReal_neg hW) hv (-K)
  have hmean : (-m : ℝ) - -K = K - m := by ring
  rw [hmean] at hcall
  have hfun : (fun ω ↦ max (K - W ω) 0) = (fun ω ↦ max (-W ω - -K) 0) := by
    funext ω; congr 1; ring
  rw [hfun]
  exact hcall

/-! ### The Bachelier spread pricing identity -/

/-- Bachelier spread-option hypothesis: two forwards `F₁ = f₁ + σ₁·U` and
`F₂ = f₂ + σ₂·V` driven by a jointly Gaussian standard pair `(U, V)` with covariance
`ρ` — the two-name analogue of `BachelierHyp`, which drives one price by a single
standard normal. -/
structure BachelierSpreadHyp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f₁ f₂ σ₁ σ₂ ρ : ℝ) (U V : Ω → ℝ) : Prop where
  σ₁_pos : 0 < σ₁
  σ₂_pos : 0 < σ₂
  /-- The correlation is sub-unit, so the spread is non-degenerate. -/
  ρ_sq_lt_one : ρ ^ 2 < 1
  /-- The drivers are jointly Gaussian. -/
  joint_gaussian : HasGaussianLaw (fun ω ↦ (U ω, V ω)) Q
  U_law : HasLaw U (gaussianReal 0 1) Q
  V_law : HasLaw V (gaussianReal 0 1) Q
  /-- The driver covariance is the correlation `ρ`. -/
  cov_UV : cov[U, V; Q] = ρ

/-- **Bachelier spread call formula**: under `BachelierSpreadHyp`, the expected payoff
of the spread call `max(F₁ − F₂ − K, 0)` on the normal forwards `F₁ = f₁ + σ₁·U`,
`F₂ = f₂ + σ₂·V` collapses to the single-name Bachelier formula on the difference:

    E_Q[max(F₁ − F₂ − K, 0)] = (f₁ − f₂ − K)·Φ(d) + √(σ₁² + σ₂² − 2ρσ₁σ₂)·ϕ(d),

with `d = bachelierSpreadD f₁ f₂ K σ₁ σ₂ ρ` and the strike `K` of either sign: the
difference reduction `hasLaw_sub_gaussianPair` composed with the stop-loss transform
`gaussian_call_formula` at the effective variance. A two-name normal-model problem is
exactly a one-name one. -/
theorem bachelier_spread_call {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {f₁ f₂ K σ₁ σ₂ ρ : ℝ} {U V : Ω → ℝ}
    (h : BachelierSpreadHyp Q f₁ f₂ σ₁ σ₂ ρ U V) :
    ∫ ω, max ((f₁ + σ₁ * U ω) - (f₂ + σ₂ * V ω) - K) 0 ∂Q
      = (f₁ - f₂ - K) * Phi (bachelierSpreadD f₁ f₂ K σ₁ σ₂ ρ)
        + Real.sqrt (bachelierSpreadVariance σ₁ σ₂ ρ)
          * gaussianPDFReal 0 1 (bachelierSpreadD f₁ f₂ K σ₁ σ₂ ρ) := by
  obtain ⟨_, hσ₂, hρ, hUV, hU, hV, hcov⟩ := h
  have hpos := bachelierSpreadVariance_pos σ₁ σ₂ ρ hσ₂ hρ
  have hvnn : (bachelierSpreadVariance σ₁ σ₂ ρ).toNNReal ≠ 0 := fun hc ↦
    (not_le.2 hpos) (Real.toNNReal_eq_zero.1 hc)
  have hcoe : ((bachelierSpreadVariance σ₁ σ₂ ρ).toNNReal : ℝ)
      = bachelierSpreadVariance σ₁ σ₂ ρ := Real.coe_toNNReal _ hpos.le
  have hcall := gaussian_call_formula
    (hasLaw_sub_gaussianPair hUV hU hV hcov f₁ f₂ σ₁ σ₂) hvnn K
  rw [hcoe] at hcall
  exact hcall

/-- **Bachelier spread put formula**: under `BachelierSpreadHyp`, the expected payoff of
the spread put `max(K − (F₁ − F₂), 0)` is the mirror

    E_Q[max(K − (F₁ − F₂), 0)]
      = (K − (f₁ − f₂))·Φ((K − (f₁ − f₂))/√v) + √v·ϕ((K − (f₁ − f₂))/√v),

with `v = σ₁² + σ₂² − 2ρσ₁σ₂` — `gaussian_put_formula` applied to the reduced spread
law, at the same effective standard deviation as the call. -/
theorem bachelier_spread_put {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {f₁ f₂ K σ₁ σ₂ ρ : ℝ} {U V : Ω → ℝ}
    (h : BachelierSpreadHyp Q f₁ f₂ σ₁ σ₂ ρ U V) :
    ∫ ω, max (K - ((f₁ + σ₁ * U ω) - (f₂ + σ₂ * V ω))) 0 ∂Q
      = (K - (f₁ - f₂))
          * Phi ((K - (f₁ - f₂)) / Real.sqrt (bachelierSpreadVariance σ₁ σ₂ ρ))
        + Real.sqrt (bachelierSpreadVariance σ₁ σ₂ ρ)
          * gaussianPDFReal 0 1
              ((K - (f₁ - f₂)) / Real.sqrt (bachelierSpreadVariance σ₁ σ₂ ρ)) := by
  obtain ⟨_, hσ₂, hρ, hUV, hU, hV, hcov⟩ := h
  have hpos := bachelierSpreadVariance_pos σ₁ σ₂ ρ hσ₂ hρ
  have hvnn : (bachelierSpreadVariance σ₁ σ₂ ρ).toNNReal ≠ 0 := fun hc ↦
    (not_le.2 hpos) (Real.toNNReal_eq_zero.1 hc)
  have hcoe : ((bachelierSpreadVariance σ₁ σ₂ ρ).toNNReal : ℝ)
      = bachelierSpreadVariance σ₁ σ₂ ρ := Real.coe_toNNReal _ hpos.le
  have hput := gaussian_put_formula
    (hasLaw_sub_gaussianPair hUV hU hV hcov f₁ f₂ σ₁ σ₂) hvnn K
  rw [hcoe] at hput
  exact hput

end MathFin
