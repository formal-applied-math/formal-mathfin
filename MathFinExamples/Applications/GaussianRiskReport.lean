/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Using the library: a risk report for a Gaussian portfolio

A worked use of the library from outside it, the way a risk desk reports on a book of two
positions. Each position's loss over the horizon is Gaussian, with a given mean and volatility, and
the two are correlated. This file

1. records the book as data (means, volatilities, a correlation in `(−1, 1)`), with where the
   numbers come from and what the report leaves out;
2. reports, for a single Gaussian loss, its value-at-risk and expected shortfall in closed form at
   `z = Φ⁻¹(α)`, and its expected shortfall as the mean of the loss over its `α`-tail, a tail of
   mass exactly `1 − α` (`gaussian_loss_report`);
3. reads off the law of the combined loss from the joint Gaussian law of the book
   (`IsRealization.hasLaw_add`), so the same report applies to the whole book;
4. proves the diversification benefit for every such book: the combined VaR at every level
   `α ∈ [1/2, 1)` is at most the sum of the standalone ones, from the Gaussian closed forms
   (`IsRealization.valueAtRisk_add_le`); the combined ES is, at every level, because ES is
   subadditive for any integrable losses (`IsRealization.expectedShortfall_add_le`);
5. computes the report for an illustrative book, whose combined volatility is `8` against
   standalone volatilities of `5` and `5`.

`sample_checked` is the single statement the build certifies. It holds for every jointly Gaussian
pair of losses with the sample's means, volatilities and correlation, on any probability space.

## What the library supplies

* `MathFin.valueAtRisk_of_hasLaw_gaussianReal`, `expectedShortfall_of_hasLaw_gaussianReal`: VaR and
  ES of a Gaussian loss are the closed forms `gaussianVaR` and `gaussianCVaR` at `Φ⁻¹(α)`.
* `MathFin.measureReal_valueAtRisk_lt`, `expectedShortfall_eq_setIntegral_tail`: without atoms the
  tail `{L > VaR_α(L)}` has mass `1 − α`, and ES is the mean of `L` over it, the Acerbi–Tasche
  formula `expectedShortfall_eq_acerbiTasche` with its correction term gone.
* `MathFin.hasLaw_portfolio_gaussianReal`: a linear combination of a Gaussian vector is Gaussian,
  with the Markowitz variance.
* `MathFin.gaussianVaR_subadditive`: the closed form of VaR is subadditive in the volatility.
* `MathFin.expectedShortfall_add_le`: ES is subadditive, for any integrable losses.

## What it does not

The report is for one horizon, and the losses are exactly Gaussian with known parameters:
estimating the means, volatilities and correlation, fat tails, and the nonlinearity of option
positions are outside the model. No realization of the book is constructed here: the check is
quantified over every jointly Gaussian pair with the book's moments. The level `α` stays
symbolic: the report is in terms of `z = Φ⁻¹(α)` and `ϕ(z)`, and no numerical value of `Φ⁻¹` is
proved here.

## Source

The shape of the file follows the capped-call example
(`MathFinExamples/Applications/CappedCall.lean`). The numbers below are illustrative.
-/

namespace MathFin.Examples.GaussianRiskReport

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The report for one loss -/

/-- **The risk report for one Gaussian loss** `L ~ N(m, s²)` with `s > 0`, at a level `α ∈ (0, 1)`:
- `VaR_α(L) = m + s z` and `ES_α(L) = m + s ϕ(z)/(1 − α)`, at `z = Φ⁻¹(α)`;
- the tail `{L > VaR_α(L)}` has mass `1 − α`;
- `ES_α(L)` is the integral of `L` over that tail divided by `1 − α`. -/
theorem gaussian_loss_report {L : Ω → ℝ} {m s α : ℝ}
    (hL : HasLaw L (gaussianReal m (s ^ 2).toNNReal) P) (hs : 0 < s) (hα : α ∈ Ioo 0 1) :
    valueAtRisk L P α = gaussianVaR m s (PhiInv α) ∧
      expectedShortfall L P α = gaussianCVaR m s (PhiInv α) α ∧
      P.real {ω | valueAtRisk L P α < L ω} = 1 - α ∧
      expectedShortfall L P α = (1 - α)⁻¹ * ∫ ω in {ω | valueAtRisk L P α < L ω}, L ω ∂P := by
  have hv : (s ^ 2).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (by positivity)).ne'
  have hσ : √((s ^ 2).toNNReal : ℝ) = s := by
    rw [Real.coe_toNNReal _ (sq_nonneg s), Real.sqrt_sq hs.le]
  have := nullSingletonClass_gaussianReal (μ := m) hv
  have hF : Continuous (cdf (P.map L)) := hL.map_eq ▸ continuous_cdf
  refine ⟨?_, ?_, measureReal_valueAtRisk_lt hL.aemeasurable hF hα,
    expectedShortfall_eq_setIntegral_tail (integrable_of_hasLaw_gaussianReal hL) hF hα⟩
  · rw [valueAtRisk_of_hasLaw_gaussianReal hL hα, hσ]
  · rw [expectedShortfall_of_hasLaw_gaussianReal hv hL hα, hσ]

/-! ### The book, as data -/

/-- A book of two positions, by the mean and the volatility of each position's loss over the
horizon and the correlation of the two losses, with where the numbers come from and what the
report leaves out. -/
structure Book where
  /-- The mean loss of each position. -/
  mean : Fin 2 → ℝ
  /-- The volatility of each position's loss. -/
  vol : Fin 2 → ℝ
  /-- The correlation of the two losses. -/
  corr : ℝ
  vol_pos : ∀ i, 0 < vol i
  corr_mem : corr ∈ Ioo (-1) 1
  /-- Where the numbers come from. -/
  sources : List String
  /-- What the report does not model. -/
  unmodelled : List String

namespace Book

/-- The volatility of the combined loss, `√(σ₁² + 2ρσ₁σ₂ + σ₂²)`. -/
noncomputable def jointVol (b : Book) : ℝ :=
  √(b.vol 0 ^ 2 + 2 * b.corr * b.vol 0 * b.vol 1 + b.vol 1 ^ 2)

/-- The combined variance is `(σ₁ − σ₂)² + 2(1 + ρ)σ₁σ₂`, positive since `ρ > −1`. -/
lemma jointVar_pos (b : Book) :
    0 < b.vol 0 ^ 2 + 2 * b.corr * b.vol 0 * b.vol 1 + b.vol 1 ^ 2 := by
  nlinarith [sq_nonneg (b.vol 0 - b.vol 1),
    mul_pos (sub_pos.2 b.corr_mem.1) (mul_pos (b.vol_pos 0) (b.vol_pos 1))]

lemma jointVol_pos (b : Book) : 0 < b.jointVol :=
  Real.sqrt_pos.2 b.jointVar_pos

/-- **A realization of the book**: losses `X 0`, `X 1` that are jointly Gaussian with the book's
means, volatilities and correlation. -/
structure IsRealization (b : Book) (P : Measure Ω) (X : Fin 2 → Ω → ℝ) : Prop where
  gaussian : HasGaussianLaw (fun ω ↦ (X · ω)) P
  mean (i : Fin 2) : P[X i] = b.mean i
  var (i : Fin 2) : Var[X i; P] = b.vol i ^ 2
  cov : cov[X 0, X 1; P] = b.corr * b.vol 0 * b.vol 1

variable {b : Book} {X : Fin 2 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- Each position's loss is `N(mean, vol²)`. -/
lemma IsRealization.hasLaw (h : b.IsRealization P X) (i : Fin 2) :
    HasLaw (X i) (gaussianReal (b.mean i) (b.vol i ^ 2).toNNReal) P :=
  ⟨(h.gaussian.eval i).aemeasurable, by
    rw [(h.gaussian.eval i).map_eq_gaussianReal, h.mean, h.var]⟩

omit [IsProbabilityMeasure P] in
/-- **The combined loss is `N(μ₁ + μ₂, σ₁² + 2ρσ₁σ₂ + σ₂²)`**, the portfolio of the Gaussian vector
with unit weights (`hasLaw_portfolio_gaussianReal`). -/
lemma IsRealization.hasLaw_add (h : b.IsRealization P X) :
    HasLaw (fun ω ↦ X 0 ω + X 1 ω) (gaussianReal (b.mean 0 + b.mean 1) (b.jointVol ^ 2).toNNReal)
      P := by
  convert hasLaw_portfolio_gaussianReal h.gaussian (fun _ ↦ 1) using 3
  · simp [Fin.sum_univ_two]
  · simp [Fin.sum_univ_two, h.mean]
  · simp only [portfolioVarN, Fin.sum_univ_two, one_mul,
      covariance_self (h.gaussian.eval _).aemeasurable, covariance_comm (X 1) (X 0), h.var, h.cov,
      jointVol, Real.sq_sqrt b.jointVar_pos.le]
    ring

/-- **VaR diversifies on the book**: in every realization, at every level `α ∈ [1/2, 1)`, the
combined VaR is at most the sum of the standalone ones. All three are the closed form at the
normal quantile, and the combined volatility is at most `σ₁ + σ₂` (`gaussianVaR_subadditive`).
VaR is not subadditive for every law (`RiskMeasures/VaRSuperadditivity.lean`): the Gaussian law
and the level `α ≥ 1/2` are what make it so here. -/
theorem IsRealization.valueAtRisk_add_le (h : b.IsRealization P X) {α : ℝ}
    (hα : α ∈ Ico (1 / 2) 1) :
    valueAtRisk (fun ω ↦ X 0 ω + X 1 ω) P α ≤ valueAtRisk (X 0) P α + valueAtRisk (X 1) P α := by
  have hα' : α ∈ Ioo 0 1 := ⟨by linarith [hα.1], hα.2⟩
  rw [(gaussian_loss_report h.hasLaw_add b.jointVol_pos hα').1,
    (gaussian_loss_report (h.hasLaw 0) (b.vol_pos 0) hα').1,
    (gaussian_loss_report (h.hasLaw 1) (b.vol_pos 1) hα').1, jointVol]
  exact gaussianVaR_subadditive (b.vol_pos 0).le (b.vol_pos 1).le b.corr_mem.2.le
    ((PhiInv_nonneg_iff hα').2 hα.1)

omit [IsProbabilityMeasure P] in
/-- **ES diversifies on the book, at every level**: ES is subadditive for any two integrable
losses (`expectedShortfall_add_le`), Gaussian or not. -/
theorem IsRealization.expectedShortfall_add_le [IsProbabilityMeasure P] (h : b.IsRealization P X)
    {α : ℝ} (hα : α ∈ Ioo 0 1) :
    expectedShortfall (fun ω ↦ X 0 ω + X 1 ω) P α ≤
      expectedShortfall (X 0) P α + expectedShortfall (X 1) P α :=
  MathFin.expectedShortfall_add_le (integrable_of_hasLaw_gaussianReal (h.hasLaw 0))
    (integrable_of_hasLaw_gaussianReal (h.hasLaw 1)) hα

end Book

/-- An illustrative book: two positions whose losses have means `−1` and `−1/2` (both expected to
make money) and volatilities `5` and `5`, with correlation `0.28`. -/
noncomputable def sample : Book where
  mean := ![-1, -1 / 2]
  vol := ![5, 5]
  corr := 0.28
  vol_pos i := by fin_cases i <;> norm_num
  corr_mem := by norm_num
  sources := ["illustrative means, volatilities and correlation, in millions over one horizon"]
  unmodelled :=
    ["estimation error in the means, the volatilities and the correlation",
      "fat tails and tail dependence", "the nonlinearity of option positions",
      "trading within the horizon"]

/-- The sample's combined volatility is `√(25 + 14 + 25) = 8`. -/
theorem sample_jointVol : sample.jointVol = 8 := by
  rw [Book.jointVol, show sample.vol 0 ^ 2 + 2 * sample.corr * sample.vol 0 * sample.vol 1 +
    sample.vol 1 ^ 2 = 8 ^ 2 by norm_num [sample], Real.sqrt_sq (by norm_num)]

/-! ### The check -/

/-- **The risk report for `sample`**, the statement this file's build certifies. In every jointly
Gaussian realization of the book, at every level `α ∈ [1/2, 1)`, with `z = Φ⁻¹(α)` and
`ϕ` the standard normal density:
- the standalone VaRs are `−1 + 5z` and `−1/2 + 5z`, and the combined VaR is `−3/2 + 8z`, so
  diversification saves `2z ≥ 0`;
- the standalone ESs are `−1 + 5ϕ(z)/(1 − α)` and `−1/2 + 5ϕ(z)/(1 − α)`, and the combined ES is
  `−3/2 + 8ϕ(z)/(1 − α)`, so diversification saves `2ϕ(z)/(1 − α) > 0`;
- the combined loss exceeds its VaR with probability exactly `1 − α`, and its ES is the integral
  of the combined loss over that event divided by `1 − α`. -/
theorem sample_checked :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Fin 2 → Ω → ℝ), sample.IsRealization P X → ∀ α ∈ Ico (1 / 2 : ℝ) 1,
      (valueAtRisk (X 0) P α = -1 + 5 * PhiInv α ∧
        valueAtRisk (X 1) P α = -1 / 2 + 5 * PhiInv α ∧
        valueAtRisk (fun ω ↦ X 0 ω + X 1 ω) P α = -3 / 2 + 8 * PhiInv α ∧
        0 ≤ valueAtRisk (X 0) P α + valueAtRisk (X 1) P α
          - valueAtRisk (fun ω ↦ X 0 ω + X 1 ω) P α) ∧
      (expectedShortfall (X 0) P α = -1 + 5 * (gaussianPDFReal 0 1 (PhiInv α) / (1 - α)) ∧
        expectedShortfall (X 1) P α = -1 / 2 + 5 * (gaussianPDFReal 0 1 (PhiInv α) / (1 - α)) ∧
        expectedShortfall (fun ω ↦ X 0 ω + X 1 ω) P α =
          -3 / 2 + 8 * (gaussianPDFReal 0 1 (PhiInv α) / (1 - α)) ∧
        0 < expectedShortfall (X 0) P α + expectedShortfall (X 1) P α
          - expectedShortfall (fun ω ↦ X 0 ω + X 1 ω) P α) ∧
      P.real {ω | valueAtRisk (fun ω ↦ X 0 ω + X 1 ω) P α < X 0 ω + X 1 ω} = 1 - α ∧
      expectedShortfall (fun ω ↦ X 0 ω + X 1 ω) P α = (1 - α)⁻¹ *
        ∫ ω in {ω | valueAtRisk (fun ω ↦ X 0 ω + X 1 ω) P α < X 0 ω + X 1 ω}, X 0 ω + X 1 ω ∂P := by
  intro Ω _ P _ X h α hα
  have hα' : α ∈ Ioo 0 1 := ⟨by linarith [hα.1], hα.2⟩
  obtain ⟨hV, hE, htail, hmean⟩ := gaussian_loss_report h.hasLaw_add sample.jointVol_pos hα'
  obtain ⟨hV₀, hE₀, -⟩ := gaussian_loss_report (h.hasLaw 0) (sample.vol_pos 0) hα'
  obtain ⟨hV₁, hE₁, -⟩ := gaussian_loss_report (h.hasLaw 1) (sample.vol_pos 1) hα'
  have hϕ : 0 < gaussianPDFReal 0 1 (PhiInv α) / (1 - α) :=
    div_pos (gaussianPDFReal_pos _ _ _ one_ne_zero) (sub_pos.2 hα.2)
  rw [sample_jointVol] at hV hE
  simp only [gaussianVaR, gaussianCVaR, sample, Matrix.cons_val_zero, Matrix.cons_val_one]
    at hV hE hV₀ hE₀ hV₁ hE₁
  exact ⟨⟨hV₀, hV₁, by linarith, sub_nonneg.2 (h.valueAtRisk_add_le hα)⟩,
    ⟨hE₀, hE₁, by linarith, by linarith⟩, htail, hmean⟩

end MathFin.Examples.GaussianRiskReport
