/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Using the library: a minimum-variance portfolio

A worked use of the library from outside it, the way an allocator would split money between two
assets to take as little risk as possible. Two assets are described by their volatilities and
their correlation. This file

1. records the two assets as data, with where the numbers come from and what the allocation
   leaves out;
2. proves the nondegeneracy condition `D = σ₁² − 2ρσ₁σ₂ + σ₂² > 0` from the numbers;
3. computes the minimum-variance weight `w* = 3/4` and the minimum variance `0.03375`;
4. proves that no other weight does better, that `w*` is a critical point of the variance under
   the budget constraint, and that, for any square-integrable returns with these volatilities and
   this correlation, the lower bound and the value at `w*` are statements about the variance of
   the portfolio's return, and that such returns exist (`AssetPair.exists_returns`);
5. reads off the diversification benefit: the minimum variance is below that of either asset
   alone.

`sample_checked` is the single statement the build certifies.

## What the library supplies

* `MathFin.portfolioVarTwo`, `minVarWeightTwo`, `minPortfolioVarTwo`, `minVarDenom`: the variance
  of a two-asset mix, the minimiser, the minimum and the nondegeneracy quantity.
* `MathFin.portfolioVarTwo_ge_min`, `portfolioVarTwo_at_minVarWeight`: the variance is at least
  `V_min`, with equality at `w*` (both from `portfolioVarTwo_eq_quad`, `D (w − w*)² + V_min`).
* `MathFin.isConstrainedVarianceCriticalPoint_minVarWeightTwo`: `w*` satisfies the Lagrangian
  first-order condition under the budget constraint.
* `MathFin.portfolioVarTwo_eq_variance`: the closed form is the variance of the portfolio return.
* `MathFin.gaussianPair`, `variance_gaussianPair`, `covariance_gaussianPair`: a pair of returns with
  any given volatilities and correlation, on the Cholesky pair.

## What it does not

The weights are fixed for one period and may be negative (short positions are allowed). Expected
returns play no part: this is the minimum-variance portfolio, not a mean–variance optimum. The
volatilities and correlation are taken as known; estimating them is outside the model. The
variance clause is quantified over square-integrable returns with the given moments, and one such
pair is constructed (Gaussian, on `ℝ × ℝ`); nothing in the clause depends on that choice.

## Source

The shape of the file follows the capped-call example
(`MathFinExamples/Applications/CappedCall.lean`). The numbers below are illustrative.
-/

namespace MathFin.Examples.MinimumVariance

open MeasureTheory ProbabilityTheory

/-! ### The assets, as data -/

/-- Two assets, by their annual volatilities and their correlation, with where the numbers come
from and what the allocation leaves out. -/
structure AssetPair where
  /-- The volatility of asset 1. -/
  vol₁ : ℝ
  /-- The volatility of asset 2. -/
  vol₂ : ℝ
  /-- The correlation of their returns. -/
  corr : ℝ
  /-- Where the numbers come from. -/
  sources : List String
  /-- What the allocation does not model. -/
  unmodelled : List String

/-- Illustrative assets: volatilities `20%` and `30%`, correlation `0.25`. -/
noncomputable def sample : AssetPair where
  vol₁ := 0.2
  vol₂ := 0.3
  corr := 0.25
  sources := ["illustrative annual volatilities and correlation"]
  unmodelled :=
    ["expected returns", "estimation error in the volatilities and the correlation",
      "rebalancing within the period", "transaction costs", "limits on short positions"]

/-! ### The numbers -/

/-- The nondegeneracy quantity `D = 0.04 − 0.03 + 0.09 = 0.1` is positive. -/
theorem sample_denom : minVarDenom sample.vol₁ sample.vol₂ sample.corr = 0.1 := by
  norm_num [minVarDenom, sample]

/-- The minimum-variance weight on asset 1 is `w* = (0.09 − 0.015) / 0.1 = 3/4`. -/
theorem sample_weight : minVarWeightTwo sample.vol₁ sample.vol₂ sample.corr = 3 / 4 := by
  rw [minVarWeightTwo, sample_denom]
  norm_num [sample]

/-- The minimum variance is `V_min = 0.04 · 0.09 · (1 − 0.0625) / 0.1 = 0.03375`, a volatility of
about `18.4%` (a numerical remark, not proved). -/
theorem sample_minVar : minPortfolioVarTwo sample.vol₁ sample.vol₂ sample.corr = 0.03375 := by
  rw [minPortfolioVarTwo, sample_denom]
  norm_num [sample]

/-- **Returns with these moments exist**, whenever the correlation is in `[−1, 1]`: on the
Cholesky pair, `R₁ = σ₁ Z₁` and `R₂ = σ₂ Z₂` (`gaussianPair` with zero means) are
square-integrable with the pair's volatilities and correlation. So a statement about every such
pair of returns is not about an empty class. -/
theorem AssetPair.exists_returns (a : AssetPair) (hcorr : a.corr ^ 2 ≤ 1) :
    ∃ R₁ R₂ : ℝ × ℝ → ℝ, MemLp R₁ 2 (bivariateNormalLaw a.corr) ∧
      MemLp R₂ 2 (bivariateNormalLaw a.corr) ∧ Var[R₁; bivariateNormalLaw a.corr] = a.vol₁ ^ 2 ∧
      Var[R₂; bivariateNormalLaw a.corr] = a.vol₂ ^ 2 ∧
      cov[R₁, R₂; bivariateNormalLaw a.corr] = a.corr * a.vol₁ * a.vol₂ :=
  ⟨gaussianPair 0 ![a.vol₁, a.vol₂] 0, gaussianPair 0 ![a.vol₁, a.vol₂] 1,
    memLp_gaussianPair _ _ _ _, memLp_gaussianPair _ _ _ _,
    by simpa using variance_gaussianPair hcorr 0 ![a.vol₁, a.vol₂] 0,
    by simpa using variance_gaussianPair hcorr 0 ![a.vol₁, a.vol₂] 1,
    by simpa using covariance_gaussianPair a.corr 0 ![a.vol₁, a.vol₂]⟩

/-! ### The check -/

/-- **The allocation check for `sample`**, the statement this file's build certifies:
- the minimum-variance weight on asset 1 is `3/4`, and the minimum variance is `0.03375`;
- every weight gives a variance of at least `0.03375`, with equality at `3/4`;
- `3/4` is a critical point of the variance under the budget constraint;
- `0.03375` is below the variance `0.04` of asset 1 alone and `0.09` of asset 2 alone;
- square-integrable returns with these volatilities and this correlation exist, and for any such
  returns the variance of
  the portfolio return with weight `w` on asset 1 is at least `0.03375`, and is `0.03375` at
  `w = 3/4`. -/
theorem sample_checked :
    minVarWeightTwo sample.vol₁ sample.vol₂ sample.corr = 3 / 4 ∧
      minPortfolioVarTwo sample.vol₁ sample.vol₂ sample.corr = 0.03375 ∧
      (∀ w, 0.03375 ≤ portfolioVarTwo sample.vol₁ sample.vol₂ sample.corr w) ∧
      portfolioVarTwo sample.vol₁ sample.vol₂ sample.corr (3 / 4) = 0.03375 ∧
      IsConstrainedVarianceCriticalPoint Finset.univ
        (covTwo sample.vol₁ sample.vol₂ sample.corr) 0 ![3 / 4, 1 - 3 / 4] ∧
      (0.03375 : ℝ) < sample.vol₁ ^ 2 ∧ (0.03375 : ℝ) < sample.vol₂ ^ 2 ∧
      (∃ R₁ R₂ : ℝ × ℝ → ℝ, MemLp R₁ 2 (bivariateNormalLaw sample.corr) ∧
        MemLp R₂ 2 (bivariateNormalLaw sample.corr) ∧
        Var[R₁; bivariateNormalLaw sample.corr] = sample.vol₁ ^ 2 ∧
        Var[R₂; bivariateNormalLaw sample.corr] = sample.vol₂ ^ 2 ∧
        cov[R₁, R₂; bivariateNormalLaw sample.corr] = sample.corr * sample.vol₁ * sample.vol₂) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (R₁ R₂ : Ω → ℝ),
        MemLp R₁ 2 P → MemLp R₂ 2 P → Var[R₁; P] = sample.vol₁ ^ 2 →
        Var[R₂; P] = sample.vol₂ ^ 2 → cov[R₁, R₂; P] = sample.corr * sample.vol₁ * sample.vol₂ →
        (∀ w : ℝ, 0.03375 ≤ Var[w • R₁ + (1 - w) • R₂; P]) ∧
          Var[(3 / 4 : ℝ) • R₁ + (1 - 3 / 4 : ℝ) • R₂; P] = 0.03375 := by
  have hD : 0 < minVarDenom sample.vol₁ sample.vol₂ sample.corr := by
    rw [sample_denom]
    norm_num
  have hge (w : ℝ) : 0.03375 ≤ portfolioVarTwo sample.vol₁ sample.vol₂ sample.corr w :=
    sample_minVar ▸ portfolioVarTwo_ge_min hD w
  have hat : portfolioVarTwo sample.vol₁ sample.vol₂ sample.corr (3 / 4) = 0.03375 := by
    rw [← sample_weight, portfolioVarTwo_at_minVarWeight hD.ne', sample_minVar]
  refine ⟨sample_weight, sample_minVar, hge, hat, ?_, by norm_num [sample],
    by norm_num [sample], sample.exists_returns (by norm_num [sample]),
    fun P _ R₁ R₂ h₁ h₂ hv₁ hv₂ hc ↦ ⟨fun w ↦ ?_, ?_⟩⟩
  · simpa only [sample_weight] using isConstrainedVarianceCriticalPoint_minVarWeightTwo hD.ne'
  · exact (hge w).trans_eq (portfolioVarTwo_eq_variance h₁ h₂ hv₁ hv₂ hc w)
  · exact (portfolioVarTwo_eq_variance h₁ h₂ hv₁ hv₂ hc _).symm.trans hat

end MathFin.Examples.MinimumVariance
