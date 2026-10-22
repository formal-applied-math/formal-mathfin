/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.RiskMeasures.Gaussian

/-!
# Student-t VaR and expected shortfall closed forms

A "Student-t (Cornish-Fisher-style) parametric VaR" was wanted in the closed form

  `VaR_t = -1/α · (1-ν)⁻¹ · (ν-2+x_α²) · t.pdf(x_α) · σ - μ`.

**That formula is not a VaR formula.** Checked against McNeil, Frey and Embrechts,
*Quantitative Risk Management* (2015) — the same book this file's sibling
`RiskMeasures/RiskClosedForms.lean` cites (there, Example 2.14) — Example 2.15 (the univariate
Student-t density itself is Appendix A.2): for a location-scale Student-t loss
`L = μ + σ T`, `T ~ t_ν` standard (unit scale, not unit variance),

  `VaR_α(L) = μ + σ · t_ν⁻¹(α)`                                              (just the quantile)
  `ES_α(L) = μ + σ · g_ν(t_ν⁻¹(α))/(1 - α) · (ν + t_ν⁻¹(α)²)/(ν - 1)`,  `ν > 1`

where `g_ν` is the standard Student-t density. The above formula is the **second** line
(expected shortfall, not VaR) rewritten for losses defined as the *negative* of a return, with
`α` itself the left-tail probability and `x_α < 0`: `-1/α · (1-ν)⁻¹ = 1/(α(ν-1))` there plays the
role of `1/(1-α) · 1/(ν-1)` here, and the `-μ` plays the role of `+μ` for a loss defined with the
opposite sign — an algebraically valid rewrite of the same closed form, not a second error. The
`ν - 2` is *not* itself an error either: it is the unit-*variance*
standardization used in Christoffersen's *Elements of Financial Risk Management* (the
"Cornish-Fisher-style" chapter this formula is drawn from). Writing `Y = T·√((ν-2)/ν)` rescales the
standard `T ~ t_ν` to `Var Y = 1` (`ν > 2`), with standardized density
`f_Y(y) = √(ν/(ν-2)) · g_ν(y·√(ν/(ν-2)))`; substituting into the `g_ν`/`t_ν⁻¹(α)` form above
turns the `ν + t_ν⁻¹(α)²` factor into `ν - 2 + y_α²` for the standardized quantile `y_α`, with
`f_Y` in place of `g_ν` — the same closed form in a different scale convention, not a bug
to fix. This file formalizes the two real closed forms directly, in the unit-*scale* `(1-α)`-
upper-tail loss convention of the source (McNeil-Frey-Embrechts) rather than re-deriving the
unit-*variance* rewrite: `studentTValueAtRisk`, the honest (trivial) VaR quantile closed form, and
`studentTExpectedShortfall`, the pdf-based closed form this formula was actually describing, with
the `ν` matching this file's own scale convention rather than the unit-variance rewrite's `ν - 2`.

Mathlib has no Student-t distribution at all (no pdf, no law, no quantile function) at the
pinned version, so unlike `RiskMeasures/GaussianValueAtRisk.lean` there is no `HasLaw`-level
bridge here: nothing below is proved from a measure-theoretic tail-probability definition of
VaR/ES for an actual Student-t-distributed random variable. `studentTPdf` is defined directly
from `Real.Gamma`, matching the textbook density formula, and `studentTValueAtRisk` /
`studentTExpectedShortfall` are *stated* closed forms (parametrized by the quantile `x_α`, as
`RiskMeasures/Gaussian.lean` parametrizes on `z` rather than on `α` directly). What is proved is
purely algebraic: positivity of the density (`studentTPdf_pos`), affine invariance of both
closed forms (`studentTValueAtRisk_affine`, `studentTExpectedShortfall_affine`), and positivity
of the ES closed form (`studentTExpectedShortfall_pos`). NOT attempted: any measure-theoretic
VaR/ES statement for an actual Student-t random variable (no Mathlib support to bridge to), and
any `ν → ∞` Gaussian-limit statement (would need a limit argument on `Real.Gamma` ratios this
file does not undertake) — both left as disclosed gaps.

## Main results

* `studentTPdf`: the standard (unit-scale) Student-t density `g_ν`, built from `Real.Gamma`.
* `studentTPdf_pos`: `g_ν(x) > 0` for `ν > 0`.
* `studentTValueAtRisk`: the (trivial) VaR closed form `μ + σ x_α`, and
  `studentTValueAtRisk_eq_gaussianVaR` — it is literally `RiskMeasures.Gaussian.gaussianVaR`
  evaluated at the Student-t quantile `x_α` in place of the normal quantile `z`: the
  location-scale VaR quantile formula is the same closed form for any quantile function.
* `studentTExpectedShortfall`: the pdf-based ES closed form, meaningful only for `ν > 1`, `α < 1`
  (outside that range the Lean term is a junk value: e.g. `ν = 1` or `α = 1` collapses it to `μ`
  via `x/0 = 0`, whereas the real ES diverges there).
* `studentTValueAtRisk_affine`, `studentTExpectedShortfall_affine`: affine invariance of each
  closed form, `a ≥ 0`, matching `gaussianVaR_affine` / `gaussianCVaR_affine` (volatility scales
  by `|a|·σ`, so `0 ≤ a` is load-bearing).
* `studentTExpectedShortfall_pos`: the ES closed form is positive for a centered, positively
  scaled loss (`μ = 0`, `σ > 0`) at any quantile `x_α` (the `x_α²` term needs no sign hypothesis).

The general `valueAtRisk_le_expectedShortfall` fact (McNeil-Frey-Embrechts' VaR ≤ ES) is
deliberately NOT re-proved here for these closed forms: `(ν+x_α²)/(ν-1) ≥ 1` alone does not make
`σ·(g_ν(x_α)/(1-α))·(ν+x_α²)/(ν-1) ≥ σ·x_α` for arbitrary `x_α` (the density `g_ν(x_α)` can be
far below `1`, e.g. at a large `x_α`), so stating it as an unconditional sanity lemma here would
be dressing up a false claim as a theorem; the real inequality needs the actual tail-probability
definitions and is out of scope without a `HasLaw` bridge.
-/

@[expose] public section

namespace MathFin

open Real

/-- The standard (unit-scale, *not* unit-variance) Student-t density with `ν` degrees of
freedom, `g_ν(x) = Γ((ν+1)/2) / (√(νπ) Γ(ν/2)) · (1 + x²/ν)^(-(ν+1)/2)`
(McNeil-Frey-Embrechts, *Quantitative Risk Management*, Appendix A.2). -/
noncomputable def studentTPdf (ν x : ℝ) : ℝ :=
  Gamma ((ν + 1) / 2) / (Real.sqrt (ν * π) * Gamma (ν / 2)) * (1 + x ^ 2 / ν) ^ (-(ν + 1) / 2)

/-- The density is positive for `ν > 0`: a ratio of positive Gammas times a positive power. -/
theorem studentTPdf_pos {ν : ℝ} (hν : 0 < ν) (x : ℝ) : 0 < studentTPdf ν x := by
  have hΓ1 : 0 < Gamma ((ν + 1) / 2) := Gamma_pos_of_pos (by linarith)
  have hΓ2 : 0 < Gamma (ν / 2) := Gamma_pos_of_pos (by linarith)
  have hπ : 0 < ν * π := mul_pos hν pi_pos
  have hbase : 0 < 1 + x ^ 2 / ν := by positivity
  unfold studentTPdf
  have : 0 < Real.sqrt (ν * π) * Gamma (ν / 2) := mul_pos (Real.sqrt_pos.2 hπ) hΓ2
  positivity

/-- **Student-t value-at-risk** at quantile `x_α` for a location-scale loss `L = μ + σ T`,
`T ~ t_ν`: `VaR_α(L) = μ + σ x_α`, the same quantile closed form as `gaussianVaR`
(`RiskMeasures/Gaussian.lean`), with `x_α` in place of `z = Φ⁻¹(α)`. This is the actual VaR
closed form (McNeil-Frey-Embrechts, Example 2.15); it carries no pdf term. -/
noncomputable def studentTValueAtRisk (μ σ xα : ℝ) : ℝ := μ + σ * xα

/-- **The Student-t VaR closed form is the Gaussian one**, at the Student-t quantile:
the location-scale VaR formula `μ + σ·q` does not depend on which distribution the
quantile `q` comes from, only on it being *a* quantile of the standardized loss. This
makes literal the parallel the definition's docstring draws with `gaussianVaR`
(`RiskMeasures/Gaussian.lean`). -/
theorem studentTValueAtRisk_eq_gaussianVaR (μ σ xα : ℝ) :
    studentTValueAtRisk μ σ xα = gaussianVaR μ σ xα := rfl

/-- **Student-t expected shortfall** at quantile `x_α` and level `α` for a location-scale loss
`L = μ + σ T`, `T ~ t_ν`: `ES_α(L) = μ + σ · g_ν(x_α)/(1-α) · (ν + x_α²)/(ν-1)`
(McNeil-Frey-Embrechts, Example 2.15). Meaningful only for `ν > 1`, `α < 1`: outside that range
this is a junk value (`x/0 = 0` collapses it to `μ`), not the real (divergent) ES. This, not a
VaR, is the closed form the formula in the module docstring was actually describing (in the
unit-variance convention). -/
noncomputable def studentTExpectedShortfall (ν μ σ xα α : ℝ) : ℝ :=
  μ + σ * (studentTPdf ν xα / (1 - α)) * ((ν + xα ^ 2) / (ν - 1))

/-- **ES affine invariance**: `ES_α(a·L + b) = a·ES_α(L) + b` for `a ≥ 0`, matching
`gaussianCVaR_affine` (volatility scales by `|a|·σ`, so `0 ≤ a` is load-bearing). -/
theorem studentTExpectedShortfall_affine (ν μ σ xα α a b : ℝ) (ha : 0 ≤ a) :
    studentTExpectedShortfall ν (a * μ + b) (|a| * σ) xα α =
      a * studentTExpectedShortfall ν μ σ xα α + b := by
  unfold studentTExpectedShortfall
  rw [abs_of_nonneg ha]; ring

/-- **VaR affine invariance**: `VaR_α(a·L + b) = a·VaR_α(L) + b` for `a ≥ 0`. Since
`studentTValueAtRisk_eq_gaussianVaR` identifies this closed form with `gaussianVaR` pointwise,
the Gaussian file's own affine-invariance proof (`gaussianVaR_affine`) transfers directly —
this is the import earning its keep, not just the `rfl` identification above. -/
theorem studentTValueAtRisk_affine (μ σ xα a b : ℝ) (ha : 0 ≤ a) :
    studentTValueAtRisk (a * μ + b) (|a| * σ) xα = a * studentTValueAtRisk μ σ xα + b :=
  gaussianVaR_affine μ σ xα a b ha

/-- **The ES closed form is positive** for a centered, positively-scaled loss (`μ = 0`, `σ > 0`)
at any quantile `x_α`, with `ν > 1` and `α < 1`: a sanity check standing in for a
measure-theoretic positivity statement this file cannot derive (no `HasLaw` bridge is
available). -/
theorem studentTExpectedShortfall_pos {ν σ xα α : ℝ} (hν : 1 < ν) (hσ : 0 < σ) (hα : α < 1) :
    0 < studentTExpectedShortfall ν 0 σ xα α := by
  have hνpos : 0 < ν := by linarith
  have hpdf : 0 < studentTPdf ν xα := studentTPdf_pos hνpos xα
  have h1α : 0 < 1 - α := sub_pos.2 hα
  have hnum : 0 < ν + xα ^ 2 := by positivity
  have hden : 0 < ν - 1 := by linarith
  unfold studentTExpectedShortfall
  have : 0 < σ * (studentTPdf ν xα / (1 - α)) * ((ν + xα ^ 2) / (ν - 1)) := by positivity
  linarith

end MathFin
