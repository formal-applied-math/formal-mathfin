/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Backtest performance statistics

Finite-sample performance statistics for a backtest: the **Sharpe ratio**, **CAGR**,
**annualized volatility** and **max drawdown** of a sequence of period returns / an equity
curve `E : Fin n → ℝ`. These are sample statistics over a finite record of realized values,
not probabilistic objects — a different kind of object from a process-level drawdown
*law* (the distribution of a stochastic process's drawdown, not formalized in this
library), which would be a distribution over paths rather than a statistic of one
realized path.

## Conventions

Multiple conventions exist in the literature for these four quantities (sample vs.
population standard deviation, trading days vs. calendar days for `N`, zero vs. nonzero
risk-free rate). This file follows a plain zero-risk-free-rate, population-standard-
deviation convention, matching the way the Sharpe ratio, annualization and drawdown
measures are presented (Ch. 4, "Risk") in Bacon, *Practical Portfolio Performance
Measurement and Attribution* (2nd ed., 2008); the zero-risk-free-rate specialization is
this file's own choice — Bacon's Sharpe ratio carries a risk-free rate term. The
formulas:

* **Sharpe ratio** (`sharpeRatio`): `√N · mean(r) / std(r)`, zero risk-free rate, `N`
  periods per year, `std` the *population* standard deviation of the sample `r`
  (divide the sum of squared deviations by `n`, not `n - 1`).
* **CAGR** (`cagr`): `(E_final / E_initial) ^ (N / n) - 1` for an equity curve held over
  `n` periods, `N` periods per year.
* **Annualized volatility** (`annualizedVolatility`): `√N · std(r)`, same `std` as above.
* **Max drawdown** (`maxDrawdown`): the largest running-maximum-relative decline
  `DD_t = 1 - E_t / max_{s ≤ t} E_s` of an equity curve `E`.

Drawdown *duration* (the length of the longest drawdown) is not formalized here: a
run-length statistic needs its own definition (longest interval over which the curve
stays below a prior peak) and is left for a follow-up file if a concrete consumer needs it.

## Relation to existing performance code

Two other objects in the library are adjacent but distinct:

* `MathFin.sharpeRatio` (`Performance/Ratios.lean`) is the *parametric* Sharpe ratio
  `(μ − r_f) / σ` from already-known moments, with its own `√T` time-aggregation lemma
  `sharpeRatio_scaleT`. The `sharpeRatio` here is the *empirical* counterpart, computed
  from a finite sample of realized returns rather than supplied moments.
* `MathFin.maximumDrawdown` (`Performance/DownsideMetrics.lean`) is the largest *absolute*
  price decline `max_{i ≤ j} (price i − price j)` over a finite path. `maxDrawdown` here is
  the largest *relative* decline `1 − E_t / max_{s ≤ t} E_s`, the convention used in
  Bacon (2008) — a different normalization of the same running-maximum idea.

## Main results

* `sharpeRatio_scale_pos`, `annualizedVolatility_scale_pos`: both are invariant
  (resp. equivariant) under scaling every return by a positive constant — rescaling the
  unit returns are measured in (e.g. USD → cents) does not change the Sharpe ratio.
* `cagr_scale_pos`: CAGR is invariant under scaling both endpoints of the equity curve by
  the same positive constant (e.g. a currency redenomination).
* `drawdown_nonneg`, `drawdown_le_one`, `maxDrawdown_nonneg`, `maxDrawdown_le_one`: for a
  strictly positive equity curve, every drawdown — hence the max drawdown — lies in `[0, 1]`.
-/

@[expose] public section

noncomputable section

open Finset

namespace MathFin.Backtest

variable {n : ℕ}

/-- Sample mean of a finite sequence of period returns. -/
def sampleMean (r : Fin n → ℝ) : ℝ := (∑ i, r i) / n

/-- Sample (population) variance of a finite sequence of period returns: the sum of squared
deviations from the sample mean, divided by `n` (not `n - 1`). -/
def sampleVariance (r : Fin n → ℝ) : ℝ := (∑ i, (r i - sampleMean r) ^ 2) / n

/-- Sample (population) standard deviation. -/
def sampleStdDev (r : Fin n → ℝ) : ℝ := Real.sqrt (sampleVariance r)

/-- Sharpe ratio at zero risk-free rate: `√N · mean(r) / std(r)`, `N` periods per year. -/
def sharpeRatio (N : ℝ) (r : Fin n → ℝ) : ℝ := Real.sqrt N * sampleMean r / sampleStdDev r

/-- Annualized volatility: `√N · std(r)`, `N` periods per year. -/
def annualizedVolatility (N : ℝ) (r : Fin n → ℝ) : ℝ := Real.sqrt N * sampleStdDev r

/-- Compound annual growth rate of an equity curve held for `n` periods, `N` periods per
year: `(E_final / E_initial) ^ (N / n) - 1`. -/
def cagr (N : ℝ) (n : ℕ) (E_initial E_final : ℝ) : ℝ := (E_final / E_initial) ^ (N / n) - 1

/-- Running maximum of an equity curve up to and including time `t`. -/
def runningMax (E : Fin n → ℝ) (t : Fin n) : ℝ :=
    (univ.filter (· ≤ t)).sup' ⟨t, by simp⟩ E

/-- Drawdown at time `t`: the running-maximum-relative decline `1 - E_t / max_{s ≤ t} E_s`. -/
def drawdown (E : Fin n → ℝ) (t : Fin n) : ℝ := 1 - E t / runningMax E t

/-- Max drawdown over the whole equity curve. -/
def maxDrawdown (hn : 0 < n) (E : Fin n → ℝ) : ℝ :=
    haveI : NeZero n := ⟨hn.ne'⟩
    univ.sup' univ_nonempty (drawdown E)

/-! ## Scale invariance -/

theorem sampleMean_scale (c : ℝ) (r : Fin n → ℝ) :
    sampleMean (fun i ↦ c * r i) = c * sampleMean r := by
  unfold sampleMean
  rw [← Finset.mul_sum, mul_div_assoc]

theorem sampleVariance_scale (c : ℝ) (r : Fin n → ℝ) :
    sampleVariance (fun i ↦ c * r i) = c ^ 2 * sampleVariance r := by
  unfold sampleVariance
  rw [sampleMean_scale]
  have hterm : ∀ i, (c * r i - c * sampleMean r) ^ 2 = c ^ 2 * (r i - sampleMean r) ^ 2 := by
    intro i; ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, mul_div_assoc]

theorem sampleStdDev_scale_pos {c : ℝ} (hc : 0 < c) (r : Fin n → ℝ) :
    sampleStdDev (fun i ↦ c * r i) = c * sampleStdDev r := by
  unfold sampleStdDev
  rw [sampleVariance_scale, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]

/-- Rescaling every return by a positive constant (e.g. a currency redenomination) does not
change the Sharpe ratio: both the numerator and the denominator scale by `c`, which cancels. -/
theorem sharpeRatio_scale_pos {c : ℝ} (hc : 0 < c) (N : ℝ) (r : Fin n → ℝ) :
    sharpeRatio N (fun i ↦ c * r i) = sharpeRatio N r := by
  unfold sharpeRatio
  rw [sampleMean_scale, sampleStdDev_scale_pos hc,
    show Real.sqrt N * (c * sampleMean r) = c * (Real.sqrt N * sampleMean r) by ring,
    mul_div_mul_left _ _ hc.ne']

/-- Annualized volatility scales linearly with the unit returns are measured in. -/
theorem annualizedVolatility_scale_pos {c : ℝ} (hc : 0 < c) (N : ℝ) (r : Fin n → ℝ) :
    annualizedVolatility N (fun i ↦ c * r i) = c * annualizedVolatility N r := by
  unfold annualizedVolatility
  rw [sampleStdDev_scale_pos hc, mul_left_comm]

/-- CAGR is unchanged by scaling both endpoints of the equity curve by the same positive
constant (e.g. a currency redenomination): only the ratio `E_final / E_initial` matters. -/
theorem cagr_scale_pos {c : ℝ} (hc : 0 < c) (N : ℝ) (n : ℕ) (E_initial E_final : ℝ) :
    cagr N n (c * E_initial) (c * E_final) = cagr N n E_initial E_final := by
  unfold cagr
  rw [mul_div_mul_left _ _ hc.ne']

/-! ## Max drawdown lies in `[0, 1]` for a strictly positive equity curve -/

theorem le_runningMax {E : Fin n → ℝ} (t : Fin n) : E t ≤ runningMax E t :=
    Finset.le_sup' E (by simp : t ∈ univ.filter (· ≤ t))

theorem runningMax_pos {E : Fin n → ℝ} (hE : ∀ t, 0 < E t) (t : Fin n) : 0 < runningMax E t := by
  obtain ⟨s, hs, hsE⟩ := Finset.exists_mem_eq_sup' (⟨t, by simp⟩ : (univ.filter (· ≤ t)).Nonempty) E
  rw [runningMax, hsE]
  exact hE s

theorem drawdown_nonneg {E : Fin n → ℝ} (hE : ∀ t, 0 < E t) (t : Fin n) : 0 ≤ drawdown E t := by
  have h1 : E t / runningMax E t ≤ 1 :=
    (div_le_one (runningMax_pos hE t)).mpr (le_runningMax t)
  unfold drawdown; linarith

theorem drawdown_le_one {E : Fin n → ℝ} (hE : ∀ t, 0 < E t) (t : Fin n) : drawdown E t ≤ 1 := by
  have h1 : 0 ≤ E t / runningMax E t := le_of_lt (div_pos (hE t) (runningMax_pos hE t))
  unfold drawdown; linarith

/-- Max drawdown of a strictly positive equity curve is nonnegative. -/
theorem maxDrawdown_nonneg (hn : 0 < n) {E : Fin n → ℝ} (hE : ∀ t, 0 < E t) :
    0 ≤ maxDrawdown hn E := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨t, -⟩ := univ_nonempty (α := Fin n)
  exact le_trans (drawdown_nonneg hE t) (Finset.le_sup' (drawdown E) (mem_univ t))

/-- Max drawdown of a strictly positive equity curve is at most `1`. -/
theorem maxDrawdown_le_one (hn : 0 < n) {E : Fin n → ℝ} (hE : ∀ t, 0 < E t) :
    maxDrawdown hn E ≤ 1 := by
  haveI : NeZero n := ⟨hn.ne'⟩
  exact Finset.sup'_le univ_nonempty (drawdown E) (fun t _ ↦ drawdown_le_one hE t)

end MathFin.Backtest

end
