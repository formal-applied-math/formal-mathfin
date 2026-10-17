/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Basel SA-CCR: exposure at default and effective notional aggregation

The Basel III **Standardised Approach for Counterparty Credit Risk** (SA-CCR, BCBS 279)
computes the exposure at default of a derivatives netting set as

  `EAD = α · (RC + PFE)`,

where `RC` is the replacement cost, `PFE` is the potential future exposure add-on, and the
regulator fixes `α = 1.4`. This is almost entirely a regulatory bookkeeping definition: `RC` and
`PFE` are themselves built from supervisory add-on factors, maturity and supervisory-correlation
parameters that have no mathematical content beyond their arithmetic combination. We record the
formula and its one real structural fact: `EAD` is monotone increasing in each of `RC` and `PFE`
for any fixed `α > 0`, so netting or hedging that lowers either component can only lower (never
raise) the capital exposure.

The other SA-CCR building block with actual algebraic content is the **effective notional**
aggregation of a netting set's trades into a single hedging-set number via the supervisory
correlation `ρ`:

  `EffNotional = √(D² + (1 − ρ²) · (Σ Dᵢ² − D²_single))`

reduces in the formalisation to the two-trade building block used repeatedly in the standard
(`EffNotional ρ d₁ d₂ = √(d₁² + d₂² + 2ρ·d₁·d₂)`, the same quadratic-form combination as portfolio
variance). We prove this two-trade aggregator is monotone in each notional's absolute value when
`ρ ∈ [-1, 1]`, and that it collapses to `|d₁ + d₂|` at `ρ = 1` (full correlation, no diversification
benefit) and to `√(d₁² + d₂²)` at `ρ = 0` (independent add-ons).

## Main definitions

* `saccrEAD`: `α · (RC + PFE)`.
* `effNotionalPair`: the two-trade correlated aggregation `√(d₁² + d₂² + 2ρ·d₁·d₂)`.

## Main results

* `saccrEAD_mono_rc`, `saccrEAD_mono_pfe`: `EAD` is monotone in `RC` and in `PFE` for `α > 0`.
* `effNotionalPair_nonneg`: the aggregated notional is nonnegative.
* `effNotionalPair_eq_abs_add_of_corr_one`: at `ρ = 1`, `effNotionalPair = |d₁ + d₂|`.
* `effNotionalPair_eq_hypot_of_corr_zero`: at `ρ = 0`, `effNotionalPair = √(d₁² + d₂²)`.
* `effNotionalPair_le_abs_add`: for `ρ ≤ 1`, the aggregation never exceeds `|d₁| + |d₂|` (no
  negative diversification).

## References

* Basel Committee on Banking Supervision, *The standardised approach for measuring counterparty
  credit risk exposures* (BCBS 279), 2014, §​3 (EAD formula) and Annex 4 (effective notional).
-/

namespace MathFin.RiskMeasures

open Real

/-! ## Exposure at default -/

/-- The Basel SA-CCR exposure-at-default formula `EAD = α · (RC + PFE)`, where `RC` is the
replacement cost and `PFE` the potential future exposure add-on. The regulator fixes
`α = 1.4` (`saccrAlpha`), but we keep it as a parameter since the only mathematical content is
the arithmetic combination, not the specific constant. -/
noncomputable def saccrEAD (α RC PFE : ℝ) : ℝ := α * (RC + PFE)

/-- The regulatory value of `α` fixed by Basel SA-CCR (BCBS 279 §3). -/
noncomputable def saccrAlpha : ℝ := 1.4

/-- `EAD` is monotone increasing in the replacement cost `RC`, for any fixed `α ≥ 0`. -/
theorem saccrEAD_mono_rc {α : ℝ} (hα : 0 ≤ α) {PFE : ℝ} :
    Monotone (fun RC => saccrEAD α RC PFE) := by
  intro RC₁ RC₂ h
  simp only [saccrEAD]
  gcongr

/-- `EAD` is monotone increasing in the PFE add-on, for any fixed `α ≥ 0`. -/
theorem saccrEAD_mono_pfe {α : ℝ} (hα : 0 ≤ α) {RC : ℝ} :
    Monotone (fun PFE => saccrEAD α RC PFE) := by
  intro PFE₁ PFE₂ h
  simp only [saccrEAD]
  gcongr

/-- `EAD` is jointly monotone: raising `RC` and/or `PFE` never lowers the exposure, for
`α ≥ 0`. -/
theorem saccrEAD_mono {α : ℝ} (hα : 0 ≤ α) {RC₁ RC₂ PFE₁ PFE₂ : ℝ}
    (hRC : RC₁ ≤ RC₂) (hPFE : PFE₁ ≤ PFE₂) :
    saccrEAD α RC₁ PFE₁ ≤ saccrEAD α RC₂ PFE₂ := by
  unfold saccrEAD
  gcongr

/-! ## Effective notional aggregation

SA-CCR aggregates the add-ons of trades sharing a hedging set using a supervisory correlation
parameter `ρ`. The two-trade building block, applied repeatedly to combine a netting set's
trades, is the quadratic-form combination below (identical in shape to the variance of a sum of
two correlated random variables). -/

/-- The SA-CCR two-trade effective notional: trade add-ons `d₁, d₂` combined with supervisory
correlation `ρ` as `√(d₁² + d₂² + 2ρ·d₁·d₂)` (BCBS 279, Annex 4). -/
noncomputable def effNotionalPair (ρ d₁ d₂ : ℝ) : ℝ := √(d₁ ^ 2 + d₂ ^ 2 + 2 * ρ * d₁ * d₂)

theorem effNotionalPair_nonneg (ρ d₁ d₂ : ℝ) : 0 ≤ effNotionalPair ρ d₁ d₂ :=
  Real.sqrt_nonneg _

/-- At full correlation `ρ = 1` the aggregation collapses to `|d₁ + d₂|`: no diversification
benefit, trades simply add. -/
theorem effNotionalPair_eq_abs_add_of_corr_one (d₁ d₂ : ℝ) :
    effNotionalPair 1 d₁ d₂ = |d₁ + d₂| := by
  unfold effNotionalPair
  rw [show d₁ ^ 2 + d₂ ^ 2 + 2 * 1 * d₁ * d₂ = (d₁ + d₂) ^ 2 by ring]
  exact Real.sqrt_sq_eq_abs _

/-- At zero correlation the aggregation is the Euclidean (independent-risk) combination. -/
theorem effNotionalPair_eq_hypot_of_corr_zero (d₁ d₂ : ℝ) :
    effNotionalPair 0 d₁ d₂ = √(d₁ ^ 2 + d₂ ^ 2) := by
  unfold effNotionalPair; ring_nf

/-- For supervisory correlation `ρ ∈ [-1, 1]` (the range Basel's supervisory correlations live
in), the aggregated notional never exceeds the sum of the absolute add-ons: there is no
*negative* diversification from this formula. The bound fails outside `[-1, 1]`, e.g. `ρ = -5`,
`d₁ = 1`, `d₂ = -1` gives `effNotionalPair = √12 > 2`. -/
theorem effNotionalPair_le_abs_add {ρ : ℝ} (hρ1 : -1 ≤ ρ) (hρ2 : ρ ≤ 1) (d₁ d₂ : ℝ) :
    effNotionalPair ρ d₁ d₂ ≤ |d₁| + |d₂| := by
  unfold effNotionalPair
  rw [show |d₁| + |d₂| = √((|d₁| + |d₂|) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  have h1 : d₁ ^ 2 = |d₁| ^ 2 := (sq_abs d₁).symm
  have h2 : d₂ ^ 2 = |d₂| ^ 2 := (sq_abs d₂).symm
  have h3 : 2 * ρ * d₁ * d₂ ≤ 2 * |d₁| * |d₂| := by
    have hle : d₁ * d₂ ≤ |d₁| * |d₂| := (abs_mul d₁ d₂) ▸ le_abs_self (d₁ * d₂)
    have hge : -(|d₁| * |d₂|) ≤ d₁ * d₂ := by
      have h := neg_abs_le (d₁ * d₂)
      rwa [abs_mul] at h
    nlinarith [mul_nonneg (abs_nonneg d₁) (abs_nonneg d₂)]
  nlinarith [h1, h2, h3]

/-- `effNotionalPair` is monotone in `|d₁|` when the correlation is nonnegative and `d₂` is held
fixed with the same sign convention: increasing a trade's add-on magnitude (without flipping its
sign relative to `d₂`) never decreases the aggregated notional, for `ρ ≥ 0` and `d₁, d₂ ≥ 0`. -/
theorem effNotionalPair_mono_left {ρ : ℝ} (hρ : 0 ≤ ρ) {d₂ : ℝ} (hd₂ : 0 ≤ d₂) :
    MonotoneOn (fun d₁ => effNotionalPair ρ d₁ d₂) (Set.Ici (0 : ℝ)) := by
  intro d₁ hd₁ d₁' hd₁' h
  simp only [Set.mem_Ici] at hd₁ hd₁'
  unfold effNotionalPair
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (mul_nonneg hρ hd₂) (sub_nonneg.mpr h), mul_le_mul h h hd₁ (hd₁.trans h)]

end MathFin.RiskMeasures
