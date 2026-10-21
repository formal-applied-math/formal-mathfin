/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
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
for any fixed `α ≥ 0`, so netting or hedging that lowers either component can only lower (never
raise) the capital exposure.

The other SA-CCR building block with algebraic content is the **effective notional** of an
interest-rate hedging set. SA-CCR splits the trades of one currency into three maturity buckets
(under one year, one to five years, over five years) with signed bucket effective notionals
`D₁, D₂, D₃`, and aggregates them as

  `EffectiveNotional = √(D₁² + D₂² + D₃² + 1.4·D₁·D₂ + 1.4·D₂·D₃ + 0.6·D₁·D₃)`,

that is, with correlation `0.7` between adjacent buckets and `0.3` between the first and the third
(Basel Framework CRE52.57). When two buckets are populated this is exactly

  `effNotionalPair ρ d₁ d₂ = √(d₁² + d₂² + 2ρ·d₁·d₂)`,

at `ρ = 0.7` (adjacent buckets) or `ρ = 0.3` (the first and third). It is the same quadratic form
as the standard deviation of a sum of two correlated risks. It is not the single-factor
aggregation that SA-CCR uses for the credit, equity and commodity classes,
`√((Σₖ ρₖ·Aₖ)² + Σₖ (1 − ρₖ²)·Aₖ²)` over entity-level add-ons `Aₖ`, whose two-entity cross term
with equal `ρ` is `2ρ²·A₁·A₂`. We prove that `effNotionalPair` collapses to `|d₁ + d₂|` at `ρ = 1`
(full correlation, no diversification benefit) and to `√(d₁² + d₂²)` at `ρ = 0`, that it never
exceeds `|d₁| + |d₂|` for `ρ ∈ [-1, 1]` (no *negative* diversification: recognising offset across
buckets never gives more than adding the absolute bucket notionals), and that for `ρ ≥ 0` and both
notionals nonnegative, growing `d₁` never shrinks the aggregate (`effNotionalPair_mono_left`; the
formula is symmetric in `d₁, d₂`, so the same holds for `d₂` by relabelling). The three-bucket
formula itself is not stated here.

## Main definitions

* `saccrEAD`: `α · (RC + PFE)`.
* `effNotionalPair`: the two-bucket interest-rate effective notional `√(d₁² + d₂² + 2ρ·d₁·d₂)`.

## Main results

* `saccrEAD_mono_rc`, `saccrEAD_mono_pfe`: `EAD` is monotone in `RC` and in `PFE` for `α ≥ 0`.
* `effNotionalPair_nonneg`: the aggregated notional is nonnegative.
* `effNotionalPair_eq_abs_add_of_corr_one`: at `ρ = 1`, `effNotionalPair = |d₁ + d₂|`.
* `effNotionalPair_eq_hypot_of_corr_zero`: at `ρ = 0`, `effNotionalPair = √(d₁² + d₂²)`.
* `effNotionalPair_le_abs_add`: for `ρ ∈ [-1, 1]`, the aggregation never exceeds `|d₁| + |d₂|` (no
  negative diversification).
* `effNotionalPair_mono_left`: for `ρ ≥ 0` and `d₂ ≥ 0`, the aggregation is monotone in `d₁` on
  `[0, ∞)`.

## References

* Basel Committee on Banking Supervision, *The standardised approach for measuring counterparty
  credit risk exposures* (BCBS 279), 2014 (the EAD formula and the interest-rate effective
  notional).
* Basel Committee on Banking Supervision, *The Basel Framework*, CRE52 (standardised approach to
  counterparty credit risk), CRE52.57.
-/

@[expose] public section

namespace MathFin

open Real

/-! ## Exposure at default -/

/-- The Basel SA-CCR exposure-at-default formula `EAD = α · (RC + PFE)`, where `RC` is the
replacement cost and `PFE` the potential future exposure add-on. The regulator fixes
`α = 1.4` (`saccrAlpha`), but we keep it as a parameter since the only mathematical content is
the arithmetic combination, not the specific constant. -/
noncomputable def saccrEAD (α RC PFE : ℝ) : ℝ := α * (RC + PFE)

/-- The regulatory value of `α` fixed by Basel SA-CCR (BCBS 279). -/
noncomputable def saccrAlpha : ℝ := 1.4

/-- `saccrAlpha` is positive, so `saccrEAD saccrAlpha` inherits the monotonicity lemmas below at
the regulatory value of `α`. -/
theorem saccrAlpha_pos : 0 < saccrAlpha := by norm_num [saccrAlpha]

/-- `EAD` is monotone increasing in the replacement cost `RC`, for any fixed `α ≥ 0`. -/
theorem saccrEAD_mono_rc {α : ℝ} (hα : 0 ≤ α) {PFE : ℝ} :
    Monotone (fun RC ↦ saccrEAD α RC PFE) := by
  intro RC₁ RC₂ h
  simp only [saccrEAD]
  gcongr

/-- `EAD` is monotone increasing in the PFE add-on, for any fixed `α ≥ 0`. -/
theorem saccrEAD_mono_pfe {α : ℝ} (hα : 0 ≤ α) {RC : ℝ} :
    Monotone (fun PFE ↦ saccrEAD α RC PFE) := by
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

SA-CCR aggregates the signed maturity-bucket effective notionals of an interest-rate hedging set
with correlation `0.7` between adjacent buckets and `0.3` between the first and the third
(CRE52.57; see the module docstring). `effNotionalPair` below is that aggregation when two
buckets are populated, for a general correlation `ρ`. -/

/-- The interest-rate effective notional of a hedging set with two populated maturity buckets of
signed effective notionals `d₁, d₂`: `√(d₁² + d₂² + 2ρ·d₁·d₂)`, with `ρ = 0.7` for adjacent
buckets and `ρ = 0.3` for the first and third (Basel Framework CRE52.57). -/
noncomputable def effNotionalPair (ρ d₁ d₂ : ℝ) : ℝ := √(d₁ ^ 2 + d₂ ^ 2 + 2 * ρ * d₁ * d₂)

theorem effNotionalPair_nonneg (ρ d₁ d₂ : ℝ) : 0 ≤ effNotionalPair ρ d₁ d₂ :=
  Real.sqrt_nonneg _

/-- At full correlation `ρ = 1` the aggregation collapses to `|d₁ + d₂|`: no diversification
benefit, the signed bucket notionals simply add. -/
theorem effNotionalPair_eq_abs_add_of_corr_one (d₁ d₂ : ℝ) :
    effNotionalPair 1 d₁ d₂ = |d₁ + d₂| := by
  unfold effNotionalPair
  rw [show d₁ ^ 2 + d₂ ^ 2 + 2 * 1 * d₁ * d₂ = (d₁ + d₂) ^ 2 by ring]
  exact Real.sqrt_sq_eq_abs _

/-- At zero correlation the aggregation is the Euclidean (independent-risk) combination. -/
theorem effNotionalPair_eq_hypot_of_corr_zero (d₁ d₂ : ℝ) :
    effNotionalPair 0 d₁ d₂ = √(d₁ ^ 2 + d₂ ^ 2) := by
  unfold effNotionalPair; ring_nf

/-- For a correlation `ρ ∈ [-1, 1]` (which contains Basel's `0.7` and `0.3`), the aggregated
notional never exceeds the sum of the absolute bucket notionals: there is no *negative*
diversification from this formula. The bound fails outside `[-1, 1]`, e.g. `ρ = -5`,
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

/-- `effNotionalPair` is monotone in `d₁` on `[0, ∞)`, for `ρ ≥ 0` and `d₂ ≥ 0`: increasing a
nonnegative bucket notional `d₁` never decreases the aggregate when the correlation and the other
notional are both nonnegative. -/
theorem effNotionalPair_mono_left {ρ : ℝ} (hρ : 0 ≤ ρ) {d₂ : ℝ} (hd₂ : 0 ≤ d₂) :
    MonotoneOn (fun d₁ ↦ effNotionalPair ρ d₁ d₂) (Set.Ici (0 : ℝ)) := by
  intro d₁ hd₁ d₁' hd₁' h
  simp only [Set.mem_Ici] at hd₁ hd₁'
  unfold effNotionalPair
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (mul_nonneg hρ hd₂) (sub_nonneg.mpr h), mul_le_mul h h hd₁ (hd₁.trans h)]

end MathFin
