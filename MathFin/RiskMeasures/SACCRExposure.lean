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

The other SA-CCR building block with actual algebraic content is Annex 4's **add-on**
aggregation, which combines the per-trade *effective notionals* `Dₖ` of a hedging set into a
single asset-class add-on via a single-systematic-factor correlation `ρ`:

  `AddOn = √((Σₖ ρₖ · Dₖ)² + Σₖ (1 − ρₖ²) · Dₖ²)`

(expanding this for two trades with equal supervisory correlation `ρ` gives a cross term in `ρ²`,
not `ρ`: `√(D₁² + D₂² + 2ρ²·D₁·D₂)`). We instead formalise the structurally analogous two-trade
building block with a *linear* correlation cross term, calling it `effNotionalPair` since it
takes the same per-trade effective notionals as input (Basel's own term for the add-on formula's
output would be "add-on", not "effective notional" — the formalised quantity below is named after
its inputs, not after the Basel output it does not reproduce):

  `EffNotional ρ d₁ d₂ = √(d₁² + d₂² + 2ρ·d₁·d₂)`,

the same quadratic-form combination as the variance of a sum of two correlated random variables —
useful on its own merits (it is this shape, not the Annex-4 one, that the diversification bounds
below are about), but not a literal algebraic specialisation of the Annex-4 formula above. We
prove it collapses to
`|d₁ + d₂|` at `ρ = 1` (full correlation, no diversification benefit) and to `√(d₁² + d₂²)` at
`ρ = 0` (independent add-ons), that it never exceeds `|d₁| + |d₂|` for `ρ ∈ [-1, 1]` (no *negative*
diversification), and that for `ρ ≥ 0` and both notionals nonnegative, growing `d₁`'s magnitude
never shrinks the aggregate (`effNotionalPair_mono_left`; the formula is symmetric in `d₁, d₂`, so
the same holds for `d₂` by relabelling).

## Main definitions

* `saccrEAD`: `α · (RC + PFE)`.
* `effNotionalPair`: the two-trade correlated aggregation `√(d₁² + d₂² + 2ρ·d₁·d₂)`.

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
  credit risk exposures* (BCBS 279), 2014 (the EAD formula, and the Annex 4 add-on aggregation).
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

SA-CCR's Annex 4 combines the per-trade effective notionals of a hedging set into an add-on using
a supervisory correlation parameter `ρ`, with a cross term quadratic in `ρ` (see the module
docstring). `effNotionalPair` below is the structurally analogous *two-trade, linear-in-`ρ`*
building block — not a literal specialisation of the Annex-4 formula, as the module docstring
explains — chosen because it is the shape the diversification bounds in this file are about
(identical to the variance of a sum of two correlated random variables). -/

/-- The two-trade correlated aggregation of effective notionals `d₁, d₂`, with a correlation `ρ`
cross term linear in `ρ`: `√(d₁² + d₂² + 2ρ·d₁·d₂)`. Structurally analogous to, but not a literal
specialisation of, the BCBS 279 Annex 4 add-on formula (see the module docstring). -/
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

/-- `effNotionalPair` is monotone in `d₁` on `[0, ∞)`, for `ρ ≥ 0` and `d₂ ≥ 0`: increasing a
nonnegative trade notional `d₁` never decreases the aggregate when the correlation and the other
notional are both nonnegative. -/
theorem effNotionalPair_mono_left {ρ : ℝ} (hρ : 0 ≤ ρ) {d₂ : ℝ} (hd₂ : 0 ≤ d₂) :
    MonotoneOn (fun d₁ => effNotionalPair ρ d₁ d₂) (Set.Ici (0 : ℝ)) := by
  intro d₁ hd₁ d₁' hd₁' h
  simp only [Set.mem_Ici] at hd₁ hd₁'
  unfold effNotionalPair
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (mul_nonneg hρ hd₂) (sub_nonneg.mpr h), mul_le_mul h h hd₁ (hd₁.trans h)]

end MathFin
