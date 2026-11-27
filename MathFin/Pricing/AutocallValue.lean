/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Pricing.Value
public import MathFin.Contracts.Instruments.Autocall

/-!
# The value of an autocallable note in every model

`Contracts/Instruments/Autocall.lean` writes the autocallable note as a contract at fixed dates and
proves what it pays along each scenario. This file prices it without choosing a model: in any model
`X` with any deflator `D` and measure `Q`, through `Contract.value`.

The note is linear in its notional (`value_autocall`). It is a sum of first-passage payments
(`value_autocallUnit`): a redemption `1 + (k+1) c` weighted by the deflated indicator that `k` is
the first observation at or above the barrier, summed over `k`, plus the protected redemption
weighted by the deflated indicator that none was. The coupon only helps
(`value_autocallUnit_mono_coupon`). And under nonincreasing nonnegative deflation the note is worth
at most the bond that pays the notional and all `n` coupons at the first observation date
(`value_autocallUnit_le`). No model and no dynamics is assumed, and no integrability beyond what
each statement names.

## Main results

* `value_autocall` — the value is `N` times the value per unit of notional.
* `value_autocallUnit` — the first-passage decomposition of the value.
* `value_autocallUnit_mono_coupon` — the value is nondecreasing in the coupon.
* `value_autocallUnit_le` — the value is at most `(1 + n c) P(0, t₀)`.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [S. Bouzoubaa and A. Osseiran, *Exotic Options and Hybrids*][BouzoubaaOsseiran2010], ch. 7

## Tags

autocallable, structured product, first-passage decomposition, model-free pricing, zero curve,
MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Classical

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The value of the note is linear in the notional**, in every model. -/
theorem value_autocall (Q : Measure Ω) (D : ℝ≥0 → Ω → ℝ) (X : ι → ℝ≥0 → Ω → ℝ) (N : ℝ) (i : ι)
    (t : ℕ → ℝ≥0) (n : ℕ) (B c S₀ P : ℝ) (T : ℝ≥0) :
    (autocall N i t n B c S₀ P T).value Q D X = N * (autocallUnit i t n B c S₀ P T).value Q D X :=
  Contract.value_scale Q D X N _

/-- **The first-passage decomposition of the value.** If the deflated first-passage indicators
`D(tⱼ) · 1{j is the first date at or above B}` and the deflated maturity payment are integrable,
the note per unit of notional is worth the sum over `j < n` of `1 + (j+1) c` times the value of the
deflated first-passage indicator at `j`, plus the value of the deflated protected redemption on the
event that no date reached `B`. With `D ≡ 1` the integrals are the probabilities `Q(first passage
at j)`. -/
theorem value_autocallUnit (Q : Measure Ω) (D : ℝ≥0 → Ω → ℝ) (X : ι → ℝ≥0 → Ω → ℝ) (i : ι)
    (t : ℕ → ℝ≥0) (n : ℕ) (B c S₀ P : ℝ) (T : ℝ≥0)
    (hfp : ∀ j < n, Integrable (fun ω ↦
      D (t j) ω * (if (scenarioAt X ω).FirstAbove i t B j then 1 else 0)) Q)
    (hmat : Integrable (fun ω ↦ D T ω * (if ∀ j < n, scenarioAt X ω i (t j) < B then
      (if P ≤ scenarioAt X ω i T then 1 else S₀⁻¹ * scenarioAt X ω i T) else 0)) Q) :
    (autocallUnit i t n B c S₀ P T).value Q D X
      = ∑ j ∈ Finset.range n, (1 + ((j : ℝ) + 1) * c) *
          ∫ ω, D (t j) ω * (if (scenarioAt X ω).FirstAbove i t B j then 1 else 0) ∂Q
        + ∫ ω, D T ω * (if ∀ j < n, scenarioAt X ω i (t j) < B then
            (if P ≤ scenarioAt X ω i T then 1 else S₀⁻¹ * scenarioAt X ω i T) else 0) ∂Q := by
  have e (j : ℕ) (ω : Ω) :
      D (t j) ω * (if (scenarioAt X ω).FirstAbove i t B j then 1 + ((j : ℝ) + 1) * c else 0)
        = (1 + ((j : ℝ) + 1) * c) *
          (D (t j) ω * (if (scenarioAt X ω).FirstAbove i t B j then 1 else 0)) := by
    split_ifs <;> ring
  have hs (j : ℕ) (hj : j ∈ Finset.range n) : Integrable (fun ω ↦ (1 + ((j : ℝ) + 1) * c) *
      (D (t j) ω * (if (scenarioAt X ω).FirstAbove i t B j then 1 else 0))) Q :=
    (hfp j (Finset.mem_range.1 hj)).const_mul _
  simp only [Contract.value, pathPV_autocallUnit, e]
  rw [integral_add (integrable_finsetSum _ hs) hmat, integral_finsetSum _ hs]
  simp only [integral_const_mul]

/-- **The coupon only helps.** If the deflator is nonnegative at the observation dates and the two
present values are integrable, the value of the note is nondecreasing in the coupon. -/
theorem value_autocallUnit_mono_coupon {Q : Measure Ω} {D : ℝ≥0 → Ω → ℝ} (X : ι → ℝ≥0 → Ω → ℝ)
    (i : ι) (t : ℕ → ℝ≥0) (n : ℕ) {B c c' : ℝ} (S₀ P : ℝ) (T : ℝ≥0) (hc : c ≤ c')
    (hD : ∀ j < n, ∀ ω, 0 ≤ D (t j) ω)
    (hint : Integrable (fun ω ↦
      (autocallUnit i t n B c S₀ P T).pathPV (fun u ↦ D u ω) (scenarioAt X ω)) Q)
    (hint' : Integrable (fun ω ↦
      (autocallUnit i t n B c' S₀ P T).pathPV (fun u ↦ D u ω) (scenarioAt X ω)) Q) :
    (autocallUnit i t n B c S₀ P T).value Q D X ≤ (autocallUnit i t n B c' S₀ P T).value Q D X :=
  integral_mono hint hint' fun ω ↦
    pathPV_autocallUnit_mono_coupon _ i t n S₀ P T hc fun j hj ↦ hD j hj ω

/-- **A bond at the first date dominates the note.** If, along every outcome, the deflator is
nonincreasing in time and nonnegative at maturity, the coupon is nonnegative, the initial fixing is
positive and the protection barrier is at most the fixing, and the note's present value and the
deflator `D t₀` are integrable, then the note per unit of notional is worth at most `(1 + n c)
P(0, t₀)`: the zero curve at the first observation date, times the notional and all `n` coupons.
This is the value of a bond, not a sharp bound: it ignores that the note pays once. -/
theorem value_autocallUnit_le {Q : Measure Ω} {D : ℝ≥0 → Ω → ℝ} (X : ι → ℝ≥0 → Ω → ℝ) (i : ι)
    (t : ℕ → ℝ≥0) {n : ℕ} {B c S₀ P : ℝ} {T : ℝ≥0} (hn : 0 < n) (hc : 0 ≤ c) (hS : 0 < S₀)
    (hP : P ≤ S₀) (hD : ∀ ω, Antitone fun u ↦ D u ω) (hDT : ∀ ω, 0 ≤ D T ω)
    (ht : ∀ k < n, t 0 ≤ t k ∧ t k ≤ T)
    (hint : Integrable (fun ω ↦
      (autocallUnit i t n B c S₀ P T).pathPV (fun u ↦ D u ω) (scenarioAt X ω)) Q)
    (hD0 : Integrable (D (t 0)) Q) :
    (autocallUnit i t n B c S₀ P T).value Q D X ≤ (1 + (n : ℝ) * c) * zeroCurve Q D (t 0) := by
  rw [zeroCurve, ← integral_const_mul]
  exact integral_mono hint (hD0.const_mul _) fun ω ↦
    (pathPV_autocallUnit_le (scenarioAt X ω) i t hn hc hS hP (hD ω) (hDT ω) ht).trans_eq
      (mul_comm _ _)

end MathFin.Contracts
