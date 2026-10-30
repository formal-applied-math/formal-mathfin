/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Instruments.FixedIncome
public import MathFin.FixedIncome.HullWhiteCalibration
public import MathFin.FixedIncome.GSRPiecewiseVol

/-!
# Stochastic discounting, and contracts in the Gaussian short-rate models

`Contract.value` discounts by a deterministic `D : ℝ≥0 → ℝ`. In a short-rate model the discount
factor is a random variable at each time, `D t = exp(−∫₀ᵗ r_s ds)`, so a contract is valued along
each outcome by that outcome's discount path: `Contract.valueDisc Q D X c` is the `Q`-expectation
of `c.pathPV (D · ω) (scenarioAt X ω)`. A deterministic `D` is the constant case, definitionally
(`Contract.valueDisc_const`).

A schedule of fixed cash flows sees only the model's zero curve `P(0, t) = 𝔼_Q[D t]`
(`zeroCurve`): its value under the stochastic discount factor is its value on that curve
(`valueDisc_fixedFlows_eq_value`), given each `D tᵢ` integrable. The Gaussian short-rate models
give the curve in closed form, and the integrability comes with it, since a function whose
integral is nonzero is integrable (`valueDisc_fixedFlows_of_zeroCurve_eq`). So a coupon bond is
worth `∑ cᵢ P(0, tᵢ)` with

* Vasicek: `P(0, t) = A(t) e^{−B(t) r₀}` (`valueDisc_fixedFlows_vasicek`, from
  `vasicekBondPrice_affine`);
* Hull–White with continuous forcing `θ`: the same `B`, and `A` carrying `θ`
  (`valueDisc_fixedFlows_hullWhite`, from `HullWhite.bondPrice_affine`);
* two-piece GSR, for payment dates after the volatility switch `T*`:
  `P(0, t) = exp(−M(t) + V(t)/2)` with the GSR variance (`valueDisc_fixedFlows_gsr`, from
  `gsrBondPrice_eq`).

In each, the measure is read as the pricing measure: no change of measure is built, as in the
bond-price theorems the instances consume. Contracts whose cash flows depend on the rate, such as
a floating leg paying the rate it observes, are not covered: valuing one needs the bond prices
`P(t, T)` at `t > 0`, which the library does not have for these models.

## Main definitions

* `Contract.valueDisc` — the value of a contract under a stochastic discount factor.
* `zeroCurve` — the zero curve `t ↦ 𝔼_Q[D t]`.
* `shortRateDiscount` — `D t = exp(−R t)` from an integrated short rate `R`.

## Main results

* `valueDisc_fixedFlows`, `valueDisc_fixedFlows_eq_value`, `valueDisc_fixedFlows_of_zeroCurve_eq`.
* `valueDisc_fixedFlows_vasicek`, `valueDisc_fixedFlows_hullWhite`, `valueDisc_fixedFlows_gsr`.

## Source

The layered separation of contract semantics from pricing semantics, and the
framing "the contract is not the model", are due to Paul Bilokon,
*The Contract Is Not the Model: Proof-Carrying Exotic Derivatives and the
Economics of Model Risk* (working paper, 9 August 2026; Mathematical
Finance, Imperial College London), with code at
<https://github.com/thalesians/lean_contracts> (Apache-2.0). That paper in
turn builds on the compositional contract-DSL of
Peyton Jones, Eber and Seward (2000) and the certified-contract work of Bahr,
Berthold and Elsman (2015) and Annenkov (2018).

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Stochastic discounting -/

/-- The value of a contract under a **stochastic discount factor** `D : ℝ≥0 → Ω → ℝ`: the
`Q`-expectation of its present value along each outcome `ω`, discounted by that outcome's path
`t ↦ D t ω`. -/
noncomputable def Contract.valueDisc (Q : Measure Ω) (D : ℝ≥0 → Ω → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (c : Contract ι) : ℝ :=
  ∫ ω, c.pathPV (fun t ↦ D t ω) (scenarioAt X ω) ∂Q

/-- A deterministic discount factor is the constant case of a stochastic one. -/
@[simp]
theorem Contract.valueDisc_const (Q : Measure Ω) (D : ℝ≥0 → ℝ) (X : ι → ℝ≥0 → Ω → ℝ)
    (c : Contract ι) : c.valueDisc Q (fun t _ ↦ D t) X = c.value Q D X :=
  rfl

/-- The **zero curve** of a stochastic discount factor, `P(0, t) = 𝔼_Q[D t]`: the value of one
unit paid at `t`. -/
noncomputable def zeroCurve (Q : Measure Ω) (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : ℝ :=
  ∫ ω, D t ω ∂Q

/-- **A schedule of fixed cash flows is priced off the zero curve**: under a stochastic discount
factor with each `D tᵢ` integrable, `fixedFlows t c n` is worth `∑ P(0, tᵢ) cᵢ`. -/
theorem valueDisc_fixedFlows {Q : Measure Ω} {D : ℝ≥0 → Ω → ℝ} (X : ι → ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) (hD : ∀ i < n, Integrable (D (t i)) Q) :
    (fixedFlows t c n : Contract ι).valueDisc Q D X
      = ∑ i ∈ Finset.range n, zeroCurve Q D (t i) * c i := by
  simp only [Contract.valueDisc, pathPV_fixedFlows]
  rw [integral_finsetSum _ fun i hi ↦ (hD i (Finset.mem_range.1 hi)).mul_const _]
  simp only [zeroCurve, integral_mul_const]

/-- **The stochastic discount factor reaches a fixed schedule only through its zero curve**: its
value under `D` is its value on the deterministic curve `zeroCurve Q D`, in every model. -/
theorem valueDisc_fixedFlows_eq_value {Q : Measure Ω} [IsProbabilityMeasure Q]
    {D : ℝ≥0 → Ω → ℝ} (X : ι → ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ)
    (hD : ∀ i < n, Integrable (D (t i)) Q) :
    (fixedFlows t c n : Contract ι).valueDisc Q D X
      = (fixedFlows t c n : Contract ι).value Q (zeroCurve Q D) X := by
  rw [valueDisc_fixedFlows X t c n hD, value_fixedFlows]

/-- A closed-form zero curve prices a fixed schedule: if `𝔼_Q[D tᵢ] = P(tᵢ) ≠ 0` at each payment
date, the schedule is worth `∑ P(tᵢ) cᵢ`. Integrability is not assumed: a function whose integral
is nonzero is integrable. -/
theorem valueDisc_fixedFlows_of_zeroCurve_eq {Q : Measure Ω} {D : ℝ≥0 → Ω → ℝ}
    (X : ι → ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) {P : ℝ≥0 → ℝ}
    (hP : ∀ i < n, zeroCurve Q D (t i) = P (t i)) (hP0 : ∀ i < n, P (t i) ≠ 0) :
    (fixedFlows t c n : Contract ι).valueDisc Q D X = ∑ i ∈ Finset.range n, P (t i) * c i := by
  rw [valueDisc_fixedFlows X t c n fun i hi ↦
    Integrable.of_integral_ne_zero ((hP i hi).trans_ne (hP0 i hi))]
  exact Finset.sum_congr rfl fun i hi ↦ by rw [hP i (Finset.mem_range.1 hi)]

/-- The discount factor of a short-rate model, `D t = exp(−R t)`, from its integrated short rate
`R t = ∫₀ᵗ r_s ds`. -/
noncomputable def shortRateDiscount (R : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ Real.exp (-R t ω)

/-! ### The Gaussian short-rate models -/

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- **A coupon bond in the Vasicek model**: discounted by `exp(−∫₀ᵗ r)` along the Vasicek short
rate from `r₀`, the schedule paying `cᵢ` at `tᵢ` is worth `∑ A(tᵢ) e^{−B(tᵢ) r₀} cᵢ`, the
affine bond prices of `vasicekBondPrice_affine`, with `μ` read as the pricing measure. -/
theorem valueDisc_fixedFlows_vasicek (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (X : ι → ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) :
    (fixedFlows t c n : Contract ι).valueDisc μ
        (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) X
      = ∑ i ∈ Finset.range n,
          vasicekBondA θ σ κ (t i) * Real.exp (-(vasicekBondB κ (t i) * r₀)) * c i :=
  valueDisc_fixedFlows_of_zeroCurve_eq (P := fun s ↦
      vasicekBondA θ σ κ s * Real.exp (-(vasicekBondB κ s * r₀))) X t c n
    (fun i _ ↦ vasicekBondPrice_affine hB r₀ θ σ hκ (t i))
    fun _ _ ↦ (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne'

/-- **A coupon bond in the Hull–White model**: for continuous forcing `θ`, the schedule paying
`cᵢ` at `tᵢ` is worth `∑ A(tᵢ) e^{−B(tᵢ) r₀} cᵢ`, with Vasicek's `B` and `A = HullWhite.bondA`
carrying `θ` (`HullWhite.bondPrice_affine`), with `μ` read as the pricing measure. -/
theorem valueDisc_fixedFlows_hullWhite (hB : IsPreBrownianReal B μ) {θ : ℝ → ℝ}
    (hθ : Continuous θ) (κ σ r₀ : ℝ) (hκ : 0 < κ) (X : ι → ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (c : ℕ → ℝ) (n : ℕ) :
    (fixedFlows t c n : Contract ι).valueDisc μ
        (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) X
      = ∑ i ∈ Finset.range n,
          HullWhite.bondA θ σ κ (t i) * Real.exp (-(vasicekBondB κ (t i) * r₀)) * c i :=
  valueDisc_fixedFlows_of_zeroCurve_eq (P := fun s ↦
      HullWhite.bondA θ σ κ s * Real.exp (-(vasicekBondB κ s * r₀))) X t c n
    (fun i _ ↦ HullWhite.bondPrice_affine hB θ κ σ r₀ hθ hκ (t i))
    fun _ _ ↦ (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne'

/-- **A coupon bond in the two-piece GSR model**: with volatility `σ₁` before `T*` and `σ₂`
after, the schedule paying `cᵢ` at dates `tᵢ ≥ T*` is worth `∑ exp(−M(tᵢ) + V(tᵢ)/2) cᵢ`, with
`M` the Vasicek integrated mean and `V = gsrBondV` (`gsrBondPrice_eq`), with `μ` read as the
pricing measure. -/
theorem valueDisc_fixedFlows_gsr (hB : IsPreBrownianReal B μ) (r₀ θ σ1 σ2 : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (Tstar : ℝ≥0) (X : ι → ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ)
    (ht : ∀ i < n, Tstar ≤ t i) :
    (fixedFlows t c n : Contract ι).valueDisc μ
        (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) X
      = ∑ i ∈ Finset.range n, Real.exp (-(vasicekIntegratedMean r₀ θ κ (t i))
          + gsrBondV κ σ1 σ2 (Tstar : ℝ) (t i) / 2) * c i :=
  valueDisc_fixedFlows_of_zeroCurve_eq (P := fun s ↦ Real.exp (-(vasicekIntegratedMean r₀ θ κ s)
      + gsrBondV κ σ1 σ2 (Tstar : ℝ) s / 2)) X t c n
    (fun i hi ↦ gsrBondPrice_eq hB r₀ θ σ1 σ2 hκ Tstar (t i) (ht i hi))
    fun _ _ ↦ (Real.exp_pos _).ne'

end MathFin.Contracts
