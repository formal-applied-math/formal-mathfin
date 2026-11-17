/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.Rates.NelsonSiegelSvensson

/-!
# The Nelson–Siegel loading at vanishing decay

`Models/Rates/NelsonSiegelSvensson.lean` defines the Nelson–Siegel–Svensson curve through the
slope factor `s(x) = (1 − e^{−x})/x` (`nssSlope`), and `Models/Rates/VasicekYieldNelsonSiegel.lean`
reads the Vasicek zero yield in the same factors. This file takes the decay rate `κ` (the
reciprocal `1/l` of Svensson's decay constant; `κ → 0⁺` is `l → ∞`, the flat-`c₀ + c₁`
degeneration) `κ → 0⁺` at a fixed maturity `τ ≠ 0` in the decay-parameterized loading
`s(κτ) = (1 − e^{−κτ})/(κτ)`:

  `(1 − e^{−κτ})/(κτ) → 1`, so the Nelson–Siegel zero rate
  `c₀ + c₁·s(κτ) + c₂·(s(κτ) − e^{−κτ})` tends to `c₀ + c₁`, and the Svensson second loading
  term `c₃·(s(κτ) − e^{−κτ})` tends to `0`.

## What the formalization forces

* **Substitution is not the limit.** Lean's `x / 0 = 0` sends the loading to `0` at `κ = 0`
  (numerator `1 − e^0 = 0`, junk denominator), so the zero rate evaluates to `c₀ − c₂` there and
  the second loading term to `−c₃`: values of a different model. The limits are `c₀ + c₁` and
  `0`. A small-`κ` branch must return the limits; any other value, including the junk value of
  the `κ > 0` expression, is a different model.
* **The defect species.** A small-`κ` guard that keeps the denominator away from its true zero
  while the numerator keeps its exact value evaluates the loading to `0` at `κ = 0` — the
  numerator `1 − exp(−0·τ) = 0` over a tiny denominator — a different value than the limit `1`.
  This is the same species as the hardcoded-to-0 guard of QuantLib's `Vasicek::A`
  (`vasicek.cpp`, PR #2599); the limits proved here are the values a correct
  small-`κ` branch has to reach.

## Scope (disclosed)

* The limits are stated for the closed-form loading with the coefficients `cᵢ` and the maturity
  `τ` held fixed (`τ ≠ 0`); no claim is made about a fitted curve (the coefficients are not
  re-estimated as `κ → 0`), and the `τ = 0` short end — the limit in the *maturity* direction —
  is `Models/Rates/NelsonSiegelSvensson.lean`'s `tendsto_nssYield_nhdsNE_zero`, not anything
  here.
* The epsilon-guard behaviour is described as the motivating defect species only; no engine is
  formalized here; the limits are stated as the values any correct small-`κ` branch must reach.

## Main definitions

* `nelsonSiegelZeroRate`: the Nelson–Siegel zero rate in the decay-parameter form
  `c₀ + c₁·s(κτ) + c₂·(s(κτ) − e^{−κτ})`.

## Main results

* `tendsto_oneMinusExpOverX_zero_meanReversion`: the loading `(1 − e^{−κτ})/(κτ) → 1` as
  `κ → 0⁺`, at fixed `τ ≠ 0`.
* `tendsto_exp_neg_mul_zero_meanReversion`: `e^{−κτ} → 1` as `κ → 0⁺`.
* `tendsto_nelsonSiegelZeroRate_zero_meanReversion`: the Nelson–Siegel zero rate tends to
  `c₀ + c₁` as `κ → 0⁺`.
* `nelsonSiegelZeroRate_closedForm_zero_meanReversion`: the `κ = 0` substitution gives
  `c₀ − c₂`, where the limit is `c₀ + c₁`.
* `tendsto_svenssonSecondLoading_zero_meanReversion`: the Svensson second loading term
  `c₃·(s(κτ) − e^{−κτ})` tends to `0` as `κ → 0⁺`.
* `svenssonSecondLoading_closedForm_zero_meanReversion`: the `κ = 0` substitution gives `−c₃`,
  where the limit is `0`.

## References

* [C. R. Nelson, A. F. Siegel, *Parsimonious Modeling of Yield Curves*][NelsonSiegel1987]
* [L. E. O. Svensson, *Estimating and Interpreting Forward Interest Rates: Sweden
  1992–1994*][Svensson1994]
* [The QuantLib contributors, *QuantLib*][QuantLib], Vasicek::A (vasicek.cpp, PR #2599)

## Tags

Nelson–Siegel, Svensson, vanishing decay, loading factor, zero rate, guarded limit,
removable singularity, MSC 91G30, JEL E43
-/

@[expose] public section

namespace MathFin

open Filter Topology

/-- `exp(−κ·τ) → 1` as `κ → 0⁺`, at a fixed maturity `τ` — the exponential building block of
the two composite vanishing-decay limits below (the zero rate and the Svensson second
loading term). -/
theorem tendsto_exp_neg_mul_zero_meanReversion (t : ℝ) :
    Tendsto (fun κ : ℝ ↦ Real.exp (-(κ * t))) (𝓝[>] 0) (𝓝 1) :=
  ((Real.continuous_exp.comp (continuous_id.mul continuous_const).neg).tendsto' 0 1
    (by simp)).mono_left nhdsWithin_le_nhds

/-- **The Nelson–Siegel loading at vanishing decay**: `(1 − e^{−κτ})/(κτ) → 1` as `κ → 0⁺`, at a
fixed maturity `τ ≠ 0`. Derived by transporting the repo's own `nssSlope` limit
(`tendsto_nssSlope_nhdsNE_zero`, `Models/Rates/NelsonSiegelSvensson.lean`) along
`κ ↦ κ·τ` — no parallel loading analysis. -/
theorem tendsto_oneMinusExpOverX_zero_meanReversion (t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun κ ↦ (1 - Real.exp (-(κ * t))) / (κ * t)) (𝓝[>] 0) (𝓝 1) := by
  have hcomp : Tendsto (fun κ : ℝ ↦ κ * t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    simpa using tendsto_div_const_nhdsNE_zero (inv_ne_zero ht)
  exact (tendsto_nssSlope_nhdsNE_zero.comp hcomp).mono_left (nhdsGT_le_nhdsNE 0)

/-- The **Nelson–Siegel zero rate** in the decay-parameter form, with the loading written
through the library's slope factor (`nssSlope`, `Models/Rates/NelsonSiegelSvensson.lean`):
`c₀ + c₁·s(κτ) + c₂·(s(κτ) − e^{−κτ})`. For `κ ≠ 0` this is the specialization
`nssYield c0 c1 c2 0 κ⁻¹ 0 t` of the library's decay-constant form — the plain three-factor
Nelson–Siegel curve as a function of the decay `κ` at a fixed maturity `τ`; the Svensson
extension adds one more term of the same second-loading shape
(see `tendsto_svenssonSecondLoading_zero_meanReversion`). -/
noncomputable def nelsonSiegelZeroRate (c0 c1 c2 κ t : ℝ) : ℝ :=
  c0 + c1 * nssSlope (κ * t)
    + c2 * (nssSlope (κ * t) - Real.exp (-(κ * t)))

/-- **The Nelson–Siegel zero rate at vanishing decay**: it tends to `c₀ + c₁` as `κ → 0⁺`, at a
fixed maturity `τ ≠ 0`. The slope loading `s(κτ)` tends to `1`
(`tendsto_oneMinusExpOverX_zero_meanReversion`) while `e^{−κτ}` tends to `1`, so the curvature
term `c₂·(s(κτ) − e^{−κτ})` vanishes and only level plus slope survive. This limit is the value
a correct small-`κ` branch of the zero rate has to reach. -/
theorem tendsto_nelsonSiegelZeroRate_zero_meanReversion (c0 c1 c2 t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun κ ↦ nelsonSiegelZeroRate c0 c1 c2 κ t) (𝓝[>] 0) (𝓝 (c0 + c1)) := by
  have hL := tendsto_oneMinusExpOverX_zero_meanReversion t ht
  have hE := tendsto_exp_neg_mul_zero_meanReversion t
  have h : Tendsto (fun κ ↦ nelsonSiegelZeroRate c0 c1 c2 κ t) (𝓝[>] 0)
      (𝓝 (c0 + c1 * 1 + c2 * (1 - 1))) := by
    refine ((tendsto_const_nhds.add (hL.const_mul c1)).add
      ((hL.sub hE).const_mul c2)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with κ _
    simp only [nelsonSiegelZeroRate, nssSlope]
  simpa using h

/-- **The `κ = 0` substitution is not the limit.** Lean's `x / 0 = 0` sends the loading
`s(κτ)` to `0` at `κ = 0` (numerator `1 − e^0 = 0`, junk denominator), so the zero rate
evaluates to `c₀ − c₂` there — the `κ = 0` junk value, independent of `c₁`; the limit
`tendsto_nelsonSiegelZeroRate_zero_meanReversion` is `c₀ + c₁` instead: the removable
singularity at `κ = 0` has to be filled by the limit, not by substitution. -/
theorem nelsonSiegelZeroRate_closedForm_zero_meanReversion (c0 c1 c2 t : ℝ) :
    nelsonSiegelZeroRate c0 c1 c2 0 t = c0 - c2 := by
  simp [nelsonSiegelZeroRate, nssSlope, sub_eq_add_neg]

/-- **The Svensson second loading term at vanishing decay**: `c₃·(s(κτ) − e^{−κτ}) → 0` as
`κ → 0⁺`, at a fixed maturity `τ ≠ 0` — the slope loading tends to `1` while `e^{−κτ}` tends to
`1`, so their difference cancels. This is the value a correct small-`κ` branch of the second
loading has to reach at `κ = 0`: `0`, not the substituted value `−c₃`
(`svenssonSecondLoading_closedForm_zero_meanReversion`), whatever the coefficient `c₃`. -/
theorem tendsto_svenssonSecondLoading_zero_meanReversion (c3 t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun κ ↦ c3 * (nssSlope (κ * t) - Real.exp (-(κ * t)))) (𝓝[>] 0) (𝓝 0) := by
  have hL := tendsto_oneMinusExpOverX_zero_meanReversion t ht
  have hE := tendsto_exp_neg_mul_zero_meanReversion t
  have h : Tendsto (fun κ ↦ c3 * (nssSlope (κ * t) - Real.exp (-(κ * t)))) (𝓝[>] 0)
      (𝓝 (c3 * (1 - 1))) := by
    refine ((hL.sub hE).const_mul c3).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with κ _
    simp only [nssSlope]
  simpa using h

/-- **The `κ = 0` substitution is not the limit** for the second loading term: Lean's `x / 0 = 0`
sends `s(κτ)` to `0` at `κ = 0`, so the term evaluates to `−c₃` there — a different value than
the limit `0` (`tendsto_svenssonSecondLoading_zero_meanReversion`). -/
theorem svenssonSecondLoading_closedForm_zero_meanReversion (c3 t : ℝ) :
    c3 * (nssSlope ((0 : ℝ) * t) - Real.exp (-((0 : ℝ) * t))) = -c3 := by
  simp [nssSlope, sub_eq_add_neg]

end MathFin
