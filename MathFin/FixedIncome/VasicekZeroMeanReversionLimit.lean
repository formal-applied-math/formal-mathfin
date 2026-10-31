/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.FixedIncome.VasicekBondPrice
public import MathFin.FixedIncome.VasicekMarketPriceOfRisk

/-!
# The Vasicek bond price at vanishing mean reversion

`FixedIncome/VasicekBondPrice.lean` prices the zero-coupon bond under the Vasicek short rate,
`P(0,T) = exp(−M(T) + σ²V(T)/2)` (`vasicekBondPrice_eq`), for every `κ > 0`. This file takes
`κ → 0⁺` in that closed form and shows it lands on the bond price of the driftless Gaussian
short rate `r_s = r₀ + σB_s`, which is priced here a second time, directly, with no Vasicek
formula and no limit:

  `exp(−M(T) + σ²V(T)/2) → exp(−r₀T + σ²T³/6) = 𝔼[exp(−∫₀ᵀ (r₀ + σB_s) ds)]`.

Limit algebra on the existing definitions (`vasicekBondB`, `vasicekIntegratedMean`,
`vasicekBondV`, `vasicekBondA`); the only new probability is the second route, one more instance
of the Wiener bond-price lemma `integral_exp_neg_add_mul_wienerIntegralLp`.

## What the formalization forces

* **The variance limit is a cancellation, not a lemma.** `V(T) = T/κ² − 2(1−e^{−κT})/κ³ +
  (1−e^{−2κT})/(2κ³)` is a sum of three terms of order `κ⁻³`; for `T > 0` the middle one alone
  tends to `−∞`. No limit rule applies term by term. `abs_vasicekBondV_sub_le` substitutes the
  cubic Taylor polynomials of `e^{−κT}` and `e^{−2κT}` (from `Real.exp_bound` at `n = 4`), the
  orders `κ⁻³, κ⁻², κ⁻¹` cancel exactly, and what is left is the explicit rate
  `|V(T) − T³/3| ≤ 10·|κ|·T⁴` for `|2κT| ≤ 1`. The limit follows by a squeeze. This is the
  cancellation a small-`a` branch of QuantLib's `Vasicek::A` has to resolve, here with a stated
  error bound.
* **Substitution is not the limit.** Lean's `x / 0 = 0` makes the closed form total at `κ = 0`,
  where it evaluates to `exp(−θT)` (`vasicekBondPrice_closedForm_zero_meanReversion`): the price
  of a rate pinned at the long-run level, independent of `r₀` and `σ`. The limit is
  `exp(−r₀T + σ²T³/6)`, independent of `θ`. A small-`κ` branch must return the limit; any other
  value, including the junk value of the `κ > 0` formula, is a different model.
* **The `λ` sign is a convention, fixed by the measure.** Under this library's Girsanov density
  `exp(−λB_T − λ²T/2)` the risk-adjusted level is `θ − λσ/κ`
  (`vasicekBondPrice_girsanov`), and the `κ → 0⁺` limit of the risk-neutral price is
  `exp(−r₀T + λσT²/2 + σ²T³/6)` (`tendsto_vasicekBondPrice_girsanov_zero_meanReversion`).
  QuantLib's `Vasicek::A` uses the level `b + λσ/a`, so its `λ` is the negative of the one here,
  and its `a → 0` limit `exp(−λσT²/2 + σ²T³/6)` is the same price.

## Scope (disclosed)

* The driftless model is carried, like `vasicekIntegratedRate`, in its Wiener representation
  `∫₀ᵀ r_s ds = r₀T + σ∫₀ᵀ (T − u) dB_u`; the time-order swap `∫₀ᵀ B_s ds = ∫₀ᵀ (T − u) dB_u`
  is the cited modelling bridge, not proved.
* The limits are stated for the closed forms. For each `κ > 0` the closed form is the
  expectation (`vasicekBondPrice_eq`, `vasicekBondPrice_girsanov_eq`); no convergence of the
  random variables `∫₀ᵀ r^κ_s ds` as `κ → 0⁺` is claimed.

## Main results

* `tendsto_vasicekBondB_zero_meanReversion`: `B(T) → T`.
* `abs_vasicekBondV_sub_le`: `|V(T) − T³/3| ≤ 10·|κ|·T⁴` for `κ ≠ 0`, `|2κT| ≤ 1`.
* `tendsto_vasicekBondV_zero_meanReversion`: `V(T) → T³/3`.
* `tendsto_vasicekIntegratedMean_zero_meanReversion`: `M(T) → r₀T`.
* `tendsto_vasicekBondPrice_zero_meanReversion`: `exp(−M(T) + σ²V(T)/2) → exp(−r₀T + σ²T³/6)`.
* `tendsto_vasicekBondA_zero_meanReversion`: QuantLib's `A(t,T)` tends to `exp(σ²T³/6)`.
* `vasicekBondPrice_closedForm_zero_meanReversion`: the `κ = 0` substitution gives `exp(−θT)`.
* `brownianBondPrice_eq`: the driftless model's price `exp(−r₀T + σ²T³/6)`, derived directly.
* `tendsto_vasicekBondPrice_brownianBondPrice`: the two routes agree.
* `tendsto_vasicekBondPrice_girsanov_zero_meanReversion`: with a market price of risk `λ`, the
  limit is `exp(−r₀T + λσT²/2 + σ²T³/6)`.
-/

@[expose] public section

namespace MathFin

open Real Filter Topology

/-- The cubic Taylor polynomial of `exp` with an explicit quartic remainder bound on `|x| ≤ 1`,
from `Real.exp_bound` at `n = 4` (whose constant `5/96` is relaxed to `1`). -/
private lemma abs_exp_sub_cubic_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)| ≤ |x| ^ 4 := by
  have h := Real.exp_bound hx (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  calc |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)| ≤ |x| ^ 4 * (5 / 96) := by
        convert h using 3
    _ ≤ |x| ^ 4 := by nlinarith [pow_nonneg (abs_nonneg x) 4]

/-- The quadratic Taylor polynomial of `exp` with a cubic remainder bound on `|x| ≤ 1`, from
`Real.exp_bound` at `n = 3` (whose constant `2/9` is relaxed to `1`). -/
private lemma abs_exp_sub_quadratic_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  calc |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 * (2 / 9) := by
        convert h using 3
    _ ≤ |x| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg x) 3]

/-- **`B(T) → T` as `κ → 0⁺`.** `B(T) = (1 − e^{−κT})/κ` is the difference quotient at `0` of
`κ ↦ −e^{−κT}`, whose derivative there is `T`. -/
theorem tendsto_vasicekBondB_zero_meanReversion (T : ℝ) :
    Tendsto (fun κ ↦ vasicekBondB κ T) (𝓝[>] 0) (𝓝 T) := by
  have hd : HasDerivAt (fun κ : ℝ ↦ 1 - Real.exp (κ * -T)) T 0 :=
    ((((hasDerivAt_id' (0 : ℝ)).mul_const (-T)).exp).const_sub 1).congr_deriv (by simp)
  refine hd.tendsto_slope_zero_right.congr fun κ ↦ ?_
  simp only [vasicekBondB, zero_add, smul_eq_mul, mul_neg, zero_mul, neg_zero, Real.exp_zero,
    sub_self, sub_zero]
  ring

/-- The quantitative cancellation in `V`: for `κ ≠ 0` with `|2κT| ≤ 1`,
`|V(T) − T³/3| ≤ 10·|κ|·T⁴`. Each of the three terms of `V` is of order `κ⁻³` (the middle one
alone tends to `−∞`); substituting the cubic Taylor polynomials of `e^{−κT}` and `e^{−2κT}`
cancels the `κ⁻³`, `κ⁻²` and `κ⁻¹` orders exactly and leaves `T³/3` plus the quartic
remainders divided by `κ³`. -/
lemma abs_vasicekBondV_sub_le {κ T : ℝ} (hκ : κ ≠ 0) (hsmall : |2 * κ * T| ≤ 1) :
    |vasicekBondV κ T - T ^ 3 / 3| ≤ 10 * |κ| * T ^ 4 := by
  have hx : |κ * T| ≤ 1 / 2 := by
    rw [show 2 * κ * T = 2 * (κ * T) by ring, abs_mul, abs_two] at hsmall
    linarith
  have h1 : |-(κ * T)| ≤ 1 := by rw [abs_neg]; linarith
  have h2 : |-(2 * κ * T)| ≤ 1 := by rwa [abs_neg]
  have hE₁ := abs_exp_sub_cubic_le h1
  have hE₂ := abs_exp_sub_cubic_le h2
  rw [abs_neg] at hE₁ hE₂
  have hid : vasicekBondV κ T - T ^ 3 / 3
      = (4 * (Real.exp (-(κ * T))
            - (1 + -(κ * T) + (-(κ * T)) ^ 2 / 2 + (-(κ * T)) ^ 3 / 6))
          - (Real.exp (-(2 * κ * T))
            - (1 + -(2 * κ * T) + (-(2 * κ * T)) ^ 2 / 2 + (-(2 * κ * T)) ^ 3 / 6)))
        / (2 * κ ^ 3) := by
    simp only [vasicekBondV]
    field_simp
    ring
  have h2abs : |2 * κ * T| ^ 4 = 16 * |κ * T| ^ 4 := by
    rw [show 2 * κ * T = 2 * (κ * T) by ring, abs_mul, abs_two]; ring
  have hT4 : T ^ 4 = |T| ^ 4 := (Even.pow_abs ⟨2, rfl⟩ T).symm
  rw [hid, abs_div, abs_mul, abs_two, abs_pow, div_le_iff₀ (by positivity), hT4]
  calc _ ≤ 4 * |κ * T| ^ 4 + 16 * |κ * T| ^ 4 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        linarith
    _ = 10 * |κ| * |T| ^ 4 * (2 * |κ| ^ 3) := by rw [abs_mul]; ring

/-- A continuous function of `κ` vanishing at `0` tends to `0` along `κ → 0⁺`. -/
private lemma tendsto_nhdsGT_zero_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0) :
    Tendsto f (𝓝[>] 0) (𝓝 0) := by
  simpa [h0] using (hf.tendsto 0).mono_left nhdsWithin_le_nhds

/-- **`V(T) → T³/3` as `κ → 0⁺`** — the genuine three-term cancellation limit. The terms
`T/κ²`, `−2(1 − e^{−κT})/κ³` and `(1 − e^{−2κT})/(2κ³)` of `vasicekBondV` each diverge
(for `T > 0` the middle one tends to `−∞`); only their sum converges, at rate `O(κ)`, by the
explicit bound `abs_vasicekBondV_sub_le` and a squeeze. -/
theorem tendsto_vasicekBondV_zero_meanReversion (T : ℝ) :
    Tendsto (fun κ ↦ vasicekBondV κ T) (𝓝[>] 0) (𝓝 (T ^ 3 / 3)) := by
  have hsmall : ∀ᶠ κ in 𝓝[>] (0 : ℝ), |2 * κ * T| ≤ 1 :=
    (tendsto_nhdsGT_zero_of_continuous (f := fun κ ↦ |2 * κ * T|) (by fun_prop)
      (by simp)).eventually (ge_mem_nhds one_pos)
  have hlin : Tendsto (fun κ : ℝ ↦ 10 * |κ| * T ^ 4) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by simp)
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hlin
  filter_upwards [hsmall, self_mem_nhdsWithin] with κ hs hκ
  rw [Real.norm_eq_abs]
  exact abs_vasicekBondV_sub_le (ne_of_gt hκ) hs

/-- **`M(T) → r₀·T` as `κ → 0⁺`.** With `B(T) → T`, the level term `θ·(T − B(T))` vanishes:
without mean reversion the long-run level `θ` is never felt. -/
theorem tendsto_vasicekIntegratedMean_zero_meanReversion (r₀ θ T : ℝ) :
    Tendsto (fun κ ↦ vasicekIntegratedMean r₀ θ κ T) (𝓝[>] 0) (𝓝 (r₀ * T)) := by
  have hB := tendsto_vasicekBondB_zero_meanReversion T
  simpa [vasicekIntegratedMean] using
    ((tendsto_const_nhds (x := r₀)).mul hB).add
      ((tendsto_const_nhds (x := θ)).mul ((tendsto_const_nhds (x := T)).sub hB))

/-- **The Vasicek bond price at vanishing mean reversion.** The closed form of
`vasicekBondPrice_eq`, `exp(−M(T) + σ²V(T)/2)`, tends as `κ → 0⁺` to `exp(−r₀T + σ²T³/6)` —
the bond price of the driftless Gaussian short rate `r_s = r₀ + σB_s`
(`brownianBondPrice_eq`, derived independently below). -/
theorem tendsto_vasicekBondPrice_zero_meanReversion (r₀ θ σ T : ℝ) :
    Tendsto (fun κ ↦ Real.exp (-(vasicekIntegratedMean r₀ θ κ T) + σ ^ 2 * vasicekBondV κ T / 2))
      (𝓝[>] 0) (𝓝 (Real.exp (-(r₀ * T) + σ ^ 2 * T ^ 3 / 6))) := by
  have h := ((tendsto_vasicekIntegratedMean_zero_meanReversion r₀ θ T).neg.add
    (((tendsto_const_nhds (x := σ ^ 2)).mul
      (tendsto_vasicekBondV_zero_meanReversion T)).div_const 2)).rexp
  convert h using 3
  ring

/-- **QuantLib's `A(t,T)` at vanishing mean reversion.** The `r₀`-independent factor
`vasicekBondA θ σ κ T = exp(−θ(T − B(T)) + σ²V(T)/2)` of the affine price
(`vasicekBondPrice_affine`) tends to `exp(σ²T³/6)`, not to the `κ = 0` substitution value. -/
theorem tendsto_vasicekBondA_zero_meanReversion (θ σ T : ℝ) :
    Tendsto (fun κ ↦ vasicekBondA θ σ κ T) (𝓝[>] 0) (𝓝 (Real.exp (σ ^ 2 * T ^ 3 / 6))) := by
  have hB := tendsto_vasicekBondB_zero_meanReversion T
  have h := (((tendsto_const_nhds (x := θ)).mul ((tendsto_const_nhds (x := T)).sub hB)).neg.add
    (((tendsto_const_nhds (x := σ ^ 2)).mul
      (tendsto_vasicekBondV_zero_meanReversion T)).div_const 2)).rexp
  rw [show σ ^ 2 * T ^ 3 / 6 = -(θ * (T - T)) + σ ^ 2 * (T ^ 3 / 3) / 2 by ring]
  exact h

/-- **The `κ = 0` substitution is not the limit.** Lean's `x / 0 = 0` sends `B(T)` and `V(T)`
to `0` at `κ = 0`, hence `M(T)` to `θ·T`, so the closed form `exp(−M(T) + σ²V(T)/2)` evaluates
to `exp(−θT)` there: the price of a constant rate pinned at the long-run level, independent of
`r₀` and `σ`. The limit `tendsto_vasicekBondPrice_zero_meanReversion` is
`exp(−r₀T + σ²T³/6)`, independent of `θ` instead; the removable singularity at `κ = 0` has to
be filled by the limit, not by substitution. -/
theorem vasicekBondPrice_closedForm_zero_meanReversion (r₀ θ σ T : ℝ) :
    Real.exp (-(vasicekIntegratedMean r₀ θ 0 T) + σ ^ 2 * vasicekBondV 0 T / 2)
      = Real.exp (-(θ * T)) := by
  simp [vasicekIntegratedMean, vasicekBondB, vasicekBondV]

/-! ### The second route: the driftless Gaussian short rate, priced directly -/

section Brownian

open MeasureTheory ProbabilityTheory
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- The integrated kernel of the driftless model `r_s = r₀ + σB_s`, `u ↦ T − u`
(`∫₀ᵀ B_s ds = ∫₀ᵀ (T − u) dB_u`), is in `L²((0, T])`: it lies in `[0, T)` there. -/
lemma brownianIntegratedKernel_memLp (T : ℝ≥0) :
    MemLp (fun u : ℝ ↦ (T : ℝ) - u) 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
  refine (memLp_top_of_bound (by fun_prop) (T : ℝ) ?_).mono_exponent le_top
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ ?_)
  intro s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
  linarith [hs.1]

/-- The driftless integrated kernel `u ↦ T − u` as an element of `L²((0, T])`. -/
noncomputable def brownianIntegratedKernelLp (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  (brownianIntegratedKernel_memLp T).toLp _

/-- `∫₀ᵀ (T − u)² du = T³/3`, for the `L²` element of the driftless kernel. -/
lemma brownianIntegratedKernelLp_integral_sq (T : ℝ≥0) :
    (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (brownianIntegratedKernelLp T u) ^ 2 ∂volume)
      = (T : ℝ) ^ 3 / 3 := by
  refine (brownianIntegratedKernel_memLp T).integral_sq_toLp.trans ?_
  rw [← intervalIntegral.integral_of_le T.coe_nonneg,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ 2)]
  simp [integral_pow]
  norm_num

/-- The **integrated driftless Gaussian short rate** in its Wiener representation:
`∫₀ᵀ (r₀ + σB_s) ds = r₀·T + σ·∫₀ᵀ (T − u) dB_u` — the `κ = 0` model, with the same
time-order-swap modelling bridge as `vasicekIntegratedRate` (cited, not proved). -/
noncomputable def brownianIntegratedRate (hB : IsPreBrownianReal B μ) (r₀ σ : ℝ) (T : ℝ≥0)
    (ω : Ω) : ℝ :=
  r₀ * T + σ * wienerIntegralLp B hB T (brownianIntegratedKernelLp T) ω

/-- **The bond price of the driftless Gaussian short rate**,
`𝔼[exp(−∫₀ᵀ r_s ds)] = exp(−r₀T + σ²T³/6)`: the Wiener bond-price lemma
`integral_exp_neg_add_mul_wienerIntegralLp` at `m = r₀T`, `c = σ` and the kernel `T − u`. No
Vasicek formula and no limit enters. -/
theorem brownianBondPrice_eq (hB : IsPreBrownianReal B μ) (r₀ σ : ℝ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(brownianIntegratedRate hB r₀ σ T ω)) ∂μ
      = Real.exp (-(r₀ * T) + σ ^ 2 * (T : ℝ) ^ 3 / 6) := by
  rw [show (fun ω ↦ Real.exp (-(brownianIntegratedRate hB r₀ σ T ω))) = fun ω ↦
      Real.exp (-(r₀ * T + σ * wienerIntegralLp B hB T (brownianIntegratedKernelLp T) ω)) from rfl,
    integral_exp_neg_add_mul_wienerIntegralLp, brownianIntegratedKernelLp_integral_sq]
  congr 1
  ring

/-- **Two routes to the same price.** The Vasicek closed form (`vasicekBondPrice_eq`, which for
each `κ > 0` is the `μ`-expectation `𝔼[exp(−∫₀ᵀ r^κ_s ds)]`) converges as `κ → 0⁺` to the
expectation of the driftless model, priced independently by `brownianBondPrice_eq`. -/
theorem tendsto_vasicekBondPrice_brownianBondPrice (hB : IsPreBrownianReal B μ)
    (r₀ θ σ : ℝ) (T : ℝ≥0) :
    Tendsto (fun κ ↦ Real.exp (-(vasicekIntegratedMean r₀ θ κ T) + σ ^ 2 * vasicekBondV κ T / 2))
      (𝓝[>] 0) (𝓝 (∫ ω, Real.exp (-(brownianIntegratedRate hB r₀ σ T ω)) ∂μ)) := by
  rw [brownianBondPrice_eq]
  exact tendsto_vasicekBondPrice_zero_meanReversion r₀ θ σ T

end Brownian

/-! ### Stretch: a constant market price of risk `λ` -/

/-- The second-order behaviour of `B`: for `κ ≠ 0` with `|κT| ≤ 1`,
`|(T − B(T))/κ − T²/2| ≤ |κ|·|T|³`. -/
lemma abs_vasicekBondB_secondOrder_sub_le {κ T : ℝ} (hκ : κ ≠ 0) (hsmall : |κ * T| ≤ 1) :
    |(T - vasicekBondB κ T) / κ - T ^ 2 / 2| ≤ |κ| * |T| ^ 3 := by
  have h1 : |-(κ * T)| ≤ 1 := by rwa [abs_neg]
  have hE := abs_exp_sub_quadratic_le h1
  rw [abs_neg] at hE
  have hid : (T - vasicekBondB κ T) / κ - T ^ 2 / 2
      = (Real.exp (-(κ * T)) - (1 + -(κ * T) + (-(κ * T)) ^ 2 / 2)) / κ ^ 2 := by
    simp only [vasicekBondB]
    field_simp
    ring
  rw [hid, abs_div, abs_pow, div_le_iff₀ (by positivity)]
  calc _ ≤ |κ * T| ^ 3 := hE
    _ = |κ| * |T| ^ 3 * |κ| ^ 2 := by rw [abs_mul]; ring

/-- `(T − B(T))/κ → T²/2` as `κ → 0⁺` — the `κ ↓ 0` limit of the mass `∫₀ᵀ g` of the integrated
kernel (`integral_vasicekIntegratedKernel`), which carries the Girsanov mean shift. -/
theorem tendsto_vasicekBondB_secondOrder_zero_meanReversion (T : ℝ) :
    Tendsto (fun κ ↦ (T - vasicekBondB κ T) / κ) (𝓝[>] 0) (𝓝 (T ^ 2 / 2)) := by
  have hsmall : ∀ᶠ κ in 𝓝[>] (0 : ℝ), |κ * T| ≤ 1 :=
    (tendsto_nhdsGT_zero_of_continuous (f := fun κ ↦ |κ * T|) (by fun_prop)
      (by simp)).eventually (ge_mem_nhds one_pos)
  have hlin : Tendsto (fun κ : ℝ ↦ |κ| * |T| ^ 3) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by simp)
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hlin
  filter_upwards [hsmall, self_mem_nhdsWithin] with κ hs hκ
  rw [Real.norm_eq_abs]
  exact abs_vasicekBondB_secondOrder_sub_le (ne_of_gt hκ) hs

section Girsanov

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- The closed form of the Girsanov bond price: `vasicekBondPrice_girsanov` composed with
`vasicekBondPrice_eq` at the risk-adjusted level `θ − λσ/κ`. -/
theorem vasicekBondPrice_girsanov_eq (hB : IsPreBrownianReal B μ) (r₀ θ σ lam : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(vasicekIntegratedRate hB r₀ θ σ hκ T ω))
        ∂(μ.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-lam * B T ω - lam ^ 2 * (T : ℝ) / 2)))
      = Real.exp (-(vasicekIntegratedMean r₀ (θ - lam * σ / κ) κ T)
          + σ ^ 2 * vasicekBondV κ T / 2) := by
  rw [vasicekBondPrice_girsanov, vasicekBondPrice_eq]

/-- **The Girsanov bond price at vanishing mean reversion.** The closed form of
`vasicekBondPrice_girsanov_eq` tends as `κ → 0⁺` to `exp(−r₀T + λσT²/2 + σ²T³/6)`. The level
shift `−λσ/κ` itself diverges, but it multiplies `T − B(T) = O(κ)`: the mean
`M_{θ−λσ/κ}(T) = M_θ(T) − λσ·(T − B(T))/κ` tends to `r₀T − λσT²/2`. The sign of the `λ` term
is fixed by this library's convention: the density `exp(−λB_T − λ²T/2)` makes `B_t + λt` a
Brownian motion, so the risk-adjusted level is `θ − λσ/κ` (lower for `λ > 0`) and the bond is
dearer. -/
theorem tendsto_vasicekBondPrice_girsanov_zero_meanReversion (r₀ θ σ lam T : ℝ) :
    Tendsto (fun κ ↦ Real.exp (-(vasicekIntegratedMean r₀ (θ - lam * σ / κ) κ T)
        + σ ^ 2 * vasicekBondV κ T / 2))
      (𝓝[>] 0) (𝓝 (Real.exp (-(r₀ * T) + lam * σ * T ^ 2 / 2 + σ ^ 2 * T ^ 3 / 6))) := by
  have hM (κ : ℝ) : vasicekIntegratedMean r₀ (θ - lam * σ / κ) κ T
      = vasicekIntegratedMean r₀ θ κ T - lam * σ * ((T - vasicekBondB κ T) / κ) := by
    simp only [vasicekIntegratedMean]; ring
  simp_rw [hM]
  have h := (((tendsto_vasicekIntegratedMean_zero_meanReversion r₀ θ T).sub
    ((tendsto_const_nhds (x := lam * σ)).mul
      (tendsto_vasicekBondB_secondOrder_zero_meanReversion T))).neg.add
    (((tendsto_const_nhds (x := σ ^ 2)).mul
      (tendsto_vasicekBondV_zero_meanReversion T)).div_const 2)).rexp
  convert h using 3
  ring

end Girsanov

end MathFin
