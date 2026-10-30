/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.LevyQuadraticSums
public import MathFin.Foundations.ExpMartingaleQBrownian

/-!
# The exponential martingale of a martingale whose bracket is `t`

The analytic core of the elementary route to Lévy's characterisation (issue #179). Let `M` be a
bounded (`|M| ≤ K`) real process with every path continuous, such that `M` and `M² − t` are
`Martingale`s for `𝓕`. Then for every real `a`,

  `t ↦ exp(a·M_t − a²t/2)` is a martingale              (`martingale_exp`),

and so `M` meets the library's exponential-martingale characterisation data
`IsExpQMartingale P 𝓕 M T` as soon as it starts at `0` (`isExpQMartingale`). From there
`isQBrownianMotion_of_expMartingale` (`ExpMartingaleQBrownian`) delivers `N(0, t − s)`
increments and independent increments: `M` is a Brownian motion in law.

No quadratic-variation process and no stochastic integral against `M` is used; this matters at
the pin, where BrownianMotion's general Doob–Meyer decomposition is `sorry`.

## The argument: Itô's formula for `exp(a·x − a²r/2)`, one cell at a time

Write `Zᵣ = exp(a·Mᵣ − a²r/2)` and fix a bounded `𝓕_s`-measurable `V`. Along the uniform
partition `s = t₀ ≤ ⋯ ≤ tₙ = t`, telescope `V·(Z_t − Z_s) = ∑ₖ V·Z_{tₖ}·(e^{aΔₖ − c} − 1)`,
with `Δₖ = M_{tₖ₊₁} − M_{tₖ}` and `c = a²(t − s)/(2n)`. On one cell, with `W = V·Z_{tₖ}` bounded
and `𝓕_{tₖ}`-measurable, expand `e^{aΔ} = 1 + aΔ + a²Δ²/2 + R(aΔ)`:

  `E[W·(e^{aΔ−c} − 1)] = e^{−c}·E[W·R(aΔ)] + ((1 + c)e^{−c} − 1)·E[W]`,

because `E[W·Δ] = 0` and `E[W·(Δ² − Δt)] = 0` (`LevyQuadraticSums`: the martingale property of
`M` and of `M² − t`) and `c = a²Δt/2` — the second-order term cancels *exactly*, the
probabilistic form of `∂ᵣ + ½∂ₓₓ = 0`. The Taylor remainder is `|R(x)| ≤ |x|³e^{|x|}`
(`abs_exp_sub_taylor_two_le`), and `|(1 + c)e^{−c} − 1| ≤ c²`
(`abs_one_add_mul_exp_neg_sub_one_le`). Summing over the cells,

  `|E[V·Z_t] − E[V·Z_s]| ≤ C·e^{|a|K}·(|a|³e^{2|a|K}·∑ₖ E|Δₖ|³ + (a²(t − s)/2)²/n)`,

and the cubic sums vanish (`LevyQuadraticSums.tendsto_sum_integral_abs_cube`). So the
conditional moment-generating function is propagated cell by cell, and the cubic sums are the
only global input — no ODE for `φ(t) = E[1_A e^{a(M_t − M_s)}]` has to be solved.

## Main results

* `abs_integral_mul_exp_increment_sub_le` — the one-cell estimate.
* `integral_mul_exp_eq` — `E[V·Z_t] = E[V·Z_s]` for bounded `𝓕_s`-measurable `V`.
* `setIntegral_exp_eq` — the set-integral form over `A ∈ 𝓕_s`, as `IsExpQMartingale` states it.
* `martingale_exp` — `t ↦ exp(a·M_t − a²t/2)` is a Mathlib `Martingale`.
* `isExpQMartingale` — `M` (started at `0`) satisfies `IsExpQMartingale P 𝓕 M T` for every `T`.

## Scope

`M` is **bounded** and **every** path is continuous. Extending to continuous local martingales
with `M² − t` a local martingale needs a localisation step that is not here. The conclusion that
`M` is a Brownian motion is `isQBrownianMotion_of_expMartingale` applied to `isExpQMartingale`. It
gives the law on `[0, T]`, not independence of `M_t − M_s` from `𝓕_s`.
-/

@[expose] public section

namespace MathFin
namespace LevyExpMartingale

open MeasureTheory ProbabilityTheory Filter Topology Set Finset LevyQuadraticSums
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### Two scalar estimates -/

/-- The second-order Taylor remainder of `exp`: `|eˣ − (1 + x + x²/2)| ≤ |x|³e^{|x|}`. It is the
real case of `Complex.norm_exp_sub_sum_le_norm_mul_exp`. -/
theorem abs_exp_sub_taylor_two_le (x : ℝ) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 3
  have e : Complex.exp x - ∑ m ∈ range 3, (x : ℂ) ^ m / m.factorial
      = ((Real.exp x - (1 + x + x ^ 2 / 2) : ℝ) : ℂ) := by
    simp [sum_range_succ, Complex.ofReal_exp]
  rw [e] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

/-- `|(1 + c)e^{−c} − 1| ≤ c²` for `c ≥ 0`: the mismatch between the drift `e^{−c}` and its
first-order compensation `1 + c`. Both sides of `1 − c² ≤ (1 + c)e^{−c} ≤ 1` are
`1 + x ≤ eˣ`. -/
theorem abs_one_add_mul_exp_neg_sub_one_le {c : ℝ} (hc : 0 ≤ c) :
    |(1 + c) * Real.exp (-c) - 1| ≤ c ^ 2 := by
  have h1 := Real.add_one_le_exp c
  have h2 := Real.add_one_le_exp (-c)
  have he : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-c)
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 + c)]
  · nlinarith [mul_le_mul_of_nonneg_right h1 hpos.le]

variable [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {K : ℝ}

/-- A bounded process has `exp(a·M_r − a²r/2) ≤ e^{|a|K}`. -/
theorem exp_le_exp_abs_mul (hK : ∀ t ω, |M t ω| ≤ K) (a : ℝ) (r : ℝ≥0) (ω : Ω) :
    Real.exp (a * M r ω - a ^ 2 * (r : ℝ) / 2) ≤ Real.exp (|a| * K) := by
  refine Real.exp_le_exp.2 ?_
  have h1 : a * M r ω ≤ |a| * K := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK r ω) (abs_nonneg a))
  have h2 : 0 ≤ a ^ 2 * (r : ℝ) / 2 := by positivity
  linarith

/-! ### One cell -/

/-- **The one-cell estimate.** For `p ≤ q` and a bounded (`|W| ≤ C`) `𝓕_p`-measurable `W`,

  `|E[W·(e^{a(M_q − M_p) − c} − 1)]| ≤ C·(|a|³e^{2|a|K}·E|M_q − M_p|³ + c²)`,
  `c = a²(q − p)/2`.

Expanding `e^{aΔ}` to second order, the first-order term `E[W·Δ]` and the second-order term
`E[W·(Δ² − (q − p))]` vanish (`integral_mul_increment_eq_zero`,
`integral_mul_sq_increment_sub`), which leaves the Taylor remainder and `((1 + c)e^{−c} − 1)·E[W]`. -/
theorem abs_integral_mul_exp_increment_sub_le (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P) (hK : ∀ t ω, |M t ω| ≤ K) (a : ℝ)
    {p q : ℝ≥0} (hpq : p ≤ q) {W : Ω → ℝ} (hW : StronglyMeasurable[𝓕 p] W) {C : ℝ}
    (hC : ∀ ω, |W ω| ≤ C) :
    |∫ ω, W ω * (Real.exp (a * (M q ω - M p ω) - a ^ 2 * ((q : ℝ) - p) / 2) - 1) ∂P|
      ≤ C * (|a| ^ 3 * Real.exp (2 * |a| * K) * ∫ ω, |M q ω - M p ω| ^ 3 ∂P
        + (a ^ 2 * ((q : ℝ) - p) / 2) ^ 2) := by
  set c : ℝ := a ^ 2 * ((q : ℝ) - p) / 2 with hc
  have hc0 : 0 ≤ c := by
    have : (p : ℝ) ≤ q := hpq
    rw [hc]; have := sub_nonneg.2 this; positivity
  set κ : ℝ := |a| ^ 3 * Real.exp (2 * |a| * K)
  have hMm (t : ℝ≥0) : Measurable (M t) := ((hM.stronglyAdapted t).mono (𝓕.le t)).measurable
  have hWm : Measurable W := (hW.mono (𝓕.le p)).measurable
  have hΔm : Measurable fun ω ↦ M q ω - M p ω := (hMm q).sub (hMm p)
  have hΔb (ω : Ω) := abs_sub_le_two_mul hK p q ω
  -- the Taylor remainder
  have hRb (ω : Ω) : |Real.exp (a * (M q ω - M p ω)) - (1 + a * (M q ω - M p ω)
      + (a * (M q ω - M p ω)) ^ 2 / 2)| ≤ κ * |M q ω - M p ω| ^ 3 := by
    refine (abs_exp_sub_taylor_two_le _).trans ?_
    rw [abs_mul, mul_pow, mul_comm (|a| ^ 3), mul_assoc, mul_comm κ]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    nlinarith [abs_nonneg a, hΔb ω]
  have iW : Integrable W P :=
    (memLp_of_abs_le hWm.aestronglyMeasurable hC 1).integrable le_rfl
  have iCube : Integrable (fun ω ↦ |M q ω - M p ω| ^ 3) P :=
    (memLp_of_abs_le (hΔm.abs.pow_const 3).aestronglyMeasurable (C := (2 * K) ^ 3) (fun ω ↦ by
      rw [abs_pow, abs_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hΔb ω) 3) 1).integrable le_rfl
  have iR : Integrable (fun ω ↦ Real.exp (a * (M q ω - M p ω)) - (1 + a * (M q ω - M p ω)
      + (a * (M q ω - M p ω)) ^ 2 / 2)) P :=
    (memLp_of_abs_le (by fun_prop) (C := κ * (2 * K) ^ 3) (fun ω ↦ (hRb ω).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hΔb ω) 3)
        (by positivity))) 1).integrable le_rfl
  have iWR := iR.bdd_mul hWm.aestronglyMeasurable (.of_forall hC)
  have iWΔ := ((memLp_of_abs_le (P := P) hΔm.aestronglyMeasurable hΔb 1).integrable le_rfl).bdd_mul
    hWm.aestronglyMeasurable (.of_forall hC)
  have iWY := ((memLp_sq_increment_sub hM hK p q ((q : ℝ) - p) 1).integrable le_rfl).bdd_mul
    hWm.aestronglyMeasurable (.of_forall hC)
  have h1 := integral_mul_increment_eq_zero hM hpq hW hC
  have h2 := integral_mul_sq_increment_sub hM hM2 hK hpq hW hC
  -- the split: remainder, drift mismatch, and the two martingale terms
  have hsplit : ∫ ω, W ω * (Real.exp (a * (M q ω - M p ω) - c) - 1) ∂P
      = Real.exp (-c) * ∫ ω, W ω * (Real.exp (a * (M q ω - M p ω)) - (1 + a * (M q ω - M p ω)
          + (a * (M q ω - M p ω)) ^ 2 / 2)) ∂P
        + ((1 + c) * Real.exp (-c) - 1) * ∫ ω, W ω ∂P := by
    have h0 : ∫ ω, (a * (W ω * (M q ω - M p ω))
        + a ^ 2 / 2 * (W ω * ((M q ω - M p ω) ^ 2 - ((q : ℝ) - p)))) ∂P = 0 := by
      rw [integral_add (iWΔ.const_mul a) (iWY.const_mul _), integral_const_mul,
        integral_const_mul, h1, h2]
      ring
    have iA : Integrable (fun ω ↦ Real.exp (-c) * (W ω * (Real.exp (a * (M q ω - M p ω))
        - (1 + a * (M q ω - M p ω) + (a * (M q ω - M p ω)) ^ 2 / 2)))) P := iWR.const_mul _
    have iB : Integrable (fun ω ↦ ((1 + c) * Real.exp (-c) - 1) * W ω) P := iW.const_mul _
    have iAB : Integrable (fun ω ↦ Real.exp (-c) * (W ω * (Real.exp (a * (M q ω - M p ω))
        - (1 + a * (M q ω - M p ω) + (a * (M q ω - M p ω)) ^ 2 / 2)))
        + ((1 + c) * Real.exp (-c) - 1) * W ω) P := iA.add iB
    have iG : Integrable (fun ω ↦ Real.exp (-c) * (a * (W ω * (M q ω - M p ω))
        + a ^ 2 / 2 * (W ω * ((M q ω - M p ω) ^ 2 - ((q : ℝ) - p))))) P :=
      ((iWΔ.const_mul a).add (iWY.const_mul _)).const_mul _
    rw [integral_congr_ae (g := fun ω ↦ Real.exp (-c) * (W ω * (Real.exp (a * (M q ω - M p ω))
        - (1 + a * (M q ω - M p ω) + (a * (M q ω - M p ω)) ^ 2 / 2)))
        + ((1 + c) * Real.exp (-c) - 1) * W ω + Real.exp (-c) * (a * (W ω * (M q ω - M p ω))
        + a ^ 2 / 2 * (W ω * ((M q ω - M p ω) ^ 2 - ((q : ℝ) - p))))) (.of_forall fun ω ↦ by
          rw [show Real.exp (a * (M q ω - M p ω) - c)
            = Real.exp (-c) * Real.exp (a * (M q ω - M p ω)) by
              rw [sub_eq_add_neg, Real.exp_add, mul_comm], hc]
          ring),
      integral_add iAB iG, integral_add iA iB, integral_const_mul, integral_const_mul,
      integral_const_mul, h0]
    ring
  rw [hsplit]
  have hX : |∫ ω, W ω * (Real.exp (a * (M q ω - M p ω)) - (1 + a * (M q ω - M p ω)
      + (a * (M q ω - M p ω)) ^ 2 / 2)) ∂P| ≤ C * (κ * ∫ ω, |M q ω - M p ω| ^ 3 ∂P) := by
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_mono iWR.abs ((iCube.const_mul _).const_mul _) fun ω ↦ ?_
    rw [abs_mul]
    exact mul_le_mul (hC ω) (hRb ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))
  have hY : |∫ ω, W ω ∂P| ≤ C := by
    simpa [measureReal_def] using norm_integral_le_of_norm_le_const (f := W) (μ := P)
      (.of_forall fun ω ↦ (Real.norm_eq_abs _).le.trans (hC ω))
  have he : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hc0)
  have hd := abs_one_add_mul_exp_neg_sub_one_le hc0
  have hA := mul_le_mul_of_nonneg_right he (abs_nonneg (∫ ω, W ω * (Real.exp (a * (M q ω
    - M p ω)) - (1 + a * (M q ω - M p ω) + (a * (M q ω - M p ω)) ^ 2 / 2)) ∂P))
  have hB := mul_le_mul hd hY (abs_nonneg _) (sq_nonneg c)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  nlinarith

/-! ### The exponential martingale -/

section Exp

variable (hM : Martingale M 𝓕 P) (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P)
  (hK : ∀ t ω, |M t ω| ≤ K) (hcont : ∀ ω, Continuous fun t ↦ M t ω)
include hM hM2 hK hcont

/-- **`exp(a·M − a²t/2)` keeps its expectation against the bounded past.** For `s ≤ t` and a
bounded `𝓕_s`-measurable `V`, `E[V·Z_t] = E[V·Z_s]` with `Zᵣ = exp(a·Mᵣ − a²r/2)`. Telescoping
along the uniform partition of `[s, t]` and the one-cell estimate bound the difference by
`C·e^{|a|K}·(|a|³e^{2|a|K}·∑ₖ E|Δₖ|³ + (a²(t − s)/2)²/n)`, which tends to `0`. -/
theorem integral_mul_exp_eq (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {V : Ω → ℝ}
    (hV : StronglyMeasurable[𝓕 s] V) {C : ℝ} (hC : ∀ ω, |V ω| ≤ C) :
    ∫ ω, V ω * Real.exp (a * M t ω - a ^ 2 * (t : ℝ) / 2) ∂P
      = ∫ ω, V ω * Real.exp (a * M s ω - a ^ 2 * (s : ℝ) / 2) ∂P := by
  set Z : ℝ≥0 → Ω → ℝ := fun r ω ↦ Real.exp (a * M r ω - a ^ 2 * (r : ℝ) / 2) with hZ
  set κ : ℝ := |a| ^ 3 * Real.exp (2 * |a| * K)
  set C' : ℝ := C * Real.exp (|a| * K)
  have hMm (t : ℝ≥0) : Measurable (M t) := ((hM.stronglyAdapted t).mono (𝓕.le t)).measurable
  have hVm : Measurable V := (hV.mono (𝓕.le s)).measurable
  have hZsm (r : ℝ≥0) : StronglyMeasurable[𝓕 r] (Z r) :=
    Real.continuous_exp.comp_stronglyMeasurable
      (((hM.stronglyAdapted r).const_mul a).sub stronglyMeasurable_const)
  have iVZ (r : ℝ≥0) : Integrable (fun ω ↦ V ω * Z r ω) P :=
    ((memLp_of_abs_le ((hZsm r).mono (𝓕.le r)).aestronglyMeasurable (C := Real.exp (|a| * K))
      (fun ω ↦ by rw [abs_of_pos (Real.exp_pos _)]; exact exp_le_exp_abs_mul hK a r ω)
      1).integrable le_rfl).bdd_mul hVm.aestronglyMeasurable (.of_forall hC)
  -- the bound along the `n`-th partition
  have hbound : ∀ᶠ n : ℕ in atTop, |∫ ω, V ω * Z t ω ∂P - ∫ ω, V ω * Z s ω ∂P|
      ≤ C' * (κ * ∑ k ∈ range n, ∫ ω, |M (unifPartIcc s t n (k + 1)) ω
          - M (unifPartIcc s t n k) ω| ^ 3 ∂P + (a ^ 2 * ((t : ℝ) - s) / 2) ^ 2 / n) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    set π := unifPartIcc s t n
    have hcell (k : ℕ) : |∫ ω, V ω * (Z (π (k + 1)) ω - Z (π k) ω) ∂P|
        ≤ C' * (κ * ∫ ω, |M (π (k + 1)) ω - M (π k) ω| ^ 3 ∂P
          + (a ^ 2 * (((t : ℝ) - s) / n) / 2) ^ 2) := by
      have hsk : s ≤ π k := le_self_add
      have hfac (ω : Ω) : V ω * (Z (π (k + 1)) ω - Z (π k) ω) = (V ω * Z (π k) ω)
          * (Real.exp (a * (M (π (k + 1)) ω - M (π k) ω)
            - a ^ 2 * ((π (k + 1) : ℝ) - π k) / 2) - 1) := by
        simp only [hZ]
        rw [show a * M (π (k + 1)) ω - a ^ 2 * (π (k + 1) : ℝ) / 2
          = (a * M (π k) ω - a ^ 2 * (π k : ℝ) / 2) + (a * (M (π (k + 1)) ω - M (π k) ω)
            - a ^ 2 * ((π (k + 1) : ℝ) - π k) / 2) by ring, Real.exp_add]
        ring
      simp_rw [hfac]
      have h := abs_integral_mul_exp_increment_sub_le hM hM2 hK a
        (unifPartIcc_mono s t n k.le_succ) ((hV.mono (𝓕.mono hsk)).mul (hZsm (π k)))
        (C := C') (fun ω ↦ by
          show |V ω * Z (π k) ω| ≤ C'
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul (hC ω) (exp_le_exp_abs_mul hK a _ ω) (Real.exp_pos _).le
            ((abs_nonneg _).trans (hC ω)))
      exact h.trans_eq (by rw [← unifPartIcc_succ_sub hst n k])
    have htel (ω : Ω) : V ω * Z t ω - V ω * Z s ω
        = ∑ k ∈ range n, V ω * (Z (π (k + 1)) ω - Z (π k) ω) := by
      have e1 : π n = t := unifPartIcc_self hst hn
      have e0 : π 0 = s := unifPartIcc_zero s t n
      rw [← mul_sum, sum_range_sub (fun k ↦ Z (π k) ω), e1, e0, mul_sub]
    rw [← integral_sub (iVZ t) (iVZ s), integral_congr_ae (.of_forall htel),
      integral_finsetSum _ fun k _ ↦ ((iVZ (π (k + 1))).sub (iVZ (π k))).congr (.of_forall fun ω ↦ by
        simp only [Pi.sub_apply, mul_sub])]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun k _ ↦ hcell k).trans_eq ?_)
    rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    field_simp
  have hg : Tendsto (fun n : ℕ ↦ C' * (κ * ∑ k ∈ range n, ∫ ω, |M (unifPartIcc s t n (k + 1)) ω
      - M (unifPartIcc s t n k) ω| ^ 3 ∂P + (a ^ 2 * ((t : ℝ) - s) / 2) ^ 2 / n))
      atTop (𝓝 0) := by
    simpa using ((tendsto_sum_integral_abs_cube hM hK hcont hst hM2).const_mul κ |>.add
      (tendsto_const_div_atTop_nhds_zero_nat _)).const_mul C'
  have h0 := ge_of_tendsto hg hbound
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

/-- **The exponential martingale, over `𝓕_s`-sets**: for `s ≤ t` and `A ∈ 𝓕_s`,
`∫_A exp(a·M_t − a²t/2) dP = ∫_A exp(a·M_s − a²s/2) dP`, which is the form
`IsExpQMartingale.martingale` asks for. -/
theorem setIntegral_exp_eq (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, Real.exp (a * M t ω - a ^ 2 * (t : ℝ) / 2) ∂P
      = ∫ ω in A, Real.exp (a * M s ω - a ^ 2 * (s : ℝ) / 2) ∂P := by
  have h := integral_mul_exp_eq hM hM2 hK hcont a hst
    (stronglyMeasurable_one.indicator hA) (C := 1) (fun ω ↦ by
      by_cases hω : ω ∈ A <;> simp [hω])
  rw [← integral_indicator (𝓕.le s A hA), ← integral_indicator (𝓕.le s A hA)]
  convert h using 2 <;> · funext ω; by_cases hω : ω ∈ A <;> simp [hω]

/-- **`exp(a·M_t − a²t/2)` is a martingale**, as Mathlib's `Martingale`: adapted, and the
set-integral identity `setIntegral_exp_eq` identifies the conditional expectation
(`ae_eq_condExp_of_forall_setIntegral_eq`). -/
theorem martingale_exp (a : ℝ) :
    Martingale (fun t ω ↦ Real.exp (a * M t ω - a ^ 2 * (t : ℝ) / 2)) 𝓕 P := by
  have hZsm (r : ℝ≥0) : StronglyMeasurable[𝓕 r]
      (fun ω ↦ Real.exp (a * M r ω - a ^ 2 * (r : ℝ) / 2)) :=
    Real.continuous_exp.comp_stronglyMeasurable
      (((hM.stronglyAdapted r).const_mul a).sub stronglyMeasurable_const)
  have hi (r : ℝ≥0) : Integrable (fun ω ↦ Real.exp (a * M r ω - a ^ 2 * (r : ℝ) / 2)) P :=
    (memLp_of_abs_le ((hZsm r).mono (𝓕.le r)).aestronglyMeasurable (C := Real.exp (|a| * K))
      (fun ω ↦ by rw [abs_of_pos (Real.exp_pos _)]; exact exp_le_exp_abs_mul hK a r ω)
      1).integrable le_rfl
  exact ⟨hZsm, fun s t hst ↦ (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hi t)
    (fun _ _ _ ↦ (hi s).integrableOn)
    (fun A hA _ ↦ (setIntegral_exp_eq hM hM2 hK hcont a hst hA).symm)
    (hZsm s).aestronglyMeasurable).symm⟩

/-- **Lévy's characterisation, analytic core.** A bounded process `M` with continuous paths,
started at `0`, such that `M` and `M² − t` are martingales, satisfies the library's
exponential-martingale characterisation data `IsExpQMartingale P 𝓕 M T` for every horizon
`T`. Composed with `isQBrownianMotion_of_expMartingale`, `M` has `N(0, t − s)` increments and
independent increments on `[0, T]`. -/
theorem isExpQMartingale (hM0 : M 0 =ᵐ[P] 0) (T : ℝ≥0) : IsExpQMartingale P 𝓕 M T where
  adapted := hM.stronglyAdapted
  zero_start := hM0
  martingale a _ _ hst _ _ hA := setIntegral_exp_eq hM hM2 hK hcont a hst hA

end Exp

end LevyExpMartingale
end MathFin
