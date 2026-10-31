/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.LevyQuadraticSums
public import MathFin.Foundations.ExpMartingaleQBrownian
public import MathFin.Foundations.MartingaleSetIntegral

/-!
# The exponential martingale of a martingale with a slow bracket

The analytic core of the elementary route to Lévy's characterisation (issue #179). Let `M` be a
bounded (`|M| ≤ K`) real process with every path continuous, such that `M` and `M² − A` are
`Martingale`s for `𝓕`, where `A` is a slow clock (`IsSlowClock`: `A₀ = 0`,
`0 ≤ A_q − A_p ≤ q − p`; `A_t = t` or the stopped clock `t ∧ τ`). Then for every real `a`,

  `t ↦ exp(a·M_t − a²A_t/2)` is a martingale              (`martingale_exp`),

and for the clock `A_t = t`, `M` meets the library's exponential-martingale characterisation data
`IsExpQMartingale P 𝓕 M T` as soon as it starts at `0` (`isExpQMartingale`). From there
`isQBrownianMotion_of_expMartingale` (`ExpMartingaleQBrownian`) delivers `N(0, t − s)`
increments and independent increments: `M` is a Brownian motion in law.

No quadratic-variation process and no stochastic integral against `M` is used; this matters at
the pin, where BrownianMotion's general Doob–Meyer decomposition is `sorry`.

## The argument: Itô's formula for `exp(a·x − a²r/2)`, one cell at a time

Write `Zᵣ = exp(a·Mᵣ − a²Aᵣ/2)` and fix a bounded `𝓕_s`-measurable `V`. Along the uniform
partition `s = t₀ ≤ ⋯ ≤ tₙ = t`, telescope `V·(Z_t − Z_s) = ∑ₖ V·Z_{tₖ}·(e^{aΔₖ − cₖ} − 1)`,
with `Δₖ = M_{tₖ₊₁} − M_{tₖ}` and `cₖ = a²(A_{tₖ₊₁} − A_{tₖ})/2 ∈ [0, γ]`, `γ = a²(t − s)/(2n)`.
On one cell, with `W = V·Z_{tₖ}` bounded and `𝓕_{tₖ}`-measurable, compare `e^{aΔ−c} − 1` with its
second-order expansion `G = aΔ + (a²/2)·(Δ² − ΔA)`:

  `E[W·(e^{aΔ−c} − 1)] = E[W·(e^{aΔ−c} − 1 − G)]`,

because `E[W·Δ] = 0` and `E[W·(Δ² − ΔA)] = 0` (`LevyQuadraticSums`: the martingale property of
`M` and of `M² − A`) — the second-order term cancels *exactly*, the probabilistic form of
`∂ᵣ + ½∂ₓₓ = 0`. The remainder is bounded pointwise by

  `|e^{aΔ−c} − 1 − G| ≤ κ|Δ|³ + 2γ² + γ|a||Δ| + γ(a²/2)Δ²`,  `κ = |a|³e^{2|a|K}`

(`abs_exp_sub_sub_le`: Taylor's remainder `|R(x)| ≤ |x|³e^{|x|}` and `|(1 + c)e^{−c} − 1| ≤ c²`),
and `E[Δ²] = E[ΔA] ≤ q − p` absorbs the last term. A *random* clock only costs the cross term
`γ|a||Δ|`, first order in `Δt` but only first order in `Δ`: summed over the cells it is
`g|a|·E[maxₖ|Δₖ|] → 0`. Altogether

  `|E[V·Z_t] − E[V·Z_s]| ≤ C·e^{|a|K}·(κ·∑ₖ E|Δₖ|³ + 3g²/n + g|a|·E[maxₖ|Δₖ|])`,  `g = a²(t − s)/2`,

and the cubic sums and the largest increment vanish (`LevyQuadraticSums`). So the conditional
moment-generating function is propagated cell by cell, and no ODE for
`φ(t) = E[1_A e^{a(M_t − M_s)}]` has to be solved.

## Main results

* `abs_integral_mul_exp_increment_sub_le` — the one-cell estimate.
* `integral_mul_exp_eq` — `E[V·Z_t] = E[V·Z_s]` for bounded `𝓕_s`-measurable `V`.
* `setIntegral_exp_eq` — the set-integral form over `S ∈ 𝓕_s`, as `IsExpQMartingale` states it.
* `martingale_exp` — `t ↦ exp(a·M_t − a²A_t/2)` is a Mathlib `Martingale`.
* `isExpQMartingale` — `M` (started at `0`, bracket `t`) satisfies `IsExpQMartingale P 𝓕 M T`.

## Scope

`M` is **bounded** and **every** path is continuous. The localisation to continuous local
martingales is `LevyCharacterization`, which uses the stopped clock `t ∧ τ` for `A`. The conclusion
that `M` is a Brownian motion is `isQBrownianMotion_of_expMartingale` applied to
`isExpQMartingale`; independence of `M_t − M_s` from `𝓕_s` is `ExpMartingaleBrownian`.
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

/-- Pointwise form of the one-cell estimate. For `0 ≤ c ≤ γ`,

  `|e^{x−c} − 1 − (x + (x²/2 − c))| ≤ |x|³e^{|x|} + 2γ² + γ|x| + γ·x²/2`.

Write `e^{x−c} = e^{−c}·e^x`, expand `e^x` to second order, and regroup as
`e^{−c}·R(x) + ((1 + c)e^{−c} − 1) + (e^{−c} − 1)·(x + x²/2 − c)`. -/
theorem abs_exp_sub_sub_le {x c γ : ℝ} (hc : 0 ≤ c) (hcγ : c ≤ γ) :
    |Real.exp (x - c) - 1 - (x + (x ^ 2 / 2 - c))|
      ≤ |x| ^ 3 * Real.exp |x| + 2 * γ ^ 2 + γ * |x| + γ * (x ^ 2 / 2) := by
  have hR := abs_exp_sub_taylor_two_le x
  have hd := abs_one_add_mul_exp_neg_sub_one_le hc
  have he1 : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hc)
  have he0 := Real.exp_pos (-c)
  have hlin : |Real.exp (-c) - 1| ≤ c := by
    rw [abs_le]
    exact ⟨by linarith [Real.add_one_le_exp (-c)], by linarith⟩
  have hid : Real.exp (x - c) - 1 - (x + (x ^ 2 / 2 - c))
      = Real.exp (-c) * (Real.exp x - (1 + x + x ^ 2 / 2)) + ((1 + c) * Real.exp (-c) - 1)
        + (Real.exp (-c) - 1) * (x + x ^ 2 / 2 - c) := by
    rw [show Real.exp (x - c) = Real.exp (-c) * Real.exp x by rw [sub_eq_neg_add, Real.exp_add]]
    ring
  have h1 : |Real.exp (-c) * (Real.exp x - (1 + x + x ^ 2 / 2))| ≤ |x| ^ 3 * Real.exp |x| := by
    rw [abs_mul, abs_of_pos he0]
    exact (mul_le_of_le_one_left (abs_nonneg _) he1).trans hR
  have h2 : |(1 + c) * Real.exp (-c) - 1| ≤ γ ^ 2 :=
    hd.trans (pow_le_pow_left₀ hc hcγ 2)
  have hx : |x + x ^ 2 / 2 - c| ≤ |x| + x ^ 2 / 2 + c :=
    abs_le.2 ⟨by nlinarith [neg_abs_le x, sq_nonneg x], by nlinarith [le_abs_self x, sq_nonneg x]⟩
  have h3 : |(Real.exp (-c) - 1) * (x + x ^ 2 / 2 - c)| ≤ γ * |x| + γ * (x ^ 2 / 2) + γ ^ 2 := by
    rw [abs_mul]
    have := mul_le_mul hlin hx (abs_nonneg _) hc
    nlinarith [mul_le_mul_of_nonneg_right hcγ (abs_nonneg x), sq_nonneg x,
      mul_le_mul_of_nonneg_right hcγ (by positivity : 0 ≤ x ^ 2 / 2),
      mul_le_mul hcγ hcγ hc (hc.trans hcγ)]
  rw [hid]
  refine (abs_add_three _ _ _).trans ?_
  linarith

variable [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {K : ℝ}
  {A : ℝ≥0 → Ω → ℝ}

/-- A bounded process on a slow clock has `exp(a·M_r − a²A_r/2) ≤ e^{|a|K}`. -/
theorem exp_le_exp_abs_mul (hA : IsSlowClock A) (hK : ∀ t ω, |M t ω| ≤ K) (a : ℝ) (r : ℝ≥0)
    (ω : Ω) : Real.exp (a * M r ω - a ^ 2 * A r ω / 2) ≤ Real.exp (|a| * K) := by
  refine Real.exp_le_exp.2 ?_
  have h1 : a * M r ω ≤ |a| * K := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK r ω) (abs_nonneg a))
  have h2 : 0 ≤ a ^ 2 * A r ω / 2 := by have := hA.apply_nonneg r ω; positivity
  linarith

/-! ### One cell -/

/-- **The one-cell estimate.** For `p ≤ q` and a bounded (`|W| ≤ C`) `𝓕_p`-measurable `W`,

  `|E[W·(e^{aΔ − c} − 1)]| ≤ C·(κ·E|Δ|³ + 3γ² + γ|a|·E|Δ|)`,

with `Δ = M_q − M_p`, `c = a²(A_q − A_p)/2`, `γ = a²(q − p)/2` and `κ = |a|³e^{2|a|K}`.

The second-order expansion `e^{aΔ−c} − 1 ≈ G := aΔ + (a²/2)·((Δ)² − (A_q − A_p))` has
`E[W·G] = 0` (`integral_mul_increment_eq_zero`, `integral_mul_sq_increment_sub`), so
`E[W·(e^{aΔ−c} − 1)] = E[W·(e^{aΔ−c} − 1 − G)]`, and the pointwise remainder bound
`abs_exp_sub_sub_le` (`c ≤ γ`) integrates, using `E[Δ²] = E[A_q − A_p] ≤ q − p`. The clock
`A` need not be deterministic: only `0 ≤ A_q − A_p ≤ q − p` is used. -/
theorem abs_integral_mul_exp_increment_sub_le (hA : IsSlowClock A) (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - A t ω) 𝓕 P) (hK : ∀ t ω, |M t ω| ≤ K) (a : ℝ)
    {p q : ℝ≥0} (hpq : p ≤ q) {W : Ω → ℝ} (hW : StronglyMeasurable[𝓕 p] W) {C : ℝ}
    (hC : ∀ ω, |W ω| ≤ C) :
    |∫ ω, W ω * (Real.exp (a * (M q ω - M p ω) - a ^ 2 * (A q ω - A p ω) / 2) - 1) ∂P|
      ≤ C * (|a| ^ 3 * Real.exp (2 * |a| * K) * ∫ ω, |M q ω - M p ω| ^ 3 ∂P
        + 3 * (a ^ 2 * ((q : ℝ) - p) / 2) ^ 2
        + a ^ 2 * ((q : ℝ) - p) / 2 * |a| * ∫ ω, |M q ω - M p ω| ∂P) := by
  set γ : ℝ := a ^ 2 * ((q : ℝ) - p) / 2 with hγ
  have hd0 : 0 ≤ (q : ℝ) - p := sub_nonneg.2 (NNReal.coe_le_coe.2 hpq)
  have hγ0 : 0 ≤ γ := by positivity
  set κ : ℝ := |a| ^ 3 * Real.exp (2 * |a| * K)
  have hAad := stronglyAdapted_of_martingale_sq_sub hM hM2
  have hMm (t : ℝ≥0) : Measurable (M t) := ((hM.stronglyAdapted t).mono (𝓕.le t)).measurable
  have hAm (t : ℝ≥0) : Measurable (A t) := ((hAad t).mono (𝓕.le t)).measurable
  have hWm : Measurable W := (hW.mono (𝓕.le p)).measurable
  have hΔm : Measurable fun ω ↦ M q ω - M p ω := (hMm q).sub (hMm p)
  have hαm : Measurable fun ω ↦ A q ω - A p ω := (hAm q).sub (hAm p)
  have hΔb (ω : Ω) := abs_sub_le_two_mul hK p q ω
  have hα0 (ω : Ω) := hA.sub_nonneg hpq ω
  have hαd (ω : Ω) := hA.sub_le hpq ω
  -- bounded integrands
  have iΔ : Integrable (fun ω ↦ M q ω - M p ω) P :=
    (memLp_of_abs_le hΔm.aestronglyMeasurable hΔb 1).integrable le_rfl
  have iAbsΔ : Integrable (fun ω ↦ |M q ω - M p ω|) P := iΔ.abs
  have iCube : Integrable (fun ω ↦ |M q ω - M p ω| ^ 3) P :=
    (memLp_of_abs_le (hΔm.abs.pow_const 3).aestronglyMeasurable (C := (2 * K) ^ 3) (fun ω ↦ by
      rw [abs_pow, abs_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hΔb ω) 3) 1).integrable le_rfl
  have iSq : Integrable (fun ω ↦ (M q ω - M p ω) ^ 2) P :=
    (memLp_of_abs_le (hΔm.pow_const 2).aestronglyMeasurable (C := (2 * K) ^ 2) (fun ω ↦ by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hΔb ω) 2) 1).integrable le_rfl
  have iα : Integrable (fun ω ↦ A q ω - A p ω) P :=
    (memLp_of_abs_le hαm.aestronglyMeasurable (C := (q : ℝ) - p) (fun ω ↦ by
      rw [abs_of_nonneg (hα0 ω)]; exact hαd ω) 1).integrable le_rfl
  have iW : Integrable W P :=
    (memLp_of_abs_le hWm.aestronglyMeasurable hC 1).integrable le_rfl
  -- the orthogonality: `E[W·G] = 0`
  have iWΔ := iΔ.bdd_mul hWm.aestronglyMeasurable (.of_forall hC)
  have iWY := (memLp_sq_increment_sub hA hM hM2 hK hpq 1).integrable le_rfl |>.bdd_mul
    hWm.aestronglyMeasurable (.of_forall hC)
  have hWG : ∫ ω, W ω * (a * (M q ω - M p ω) + ((a * (M q ω - M p ω)) ^ 2 / 2
      - a ^ 2 * (A q ω - A p ω) / 2)) ∂P = 0 := by
    have h1 := integral_mul_increment_eq_zero hM hpq hW hC
    have h2 := integral_mul_sq_increment_sub hM hM2 hK hpq hW hC
    have : ∀ ω, W ω * (a * (M q ω - M p ω) + ((a * (M q ω - M p ω)) ^ 2 / 2
        - a ^ 2 * (A q ω - A p ω) / 2))
        = a * (W ω * (M q ω - M p ω))
          + a ^ 2 / 2 * (W ω * ((M q ω - M p ω) ^ 2 - (A q ω - A p ω))) := fun ω ↦ by ring
    simp_rw [this]
    rw [integral_add (iWΔ.const_mul a) (iWY.const_mul _), integral_const_mul, integral_const_mul,
      h1, h2]
    ring
  have iWG : Integrable (fun ω ↦ W ω * (a * (M q ω - M p ω) + ((a * (M q ω - M p ω)) ^ 2 / 2
      - a ^ 2 * (A q ω - A p ω) / 2))) P := by
    refine ((iWΔ.const_mul a).add (iWY.const_mul (a ^ 2 / 2))).congr (.of_forall fun ω ↦ ?_)
    simp only [Pi.add_apply]
    ring
  -- `W·F` is bounded
  have hFb (ω : Ω) : |Real.exp (a * (M q ω - M p ω) - a ^ 2 * (A q ω - A p ω) / 2) - 1|
      ≤ Real.exp (2 * |a| * K) + 1 := by
    have hy : a * (M q ω - M p ω) - a ^ 2 * (A q ω - A p ω) / 2 ≤ 2 * |a| * K := by
      have : a * (M q ω - M p ω) ≤ |a| * (2 * K) := (le_abs_self _).trans (by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hΔb ω) (abs_nonneg a))
      have : 0 ≤ a ^ 2 * (A q ω - A p ω) / 2 := by have := hα0 ω; positivity
      linarith
    have := Real.exp_le_exp.2 hy
    have := Real.exp_pos (a * (M q ω - M p ω) - a ^ 2 * (A q ω - A p ω) / 2)
    rw [abs_le]
    constructor <;> linarith [Real.exp_pos (2 * |a| * K)]
  have iWF : Integrable (fun ω ↦ W ω * (Real.exp (a * (M q ω - M p ω)
      - a ^ 2 * (A q ω - A p ω) / 2) - 1)) P :=
    (memLp_of_abs_le (by fun_prop : Measurable fun ω ↦ W ω * (Real.exp (a * (M q ω - M p ω)
      - a ^ 2 * (A q ω - A p ω) / 2) - 1)).aestronglyMeasurable
      (C := C * (Real.exp (2 * |a| * K) + 1)) (fun ω ↦ by
        rw [abs_mul]
        exact mul_le_mul (hC ω) (hFb ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))) 1).integrable
      le_rfl
  -- remove the second-order part
  have hFG : ∫ ω, W ω * (Real.exp (a * (M q ω - M p ω) - a ^ 2 * (A q ω - A p ω) / 2) - 1) ∂P
      = ∫ ω, W ω * (Real.exp (a * (M q ω - M p ω) - a ^ 2 * (A q ω - A p ω) / 2) - 1
        - (a * (M q ω - M p ω) + ((a * (M q ω - M p ω)) ^ 2 / 2
        - a ^ 2 * (A q ω - A p ω) / 2))) ∂P := by
    have : ∀ ω, W ω * (Real.exp (a * (M q ω - M p ω) - a ^ 2 * (A q ω - A p ω) / 2) - 1
        - (a * (M q ω - M p ω) + ((a * (M q ω - M p ω)) ^ 2 / 2 - a ^ 2 * (A q ω - A p ω) / 2)))
        = W ω * (Real.exp (a * (M q ω - M p ω) - a ^ 2 * (A q ω - A p ω) / 2) - 1)
          - W ω * (a * (M q ω - M p ω) + ((a * (M q ω - M p ω)) ^ 2 / 2
            - a ^ 2 * (A q ω - A p ω) / 2)) := fun ω ↦ by ring
    simp_rw [this]
    rw [integral_sub iWF iWG, hWG, sub_zero]
  -- the pointwise bound
  have hpt (ω : Ω) : |W ω * (Real.exp (a * (M q ω - M p ω) - a ^ 2 * (A q ω - A p ω) / 2) - 1
        - (a * (M q ω - M p ω) + ((a * (M q ω - M p ω)) ^ 2 / 2
        - a ^ 2 * (A q ω - A p ω) / 2)))|
      ≤ C * (κ * |M q ω - M p ω| ^ 3 + 2 * γ ^ 2 + γ * |a| * |M q ω - M p ω|
        + γ * (a ^ 2 / 2) * (M q ω - M p ω) ^ 2) := by
    have hc0 : 0 ≤ a ^ 2 * (A q ω - A p ω) / 2 := by have := hα0 ω; positivity
    have hcγ : a ^ 2 * (A q ω - A p ω) / 2 ≤ γ := by
      rw [hγ]; have := mul_le_mul_of_nonneg_left (hαd ω) (sq_nonneg a); linarith
    have h := abs_exp_sub_sub_le (x := a * (M q ω - M p ω)) hc0 hcγ
    rw [abs_mul a] at h
    have hrem : (|a| * |M q ω - M p ω|) ^ 3 * Real.exp (|a| * |M q ω - M p ω|)
        ≤ κ * |M q ω - M p ω| ^ 3 := by
      calc (|a| * |M q ω - M p ω|) ^ 3 * Real.exp (|a| * |M q ω - M p ω|)
          = |a| ^ 3 * |M q ω - M p ω| ^ 3 * Real.exp (|a| * |M q ω - M p ω|) := by ring
        _ ≤ |a| ^ 3 * |M q ω - M p ω| ^ 3 * Real.exp (2 * |a| * K) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
            have := mul_le_mul_of_nonneg_left (hΔb ω) (abs_nonneg a); linarith)) (by positivity)
        _ = κ * |M q ω - M p ω| ^ 3 := by ring
    have e2 : γ * ((a * (M q ω - M p ω)) ^ 2 / 2) = γ * (a ^ 2 / 2) * (M q ω - M p ω) ^ 2 := by
      ring
    rw [abs_mul]
    exact mul_le_mul (hC ω) (h.trans (by linarith [e2, hrem])) (abs_nonneg _)
      ((abs_nonneg _).trans (hC ω))
  have iFG : Integrable (fun ω ↦ W ω * (Real.exp (a * (M q ω - M p ω)
      - a ^ 2 * (A q ω - A p ω) / 2) - 1 - (a * (M q ω - M p ω) + ((a * (M q ω - M p ω)) ^ 2 / 2
      - a ^ 2 * (A q ω - A p ω) / 2)))) P :=
    (iWF.sub iWG).congr (.of_forall fun ω ↦ by simp only [Pi.sub_apply]; ring)
  have i1 : Integrable (fun ω ↦ κ * |M q ω - M p ω| ^ 3) P := iCube.const_mul κ
  have i2 : Integrable (fun _ : Ω ↦ 2 * γ ^ 2) P := integrable_const _
  have i3 : Integrable (fun ω ↦ γ * |a| * |M q ω - M p ω|) P := iAbsΔ.const_mul _
  have i4 : Integrable (fun ω ↦ γ * (a ^ 2 / 2) * (M q ω - M p ω) ^ 2) P := iSq.const_mul _
  have i12 : Integrable (fun ω ↦ κ * |M q ω - M p ω| ^ 3 + 2 * γ ^ 2) P := i1.add i2
  have i123 : Integrable (fun ω ↦ κ * |M q ω - M p ω| ^ 3 + 2 * γ ^ 2
      + γ * |a| * |M q ω - M p ω|) P := i12.add i3
  have ib : Integrable (fun ω ↦ κ * |M q ω - M p ω| ^ 3 + 2 * γ ^ 2 + γ * |a| * |M q ω - M p ω|
      + γ * (a ^ 2 / 2) * (M q ω - M p ω) ^ 2) P := i123.add i4
  -- `E[Δ²] ≤ q − p`
  have hI2 : ∫ ω, (M q ω - M p ω) ^ 2 ∂P ≤ (q : ℝ) - p := by
    have h2 := integral_mul_sq_increment_sub hM hM2 hK hpq (V := fun _ ↦ (1 : ℝ))
      stronglyMeasurable_const (C := 1) (fun _ ↦ by simp)
    simp only [one_mul] at h2
    rw [integral_sub iSq iα, sub_eq_zero] at h2
    rw [h2]
    have := integral_mono iα (integrable_const ((q : ℝ) - p)) hαd
    simpa [measureReal_def] using this
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (Classical.arbitrary Ω))
  rw [hFG]
  refine abs_integral_le_integral_abs.trans ((integral_mono iFG.abs (ib.const_mul C) hpt).trans ?_)
  rw [integral_const_mul, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  refine mul_le_mul_of_nonneg_left ?_ hC0
  have : γ * (a ^ 2 / 2) * ∫ ω, (M q ω - M p ω) ^ 2 ∂P ≤ γ ^ 2 :=
    (mul_le_mul_of_nonneg_left hI2 (by positivity)).trans_eq (by rw [hγ]; ring)
  linarith

/-! ### The exponential martingale -/

section Exp

variable (hA : IsSlowClock A) (hM : Martingale M 𝓕 P)
  (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - A t ω) 𝓕 P)
  (hK : ∀ t ω, |M t ω| ≤ K) (hcont : ∀ ω, Continuous fun t ↦ M t ω)
include hA hM hM2 hK hcont

/-- **`exp(a·M − a²A/2)` keeps its expectation against the bounded past.** For `s ≤ t` and a
bounded `𝓕_s`-measurable `V`, `E[V·Z_t] = E[V·Z_s]` with `Zᵣ = exp(a·Mᵣ − a²Aᵣ/2)`. Telescoping
along the uniform partition of `[s, t]` and the one-cell estimate bound the difference by
`C·e^{|a|K}·(κ·∑ₖ E|Δₖ|³ + 3g²/n + g|a|·E[maxₖ|Δₖ|])`, `g = a²(t − s)/2`, which tends to `0`. -/
theorem integral_mul_exp_eq (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {V : Ω → ℝ}
    (hV : StronglyMeasurable[𝓕 s] V) {C : ℝ} (hC : ∀ ω, |V ω| ≤ C) :
    ∫ ω, V ω * Real.exp (a * M t ω - a ^ 2 * A t ω / 2) ∂P
      = ∫ ω, V ω * Real.exp (a * M s ω - a ^ 2 * A s ω / 2) ∂P := by
  set Z : ℝ≥0 → Ω → ℝ := fun r ω ↦ Real.exp (a * M r ω - a ^ 2 * A r ω / 2) with hZ
  set κ : ℝ := |a| ^ 3 * Real.exp (2 * |a| * K)
  set C' : ℝ := C * Real.exp (|a| * K)
  set g : ℝ := a ^ 2 * ((t : ℝ) - s) / 2 with hg
  have hg0 : 0 ≤ g := by
    have : (s : ℝ) ≤ t := hst
    rw [hg]; have := sub_nonneg.2 this; positivity
  have hAad := stronglyAdapted_of_martingale_sq_sub hM hM2
  have hAdiv (r : ℝ≥0) : StronglyMeasurable[𝓕 r] fun ω ↦ a ^ 2 * A r ω / 2 := by
    simpa only [div_eq_mul_inv] using ((hAad r).const_mul (a ^ 2)).mul_const 2⁻¹
  have hMm (t : ℝ≥0) : Measurable (M t) := ((hM.stronglyAdapted t).mono (𝓕.le t)).measurable
  have hVm : Measurable V := (hV.mono (𝓕.le s)).measurable
  have hZsm (r : ℝ≥0) : StronglyMeasurable[𝓕 r] (Z r) :=
    Real.continuous_exp.comp_stronglyMeasurable
      (((hM.stronglyAdapted r).const_mul a).sub (hAdiv r))
  have iVZ (r : ℝ≥0) : Integrable (fun ω ↦ V ω * Z r ω) P :=
    ((memLp_of_abs_le ((hZsm r).mono (𝓕.le r)).aestronglyMeasurable (C := Real.exp (|a| * K))
      (fun ω ↦ by rw [abs_of_pos (Real.exp_pos _)]; exact exp_le_exp_abs_mul hA hK a r ω)
      1).integrable le_rfl).bdd_mul hVm.aestronglyMeasurable (.of_forall hC)
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (Classical.arbitrary Ω))
  have hC'0 : 0 ≤ C' := by positivity
  -- the bound along the `n`-th partition
  have hbound : ∀ᶠ n : ℕ in atTop, |∫ ω, V ω * Z t ω ∂P - ∫ ω, V ω * Z s ω ∂P|
      ≤ C' * (κ * ∑ k ∈ range n, ∫ ω, |M (unifPartIcc s t n (k + 1)) ω
          - M (unifPartIcc s t n k) ω| ^ 3 ∂P + 3 * g ^ 2 / n
          + g * |a| * ∫ ω, maxIncr M s t n ω ∂P) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    set π := unifPartIcc s t n
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hcell (k : ℕ) : |∫ ω, V ω * (Z (π (k + 1)) ω - Z (π k) ω) ∂P|
        ≤ C' * (κ * ∫ ω, |M (π (k + 1)) ω - M (π k) ω| ^ 3 ∂P + 3 * (g / n) ^ 2
          + g / n * |a| * ∫ ω, |M (π (k + 1)) ω - M (π k) ω| ∂P) := by
      have hsk : s ≤ π k := le_self_add
      have hfac (ω : Ω) : V ω * (Z (π (k + 1)) ω - Z (π k) ω) = (V ω * Z (π k) ω)
          * (Real.exp (a * (M (π (k + 1)) ω - M (π k) ω)
            - a ^ 2 * (A (π (k + 1)) ω - A (π k) ω) / 2) - 1) := by
        simp only [hZ]
        rw [show a * M (π (k + 1)) ω - a ^ 2 * A (π (k + 1)) ω / 2
          = (a * M (π k) ω - a ^ 2 * A (π k) ω / 2) + (a * (M (π (k + 1)) ω - M (π k) ω)
            - a ^ 2 * (A (π (k + 1)) ω - A (π k) ω) / 2) by ring, Real.exp_add]
        ring
      simp_rw [hfac]
      have h := abs_integral_mul_exp_increment_sub_le hA hM hM2 hK a
        (unifPartIcc_mono s t n k.le_succ) ((hV.mono (𝓕.mono hsk)).mul (hZsm (π k)))
        (C := C') (fun ω ↦ by
          show |V ω * Z (π k) ω| ≤ C'
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul (hC ω) (exp_le_exp_abs_mul hA hK a _ ω) (Real.exp_pos _).le
            ((abs_nonneg _).trans (hC ω)))
      have hlen : (a ^ 2 * (((unifPartIcc s t n (k + 1) : ℝ≥0) : ℝ) - unifPartIcc s t n k) / 2)
          = g / n := by
        rw [unifPartIcc_succ_sub hst n k, hg]; field_simp
      rwa [hlen] at h
    have htel (ω : Ω) : V ω * Z t ω - V ω * Z s ω
        = ∑ k ∈ range n, V ω * (Z (π (k + 1)) ω - Z (π k) ω) := by
      have e1 : π n = t := unifPartIcc_self hst hn
      have e0 : π 0 = s := unifPartIcc_zero s t n
      rw [← mul_sum, sum_range_sub (fun k ↦ Z (π k) ω), e1, e0, mul_sub]
    have hmaxI : Integrable (fun ω ↦ maxIncr M s t n ω) P :=
      (memLp_of_abs_le (measurable_maxIncr hMm s t n).aestronglyMeasurable (C := 2 * K)
        (fun ω ↦ by rw [abs_of_nonneg (maxIncr_nonneg s t n ω)]; exact maxIncr_le hK s t n ω)
        1).integrable le_rfl
    have hc1 (k : ℕ) (hk : k ∈ range n) :
        ∫ ω, |M (π (k + 1)) ω - M (π k) ω| ∂P ≤ ∫ ω, maxIncr M s t n ω ∂P :=
      integral_mono ((hM.integrable _).sub (hM.integrable _)).abs hmaxI fun ω ↦
        abs_le_maxIncr s t hk ω
    rw [← integral_sub (iVZ t) (iVZ s), integral_congr_ae (.of_forall htel),
      integral_finsetSum _ fun k _ ↦ ((iVZ (π (k + 1))).sub (iVZ (π k))).congr (.of_forall fun ω ↦ by
        simp only [Pi.sub_apply, mul_sub])]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun k _ ↦ hcell k).trans
      ((sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_left (add_le_add_right
        (mul_le_mul_of_nonneg_left (hc1 k hk) (mul_nonneg (div_nonneg hg0 n.cast_nonneg)
          (abs_nonneg a))) _) hC'0).trans_eq ?_))
    rw [← mul_sum, sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, sum_const, card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    field_simp
  have hmax : Tendsto (fun n : ℕ ↦ ∫ ω, maxIncr M s t n ω ∂P) atTop (𝓝 0) := by
    simpa using tendsto_integral_maxIncr_pow hM hK hcont s t one_ne_zero
  have hlim : Tendsto (fun n : ℕ ↦ C' * (κ * ∑ k ∈ range n, ∫ ω, |M (unifPartIcc s t n (k + 1)) ω
      - M (unifPartIcc s t n k) ω| ^ 3 ∂P + 3 * g ^ 2 / n
      + g * |a| * ∫ ω, maxIncr M s t n ω ∂P)) atTop (𝓝 0) := by
    simpa using ((((tendsto_sum_integral_abs_cube hA hM hK hcont hst hM2).const_mul κ).add
      (tendsto_const_div_atTop_nhds_zero_nat (3 * g ^ 2))).add
      (hmax.const_mul (g * |a|))).const_mul C'
  have h0 := ge_of_tendsto hlim hbound
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

/-- **The exponential martingale, over `𝓕_s`-sets**: for `s ≤ t` and `A ∈ 𝓕_s`,
`∫_A exp(a·M_t − a²A_t/2) dP = ∫_A exp(a·M_s − a²A_s/2) dP`, which is the form
`IsExpQMartingale.martingale` asks for when the clock is `t`. -/
theorem setIntegral_exp_eq (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {S : Set Ω}
    (hS : MeasurableSet[𝓕 s] S) :
    ∫ ω in S, Real.exp (a * M t ω - a ^ 2 * A t ω / 2) ∂P
      = ∫ ω in S, Real.exp (a * M s ω - a ^ 2 * A s ω / 2) ∂P := by
  have h := integral_mul_exp_eq hA hM hM2 hK hcont a hst
    (stronglyMeasurable_one.indicator hS) (C := 1) (fun ω ↦ by
      by_cases hω : ω ∈ S <;> simp [hω])
  rw [← integral_indicator (𝓕.le s S hS), ← integral_indicator (𝓕.le s S hS)]
  convert h using 2 <;> · funext ω; by_cases hω : ω ∈ S <;> simp [hω]

/-- **`exp(a·M_t − a²A_t/2)` is a martingale**, as Mathlib's `Martingale`: adapted, and the
set-integral identity `setIntegral_exp_eq` makes it a martingale
(`martingale_of_setIntegral_eq`). -/
theorem martingale_exp (a : ℝ) :
    Martingale (fun t ω ↦ Real.exp (a * M t ω - a ^ 2 * A t ω / 2)) 𝓕 P := by
  have hAad := stronglyAdapted_of_martingale_sq_sub hM hM2
  have hAdiv (r : ℝ≥0) : StronglyMeasurable[𝓕 r] fun ω ↦ a ^ 2 * A r ω / 2 := by
    simpa only [div_eq_mul_inv] using ((hAad r).const_mul (a ^ 2)).mul_const 2⁻¹
  have hZsm (r : ℝ≥0) : StronglyMeasurable[𝓕 r]
      (fun ω ↦ Real.exp (a * M r ω - a ^ 2 * A r ω / 2)) :=
    Real.continuous_exp.comp_stronglyMeasurable
      (((hM.stronglyAdapted r).const_mul a).sub (hAdiv r))
  have hi (r : ℝ≥0) : Integrable (fun ω ↦ Real.exp (a * M r ω - a ^ 2 * A r ω / 2)) P :=
    (memLp_of_abs_le ((hZsm r).mono (𝓕.le r)).aestronglyMeasurable (C := Real.exp (|a| * K))
      (fun ω ↦ by rw [abs_of_pos (Real.exp_pos _)]; exact exp_le_exp_abs_mul hA hK a r ω)
      1).integrable le_rfl
  exact martingale_of_setIntegral_eq hZsm hi fun s t hst S hS ↦
    (setIntegral_exp_eq hA hM hM2 hK hcont a hst hS).symm

end Exp

/-- **Lévy's characterisation, analytic core.** A bounded process `M` with continuous paths,
started at `0`, such that `M` and `M² − t` are martingales, satisfies the library's
exponential-martingale characterisation data `IsExpQMartingale P 𝓕 M T` for every horizon
`T`. Composed with `isQBrownianMotion_of_expMartingale`, `M` has `N(0, t − s)` increments and
independent increments on `[0, T]`. It is `setIntegral_exp_eq` for the clock `A_t = t`. -/
theorem isExpQMartingale (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P) (hK : ∀ t ω, |M t ω| ≤ K)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hM0 : M 0 =ᵐ[P] 0) (T : ℝ≥0) :
    IsExpQMartingale P 𝓕 M T where
  adapted := hM.stronglyAdapted
  zero_start := hM0
  martingale a _ _ hst _ _ hS :=
    setIntegral_exp_eq (A := fun t _ ↦ (t : ℝ)) isSlowClock_id hM hM2 hK hcont a hst hS

end LevyExpMartingale
end MathFin
