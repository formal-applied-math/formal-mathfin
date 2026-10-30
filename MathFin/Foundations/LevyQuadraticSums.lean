/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaAdapted

/-!
# Quadratic sums of a martingale whose bracket is `t`

The first half of the elementary route to Lévy's characterisation (issue #179). Let `M` be a
real process on a filtered probability space `(Ω, 𝓕, P)` with

* every path `t ↦ M t ω` continuous,
* `|M t ω| ≤ K` everywhere (bounded — localisation is a later step),
* `M` and `M² − t` both `Martingale`s for `𝓕` (Mathlib's notion).

Along the uniform partition of `[s, t]` into `n` cells (`unifPartIcc`, the library's `unifPart`
shifted to start at `s`), the sum of squared increments converges to `t − s` in mean square:

  `E[(∑ₖ (M_{tₖ₊₁} − M_{tₖ})² − (t − s))²] → 0`        (`tendsto_integral_sq_sum_sub`),

and the cubed increments are negligible, `∑ₖ E|M_{tₖ₊₁} − M_{tₖ}|³ → 0`
(`tendsto_sum_integral_abs_cube`) — the estimate the exponential martingale of
`LevyExpMartingale` consumes. No quadratic-variation process and no stochastic integral
against `M` appears: the bracket enters only through the martingale property of `M² − t`.

## The argument

It is the argument of `QuadraticVariationL2` for Brownian motion, with the two Gaussian inputs
replaced by martingale ones.

* **Orthogonality.** For a bounded `𝓕_a`-measurable `V` and `a ≤ b`,
  `E[V·(M_b − M_a)] = 0` and `E[V·((M_b − M_a)² − (b − a))] = 0`
  (`integral_mul_increment_eq_zero`, `integral_mul_sq_increment_sub`): pull `V` out of the
  conditional expectation, and expand `(M_b − M_a)² − (b−a)` as an increment of `M² − t` minus
  `2M_a·(M_b − M_a)`. So the centred squared increments `Yₖ = (ΔMₖ)² − Δtₖ` are pairwise
  orthogonal, and `E[(∑ Yₖ)²] = ∑ E[Yₖ²]` (`integral_sq_sum_centred`) — Pythagoras, as for
  Brownian motion, but with the cross terms killed by the martingale property instead of by
  independence.
* **No kurtosis.** Brownian motion evaluates `E[Yₖ²] = 2Δtₖ²` exactly; here only the bound
  `Yₖ² ≤ 2δ²·(ΔMₖ)² + 2h·Δtₖ` is available, with `δ` the largest increment. It folds back into
  the sum itself, `∑ (ΔMₖ)² = ∑ Yₖ + (t − s)`, and the AM–GM step
  `2δ²·∑Yₖ ≤ 2δ⁴ + (∑Yₖ)²/2` absorbs the unknown into the left side:
  `E[(∑Yₖ)²] ≤ 4E[δ⁴] + 4(t−s)E[δ²] + 4h(t−s)` (`integral_sq_sum_centred_le`). No
  Cauchy–Schwarz and no a-priori bound on `E[(∑(ΔMₖ)²)²]` is needed.
* **Uniform continuity.** The largest increment `maxIncr` is bounded by `2K` and tends to `0`
  pathwise (`ItoFormulaAdapted.eventually_abs_sub_unifPart_lt`, Heine–Cantor on `[s, t]`), so
  `E[δⁿ] → 0` by dominated convergence (`tendsto_integral_maxIncr_pow`).

## Main results

* `integral_mul_increment_eq_zero` — a martingale increment is orthogonal to every bounded
  random variable measurable at its left end (any preorder index).
* `integral_mul_sq_increment_sub` — the same for `(ΔM)² − Δt` when `M² − t` is a martingale.
* `integral_sq_sum_centred` — Pythagoras for the centred squared increments over any monotone
  partition.
* `integral_sq_sum_centred_le`, `sum_integral_abs_cube_le` — the mean-square and cubic bounds in
  terms of the largest increment.
* `tendsto_integral_sq_sum_sub` — **the quadratic sums converge to `t − s` in `L²(P)`**.
* `tendsto_sum_integral_abs_cube` — the cubic sums tend to `0` in `L¹(P)`.

## Scope

Everything is for a **bounded** `M` (`|M| ≤ K`) with **every** path continuous, and along the
uniform partition of `[s, t]`. The per-partition identities and bounds hold for any monotone
partition; only the limits are stated for the uniform one.
-/

@[expose] public section

namespace MathFin
namespace LevyQuadraticSums

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open QuadraticVariationL2 ItoIntegralBrownian
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### Bounded functions -/

/-- A bounded a.e.-strongly measurable real function lies in every `Lᵖ` of a finite measure. -/
theorem memLp_of_abs_le [IsFiniteMeasure P] {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) {C : ℝ}
    (hC : ∀ ω, |f ω| ≤ C) (p : ℝ≥0∞) : MemLp f p P :=
  .of_bound hf C (.of_forall hC)

/-- `|x² − c| ≤ D² + |c|` when `|x| ≤ D`. -/
theorem abs_sq_sub_le {x c D : ℝ} (hx : |x| ≤ D) : |x ^ 2 - c| ≤ D ^ 2 + |c| := by
  have h := sq_le_sq' (abs_le.1 hx).1 (abs_le.1 hx).2
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x, le_abs_self c, neg_abs_le c]

/-! ### Martingale increments against a bounded past factor -/

/-- **A martingale increment is orthogonal to the bounded past.** For a martingale `f`, `i ≤ j`,
and a bounded `𝓕 i`-measurable `V`, `E[V·(f j − f i)] = 0`: the pull-out property moves `V` out
of `E[V·f j | 𝓕 i]`, and the martingale property replaces `E[f j | 𝓕 i]` by `f i`. -/
theorem integral_mul_increment_eq_zero {ι : Type*} [Preorder ι] {𝓕 : Filtration ι mΩ}
    [IsFiniteMeasure P] {f : ι → Ω → ℝ} (hf : Martingale f 𝓕 P) {i j : ι} (hij : i ≤ j)
    {V : Ω → ℝ} (hV : StronglyMeasurable[𝓕 i] V) {C : ℝ} (hC : ∀ ω, |V ω| ≤ C) :
    ∫ ω, V ω * (f j ω - f i ω) ∂P = 0 := by
  have hb (k : ι) : Integrable (fun ω ↦ V ω * f k ω) P :=
    (hf.integrable k).bdd_mul (hV.mono (𝓕.le i)).aestronglyMeasurable (.of_forall hC)
  simp_rw [mul_sub]
  rw [integral_sub (hb j) (hb i), sub_eq_zero, ← integral_condExp (𝓕.le i)]
  refine integral_congr_ae ?_
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hV (hb j) (hf.integrable j),
    hf.condExp_ae_eq hij] with ω h1 h2
  exact h1.trans (by rw [Pi.mul_apply, h2])

variable {𝓕 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {K : ℝ}

/-- A bounded process has increments bounded by `2K`. -/
theorem abs_sub_le_two_mul (hK : ∀ t ω, |M t ω| ≤ K) (p q : ℝ≥0) (ω : Ω) :
    |M q ω - M p ω| ≤ 2 * K := by
  have hq := abs_le.1 (hK q ω)
  have hp := abs_le.1 (hK p ω)
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **The bracket is `t`, tested against the bounded past.** If `M` and `M² − t` are
martingales and `M` is bounded, then for `a ≤ b` and a bounded `𝓕 a`-measurable `V`,
`E[V·((M_b − M_a)² − (b − a))] = 0`. Expand `(M_b − M_a)² − (b − a)` as the increment of
`M² − t` minus `2M_a·(M_b − M_a)` and apply `integral_mul_increment_eq_zero` to each. -/
theorem integral_mul_sq_increment_sub [IsFiniteMeasure P] (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P) (hK : ∀ t ω, |M t ω| ≤ K)
    {a b : ℝ≥0} (hab : a ≤ b) {V : Ω → ℝ} (hV : StronglyMeasurable[𝓕 a] V) {C : ℝ}
    (hC : ∀ ω, |V ω| ≤ C) :
    ∫ ω, V ω * ((M b ω - M a ω) ^ 2 - ((b : ℝ) - a)) ∂P = 0 := by
  have hVa : ∀ ω, |V ω * M a ω| ≤ C * K := fun ω ↦ by
    rw [abs_mul]
    exact mul_le_mul (hC ω) (hK a ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))
  have hVm := (hV.mono (𝓕.le a)).aestronglyMeasurable (μ := P)
  have i1 : Integrable (fun ω ↦ V ω * ((M b ω ^ 2 - b) - (M a ω ^ 2 - a))) P :=
    ((hM2.integrable b).sub (hM2.integrable a)).bdd_mul hVm (.of_forall hC)
  have i2 : Integrable (fun ω ↦ V ω * M a ω * (M b ω - M a ω)) P :=
    ((hM.integrable b).sub (hM.integrable a)).bdd_mul
      (hVm.mul ((hM.stronglyAdapted a).mono (𝓕.le a)).aestronglyMeasurable) (.of_forall hVa)
  have h1 := integral_mul_increment_eq_zero hM2 hab hV hC
  have h2 := integral_mul_increment_eq_zero hM hab (hV.mul (hM.stronglyAdapted a)) hVa
  calc ∫ ω, V ω * ((M b ω - M a ω) ^ 2 - ((b : ℝ) - a)) ∂P
      = ∫ ω, (V ω * ((M b ω ^ 2 - b) - (M a ω ^ 2 - a))
          - 2 * (V ω * M a ω * (M b ω - M a ω))) ∂P :=
        integral_congr_ae (.of_forall fun ω ↦ by ring)
    _ = 0 := by
        rw [integral_sub i1 (i2.const_mul 2), integral_const_mul]
        simp only [Pi.mul_apply] at h2
        rw [h1, h2]
        ring

/-! ### Over one partition -/

section Partition

variable [IsProbabilityMeasure P]

/-- The centred squared increment `(ΔMₖ)² − Δtₖ` over a cell of a partition is bounded and
measurable at the cell's right end, so it lies in every `Lᵖ`. -/
theorem memLp_sq_increment_sub (hM : Martingale M 𝓕 P) (hK : ∀ t ω, |M t ω| ≤ K)
    (a b : ℝ≥0) (c : ℝ) (p : ℝ≥0∞) :
    MemLp (fun ω ↦ (M b ω - M a ω) ^ 2 - c) p P :=
  memLp_of_abs_le (((((hM.stronglyAdapted b).mono (𝓕.le b)).sub
      ((hM.stronglyAdapted a).mono (𝓕.le a))).pow 2).sub
      stronglyMeasurable_const).aestronglyMeasurable
    (fun ω ↦ abs_sq_sub_le (abs_sub_le_two_mul hK a b ω)) p

/-- **Pythagoras for the centred squared increments.** Over any monotone partition `π`, the
centred squared increments `Yₖ = (M_{πₖ₊₁} − M_{πₖ})² − (πₖ₊₁ − πₖ)` are pairwise orthogonal
(`integral_mul_sq_increment_sub`, the earlier one being bounded and measurable at the later
cell's left end), so the mean square of their sum is the sum of their mean squares. -/
theorem integral_sq_sum_centred (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P) (hK : ∀ t ω, |M t ω| ≤ K)
    {π : ℕ → ℝ≥0} (hπ : Monotone π) (n : ℕ) :
    ∫ ω, (∑ k ∈ range n, ((M (π (k + 1)) ω - M (π k) ω) ^ 2 - ((π (k + 1) : ℝ) - π k))) ^ 2 ∂P
      = ∑ k ∈ range n,
          ∫ ω, ((M (π (k + 1)) ω - M (π k) ω) ^ 2 - ((π (k + 1) : ℝ) - π k)) ^ 2 ∂P := by
  set Y : ℕ → Ω → ℝ := fun k ω ↦ (M (π (k + 1)) ω - M (π k) ω) ^ 2 - ((π (k + 1) : ℝ) - π k)
  have hYL2 (k : ℕ) : MemLp (Y k) 2 P := memLp_sq_increment_sub hM hK _ _ _ 2
  have hint (k l : ℕ) : Integrable (fun ω ↦ Y k ω * Y l ω) P := (hYL2 k).integrable_mul (hYL2 l)
  have hcross (k l : ℕ) (hlk : l < k) : ∫ ω, Y l ω * Y k ω ∂P = 0 := by
    have hr : π (l + 1) ≤ π k := hπ hlk
    refine integral_mul_sq_increment_sub hM hM2 hK (hπ k.le_succ) ((((
      (hM.stronglyAdapted _).mono (𝓕.mono hr)).sub ((hM.stronglyAdapted _).mono
      (𝓕.mono ((hπ l.le_succ).trans hr)))).pow 2).sub stronglyMeasurable_const)
      (fun ω ↦ abs_sq_sub_le (abs_sub_le_two_mul hK (π l) (π (l + 1)) ω))
  calc ∫ ω, (∑ k ∈ range n, Y k ω) ^ 2 ∂P
      = ∫ ω, ∑ k ∈ range n, ∑ l ∈ range n, Y k ω * Y l ω ∂P := by simp_rw [sq, sum_mul_sum]
    _ = ∑ k ∈ range n, ∑ l ∈ range n, ∫ ω, Y k ω * Y l ω ∂P := by
        rw [integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hint k l]
        exact sum_congr rfl fun k _ ↦ integral_finsetSum _ fun l _ ↦ hint k l
    _ = ∑ k ∈ range n, ∫ ω, Y k ω ^ 2 ∂P := by
        refine sum_congr rfl fun k hk ↦ ?_
        rw [sum_eq_single k (fun l _ hlk ↦ ?_) (fun hk' ↦ absurd hk hk')]
        · simp_rw [sq]
        · rcases lt_or_gt_of_ne hlk with hlt | hgt
          · exact (integral_congr_ae (.of_forall fun ω ↦ mul_comm _ _)).trans (hcross k l hlt)
          · exact hcross l k hgt

/-- **The mean-square bound, in terms of the largest increment.** Over a monotone partition `π`
with cells of length at most `h`, and any measurable `0 ≤ δ ≤ 2K` dominating every increment
`|M_{πₖ₊₁} − M_{πₖ}|`, the centred quadratic sum satisfies

  `E[(∑ Yₖ)²] ≤ 4E[δ⁴] + 4L·E[δ²] + 4h·L`,  `L = π_n − π_0`.

Pointwise `∑ Yₖ² ≤ 2δ²∑(ΔMₖ)² + 2hL = 2δ²(∑Yₖ + L) + 2hL`, and `2δ²∑Yₖ ≤ 2δ⁴ + (∑Yₖ)²/2`
(AM–GM); integrating and using Pythagoras (`integral_sq_sum_centred`) puts half of `E[(∑Yₖ)²]`
on the right, where it is absorbed. -/
theorem integral_sq_sum_centred_le (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P) (hK : ∀ t ω, |M t ω| ≤ K)
    {π : ℕ → ℝ≥0} (hπ : Monotone π) (n : ℕ) {h : ℝ}
    (hh : ∀ k ∈ range n, (π (k + 1) : ℝ) - π k ≤ h) {δ : Ω → ℝ} (hδm : Measurable δ)
    (hδ0 : ∀ ω, 0 ≤ δ ω) (hδK : ∀ ω, δ ω ≤ 2 * K)
    (hδ : ∀ ω, ∀ k ∈ range n, |M (π (k + 1)) ω - M (π k) ω| ≤ δ ω) :
    ∫ ω, (∑ k ∈ range n, ((M (π (k + 1)) ω - M (π k) ω) ^ 2 - ((π (k + 1) : ℝ) - π k))) ^ 2 ∂P
      ≤ 4 * ∫ ω, δ ω ^ 4 ∂P + 4 * ((π n : ℝ) - π 0) * ∫ ω, δ ω ^ 2 ∂P
        + 4 * h * ((π n : ℝ) - π 0) := by
  set L : ℝ := (π n : ℝ) - π 0
  set Y : ℕ → Ω → ℝ := fun k ω ↦ (M (π (k + 1)) ω - M (π k) ω) ^ 2 - ((π (k + 1) : ℝ) - π k)
    with hY
  set D := ∫ ω, (∑ k ∈ range n, Y k ω) ^ 2 ∂P
  have htel : ∑ k ∈ range n, ((π (k + 1) : ℝ) - π k) = L := sum_range_sub (fun k ↦ (π k : ℝ)) n
  have hYL2 (k : ℕ) : MemLp (Y k) 2 P := memLp_sq_increment_sub hM hK _ _ _ 2
  have hδp (p : ℕ) : Integrable (fun ω ↦ δ ω ^ p) P :=
    (memLp_of_abs_le (hδm.pow_const p).aestronglyMeasurable (C := (2 * K) ^ p) (fun ω ↦ by
      rw [abs_pow, abs_of_nonneg (hδ0 ω)]
      exact pow_le_pow_left₀ (hδ0 ω) (hδK ω) p) 1).integrable le_rfl
  have hS : Integrable (fun ω ↦ (∑ k ∈ range n, Y k ω) ^ 2) P :=
    (memLp_finsetSum _ fun k _ ↦ hYL2 k).integrable_sq
  -- the pointwise bound
  have hpt (ω : Ω) : ∑ k ∈ range n, Y k ω ^ 2
      ≤ 2 * δ ω ^ 4 + (∑ k ∈ range n, Y k ω) ^ 2 / 2 + 2 * L * δ ω ^ 2 + 2 * h * L := by
    have hcell : ∀ k ∈ range n, Y k ω ^ 2
        ≤ 2 * δ ω ^ 2 * (M (π (k + 1)) ω - M (π k) ω) ^ 2
          + 2 * h * ((π (k + 1) : ℝ) - π k) := fun k hk ↦ by
      have he0 : 0 ≤ (π (k + 1) : ℝ) - π k := sub_nonneg.2 (NNReal.coe_le_coe.2 (hπ k.le_succ))
      have hx : (M (π (k + 1)) ω - M (π k) ω) ^ 2 ≤ δ ω ^ 2 :=
        sq_le_sq' (abs_le.1 (hδ ω k hk)).1 (abs_le.1 (hδ ω k hk)).2
      have hx0 := sq_nonneg (M (π (k + 1)) ω - M (π k) ω)
      simp only [hY]
      nlinarith [mul_le_mul_of_nonneg_left hx hx0, mul_le_mul_of_nonneg_right (hh k hk) he0,
        sq_nonneg ((M (π (k + 1)) ω - M (π k) ω) ^ 2 + ((π (k + 1) : ℝ) - π k))]
    have hsum : ∑ k ∈ range n, (M (π (k + 1)) ω - M (π k) ω) ^ 2
        = ∑ k ∈ range n, Y k ω + L := by
      simp only [hY, sum_sub_distrib, htel, sub_add_cancel]
    calc ∑ k ∈ range n, Y k ω ^ 2
        ≤ ∑ k ∈ range n, (2 * δ ω ^ 2 * (M (π (k + 1)) ω - M (π k) ω) ^ 2
            + 2 * h * ((π (k + 1) : ℝ) - π k)) := sum_le_sum hcell
      _ = 2 * δ ω ^ 2 * (∑ k ∈ range n, Y k ω + L) + 2 * h * L := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, hsum, htel]
      _ ≤ _ := by nlinarith [sq_nonneg (2 * δ ω ^ 2 - ∑ k ∈ range n, Y k ω)]
  have i1 : Integrable (fun ω ↦ 2 * δ ω ^ 4 + (∑ k ∈ range n, Y k ω) ^ 2 / 2) P :=
    ((hδp 4).const_mul 2).add (hS.div_const 2)
  have i2 : Integrable (fun ω ↦ 2 * δ ω ^ 4 + (∑ k ∈ range n, Y k ω) ^ 2 / 2
      + 2 * L * δ ω ^ 2) P := i1.add ((hδp 2).const_mul (2 * L))
  have i3 : Integrable (fun ω ↦ 2 * δ ω ^ 4 + (∑ k ∈ range n, Y k ω) ^ 2 / 2
      + 2 * L * δ ω ^ 2 + 2 * h * L) P := i2.add (integrable_const (2 * h * L))
  have hint := integral_mono (integrable_finsetSum _ fun k _ ↦ (hYL2 k).integrable_sq) i3 hpt
  rw [integral_finsetSum _ fun k _ ↦ (hYL2 k).integrable_sq, integral_add i2 (integrable_const _),
    integral_add i1 ((hδp 2).const_mul _), integral_add ((hδp 4).const_mul _) (hS.div_const 2),
    integral_const_mul, integral_const_mul, integral_div, integral_const] at hint
  have hD : D = ∑ k ∈ range n, ∫ ω, Y k ω ^ 2 ∂P := integral_sq_sum_centred hM hM2 hK hπ n
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hint
  change D ≤ _
  linarith

/-- **The cubic bound.** Under the hypotheses of `integral_sq_sum_centred_le` (without the
bracket), `∑ₖ E|ΔMₖ|³ ≤ (E[δ²] + E[(∑Yₖ)²])/2 + L·E[δ]`: pointwise
`∑|ΔMₖ|³ ≤ δ·∑(ΔMₖ)² = δ·(∑Yₖ + L) ≤ (δ² + (∑Yₖ)²)/2 + L·δ`. -/
theorem sum_integral_abs_cube_le (hM : Martingale M 𝓕 P) (hK : ∀ t ω, |M t ω| ≤ K)
    {π : ℕ → ℝ≥0} (n : ℕ) {δ : Ω → ℝ} (hδm : Measurable δ)
    (hδ0 : ∀ ω, 0 ≤ δ ω) (hδK : ∀ ω, δ ω ≤ 2 * K)
    (hδ : ∀ ω, ∀ k ∈ range n, |M (π (k + 1)) ω - M (π k) ω| ≤ δ ω) :
    ∑ k ∈ range n, ∫ ω, |M (π (k + 1)) ω - M (π k) ω| ^ 3 ∂P
      ≤ (∫ ω, δ ω ^ 2 ∂P + ∫ ω, (∑ k ∈ range n,
            ((M (π (k + 1)) ω - M (π k) ω) ^ 2 - ((π (k + 1) : ℝ) - π k))) ^ 2 ∂P) / 2
        + ((π n : ℝ) - π 0) * ∫ ω, δ ω ∂P := by
  set L : ℝ := (π n : ℝ) - π 0
  set Y : ℕ → Ω → ℝ := fun k ω ↦ (M (π (k + 1)) ω - M (π k) ω) ^ 2 - ((π (k + 1) : ℝ) - π k)
    with hY
  have htel : ∑ k ∈ range n, ((π (k + 1) : ℝ) - π k) = L := sum_range_sub (fun k ↦ (π k : ℝ)) n
  have hδp (p : ℕ) : Integrable (fun ω ↦ δ ω ^ p) P :=
    (memLp_of_abs_le (hδm.pow_const p).aestronglyMeasurable (C := (2 * K) ^ p) (fun ω ↦ by
      rw [abs_pow, abs_of_nonneg (hδ0 ω)]
      exact pow_le_pow_left₀ (hδ0 ω) (hδK ω) p) 1).integrable le_rfl
  have hS : Integrable (fun ω ↦ (∑ k ∈ range n, Y k ω) ^ 2) P :=
    (memLp_finsetSum _ fun k _ ↦ memLp_sq_increment_sub hM hK _ _ _ 2).integrable_sq
  have hMm (t : ℝ≥0) : Measurable (M t) := ((hM.stronglyAdapted t).mono (𝓕.le t)).measurable
  have hcube (k : ℕ) : Integrable (fun ω ↦ |M (π (k + 1)) ω - M (π k) ω| ^ 3) P :=
    (memLp_of_abs_le (by fun_prop : Measurable fun ω ↦ |M (π (k + 1)) ω - M (π k) ω| ^ 3
      ).aestronglyMeasurable
      (C := (2 * K) ^ 3) (fun ω ↦ by
        rw [abs_pow, abs_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_two_mul hK _ _ ω) 3) 1).integrable
      le_rfl
  have hpt (ω : Ω) : ∑ k ∈ range n, |M (π (k + 1)) ω - M (π k) ω| ^ 3
      ≤ (δ ω ^ 2 + (∑ k ∈ range n, Y k ω) ^ 2) / 2 + L * δ ω := by
    have hsum : ∑ k ∈ range n, (M (π (k + 1)) ω - M (π k) ω) ^ 2
        = ∑ k ∈ range n, Y k ω + L := by
      simp only [hY, sum_sub_distrib, htel, sub_add_cancel]
    calc ∑ k ∈ range n, |M (π (k + 1)) ω - M (π k) ω| ^ 3
        ≤ ∑ k ∈ range n, δ ω * (M (π (k + 1)) ω - M (π k) ω) ^ 2 := sum_le_sum fun k hk ↦ by
          rw [pow_succ', ← sq_abs (M (π (k + 1)) ω - M (π k) ω)]
          exact mul_le_mul_of_nonneg_right (hδ ω k hk) (sq_nonneg _)
      _ = δ ω * (∑ k ∈ range n, Y k ω + L) := by rw [← mul_sum, hsum]
      _ ≤ _ := by nlinarith [sq_nonneg (δ ω - ∑ k ∈ range n, Y k ω)]
  have i0 : Integrable (fun ω ↦ δ ω ^ 2 + (∑ k ∈ range n, Y k ω) ^ 2) P := (hδp 2).add hS
  have i1 : Integrable (fun ω ↦ (δ ω ^ 2 + (∑ k ∈ range n, Y k ω) ^ 2) / 2) P := i0.div_const 2
  have i2 : Integrable (fun ω ↦ L * δ ω) P := by simpa using (hδp 1).const_mul L
  have hint := integral_mono (g := fun ω ↦ (δ ω ^ 2 + (∑ k ∈ range n, Y k ω) ^ 2) / 2 + L * δ ω)
    (integrable_finsetSum _ fun k _ ↦ hcube k) (i1.add i2) hpt
  rw [integral_finsetSum _ fun k _ ↦ hcube k, integral_add i1 i2, integral_div,
    integral_add (hδp 2) hS, integral_const_mul] at hint
  exact hint

end Partition

/-! ### The uniform partition of `[s, t]` -/

/-- The uniform partition of `[s, t]` into `n` cells: the library's `unifPart` of `[0, t − s]`,
shifted to start at `s`. -/
noncomputable def unifPartIcc (s t : ℝ≥0) (n k : ℕ) : ℝ≥0 := s + unifPart (t - s) n k

theorem unifPartIcc_mono (s t : ℝ≥0) (n : ℕ) : Monotone (unifPartIcc s t n) :=
  fun _ _ hij ↦ by unfold unifPartIcc; gcongr; exact unifPart_mono _ n hij

theorem unifPartIcc_zero (s t : ℝ≥0) (n : ℕ) : unifPartIcc s t n 0 = s := by
  simp [unifPartIcc, unifPart]

theorem unifPartIcc_self {s t : ℝ≥0} (hst : s ≤ t) {n : ℕ} (hn : n ≠ 0) :
    unifPartIcc s t n n = t := by
  have hn0 : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp only [unifPartIcc, unifPart, div_self hn0, one_mul, add_tsub_cancel_of_le hst]

theorem unifPartIcc_succ_sub {s t : ℝ≥0} (hst : s ≤ t) (n k : ℕ) :
    ((unifPartIcc s t n (k + 1) : ℝ) - unifPartIcc s t n k) = ((t : ℝ) - s) / n := by
  rw [unifPartIcc, unifPartIcc, NNReal.coe_add, NNReal.coe_add, add_sub_add_left_eq_sub,
    AdaptedQuadraticVariation.unifPart_succ_sub, NNReal.coe_sub hst]

/-- The largest increment of `M` over the cells of the uniform partition of `[s, t]`. -/
noncomputable def maxIncr (M : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ((range n).sup fun k ↦ ‖M (unifPartIcc s t n (k + 1)) ω - M (unifPartIcc s t n k) ω‖₊ : ℝ≥0)

theorem maxIncr_nonneg (s t : ℝ≥0) (n : ℕ) (ω : Ω) : 0 ≤ maxIncr M s t n ω :=
  NNReal.coe_nonneg _

theorem abs_le_maxIncr (s t : ℝ≥0) {n k : ℕ} (hk : k ∈ range n) (ω : Ω) :
    |M (unifPartIcc s t n (k + 1)) ω - M (unifPartIcc s t n k) ω| ≤ maxIncr M s t n ω := by
  have := NNReal.coe_le_coe.2 (le_sup (f := fun k ↦
    ‖M (unifPartIcc s t n (k + 1)) ω - M (unifPartIcc s t n k) ω‖₊) hk)
  rwa [coe_nnnorm, Real.norm_eq_abs] at this

theorem maxIncr_le (hK : ∀ t ω, |M t ω| ≤ K) (s t : ℝ≥0) (n : ℕ) (ω : Ω) :
    maxIncr M s t n ω ≤ 2 * K := by
  have h2K : 0 ≤ 2 * K := by linarith [(abs_nonneg _).trans (hK 0 ω)]
  calc maxIncr M s t n ω ≤ ((2 * K).toNNReal : ℝ) := NNReal.coe_le_coe.2 (Finset.sup_le fun k _ ↦ by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ h2K, Real.norm_eq_abs]
        exact abs_sub_le_two_mul hK _ _ ω)
    _ = 2 * K := Real.coe_toNNReal _ h2K

theorem measurable_maxIncr (hM : ∀ t, Measurable (M t)) (s t : ℝ≥0) (n : ℕ) :
    Measurable (maxIncr M s t n) := by
  refine measurable_coe_nnreal_real.comp ?_
  induction range n using Finset.induction_on with
  | empty => simp
  | insert k S _ ih =>
    simp_rw [sup_insert]
    exact (((hM _).sub (hM _)).nnnorm).sup ih

/-- **The largest increment tends to `0` along every path**: uniform continuity of the
continuous path on the compact `[s, t]` (`ItoFormulaAdapted.eventually_abs_sub_unifPart_lt`). -/
theorem tendsto_maxIncr (hcont : ∀ ω, Continuous fun t ↦ M t ω) (s t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n ↦ maxIncr M s t n ω) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha ↦ .of_forall fun n ↦ ha.trans_le (maxIncr_nonneg s t n ω),
    fun ε hε ↦ ?_⟩
  filter_upwards [ItoFormulaAdapted.eventually_abs_sub_unifPart_lt (t - s)
    ((hcont ω).comp (continuous_const.add continuous_id :
      Continuous fun r : ℝ≥0 ↦ s + r)).continuousOn (half_pos hε)]
    with n hn
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  have hε2 : 0 ≤ ε / 2 := (half_pos hε).le
  calc maxIncr M s t n ω ≤ ((ε / 2).toNNReal : ℝ) := NNReal.coe_le_coe.2 (Finset.sup_le fun k hk ↦ by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hε2, Real.norm_eq_abs]
        exact (hn k (mem_range.1 hk)).le)
    _ = ε / 2 := Real.coe_toNNReal _ hε2

/-- Every positive moment of the largest increment tends to `0` (dominated convergence, with the
constant bound `(2K)ᵖ`). -/
theorem tendsto_integral_maxIncr_pow [IsProbabilityMeasure P] (hM : Martingale M 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (hcont : ∀ ω, Continuous fun t ↦ M t ω) (s t : ℝ≥0) {p : ℕ}
    (hp : p ≠ 0) : Tendsto (fun n ↦ ∫ ω, maxIncr M s t n ω ^ p ∂P) atTop (𝓝 0) := by
  have hb (n : ℕ) : ∀ᵐ ω ∂P, ‖maxIncr M s t n ω ^ p‖ ≤ (2 * K) ^ p := .of_forall fun ω ↦ by
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (maxIncr_nonneg s t n ω)]
    exact pow_le_pow_left₀ (maxIncr_nonneg s t n ω) (maxIncr_le hK s t n ω) p
  have h := tendsto_integral_of_dominated_convergence (fun _ ↦ (2 * K) ^ p)
    (fun n ↦ ((measurable_maxIncr (fun t ↦ ((hM.stronglyAdapted t).mono (𝓕.le t)).measurable)
      s t n).pow_const p).aestronglyMeasurable) (integrable_const _) hb
    (.of_forall fun ω ↦ (tendsto_maxIncr hcont s t ω).pow p)
  simpa [zero_pow hp] using h

/-! ### The limits -/

section Limits

variable [IsProbabilityMeasure P] (hM : Martingale M 𝓕 P) (hK : ∀ t ω, |M t ω| ≤ K)
  (hcont : ∀ ω, Continuous fun t ↦ M t ω) {s t : ℝ≥0} (hst : s ≤ t)
include hM hK hcont hst

/-- **The quadratic sums of `M` converge to `t − s` in `L²(P)`.** For a bounded martingale `M`
with continuous paths whose square compensated by `t` is again a martingale, along the uniform
partition of `[s, t]`:

  `E[(∑_{k<n} (M_{tₖ₊₁} − M_{tₖ})² − (t − s))²] → 0`.

From the bound `integral_sq_sum_centred_le` with `δ = maxIncr`, whose moments vanish in the
limit (`tendsto_integral_maxIncr_pow`), and cell length `(t − s)/n`. -/
theorem tendsto_integral_sq_sum_sub (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P) :
    Tendsto (fun n : ℕ ↦ ∫ ω, (∑ k ∈ range n, (M (unifPartIcc s t n (k + 1)) ω
        - M (unifPartIcc s t n k) ω) ^ 2 - ((t : ℝ) - s)) ^ 2 ∂P) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ ↦ 4 * ∫ ω, maxIncr M s t n ω ^ 4 ∂P
      + 4 * ((t : ℝ) - s) * ∫ ω, maxIncr M s t n ω ^ 2 ∂P
      + 4 * (((t : ℝ) - s) / n) * ((t : ℝ) - s)) atTop (𝓝 0) := by
    simpa using (((tendsto_integral_maxIncr_pow hM hK hcont s t four_ne_zero).const_mul 4).add
      ((tendsto_integral_maxIncr_pow hM hK hcont s t two_ne_zero).const_mul
        (4 * ((t : ℝ) - s)))).add
      (((tendsto_const_div_atTop_nhds_zero_nat ((t : ℝ) - s)).const_mul 4).mul_const
        ((t : ℝ) - s))
  refine squeeze_zero' (.of_forall fun n ↦ integral_nonneg fun ω ↦ sq_nonneg _) ?_ hg
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hL : ((unifPartIcc s t n n : ℝ) - unifPartIcc s t n 0) = (t : ℝ) - s := by
    rw [unifPartIcc_self hst hn, unifPartIcc_zero]
  have hb := integral_sq_sum_centred_le (P := P) hM hM2 hK (unifPartIcc_mono s t n) n
    (h := ((t : ℝ) - s) / n) (fun k _ ↦ (unifPartIcc_succ_sub hst n k).le)
    (measurable_maxIncr (fun t ↦ ((hM.stronglyAdapted t).mono (𝓕.le t)).measurable) s t n)
    (maxIncr_nonneg s t n) (maxIncr_le hK s t n) (fun ω k hk ↦ abs_le_maxIncr s t hk ω)
  rw [hL] at hb
  refine le_of_eq_of_le (integral_congr_ae (.of_forall fun ω ↦ ?_)) hb
  simp only [sum_sub_distrib, sum_range_sub (fun k ↦ (unifPartIcc s t n k : ℝ)), hL]

/-- **The cubic sums vanish in `L¹(P)`**: `∑_{k<n} E|M_{tₖ₊₁} − M_{tₖ}|³ → 0` along the uniform
partition of `[s, t]` (`sum_integral_abs_cube_le` with `δ = maxIncr`, and
`tendsto_integral_sq_sum_sub`). -/
theorem tendsto_sum_integral_abs_cube
    (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ range n, ∫ ω, |M (unifPartIcc s t n (k + 1)) ω
        - M (unifPartIcc s t n k) ω| ^ 3 ∂P) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ ↦ (∫ ω, maxIncr M s t n ω ^ 2 ∂P + ∫ ω, (∑ k ∈ range n,
      (M (unifPartIcc s t n (k + 1)) ω - M (unifPartIcc s t n k) ω) ^ 2 - ((t : ℝ) - s)) ^ 2 ∂P)
        / 2 + ((t : ℝ) - s) * ∫ ω, maxIncr M s t n ω ^ 1 ∂P) atTop (𝓝 0) := by
    simpa using ((((tendsto_integral_maxIncr_pow hM hK hcont s t two_ne_zero).add
      (tendsto_integral_sq_sum_sub hM hK hcont hst hM2)).div_const 2).add
      ((tendsto_integral_maxIncr_pow hM hK hcont s t one_ne_zero).const_mul ((t : ℝ) - s)))
  refine squeeze_zero' (.of_forall fun n ↦ sum_nonneg fun k _ ↦
    integral_nonneg fun ω ↦ by positivity) ?_ hg
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hL : ((unifPartIcc s t n n : ℝ) - unifPartIcc s t n 0) = (t : ℝ) - s := by
    rw [unifPartIcc_self hst hn, unifPartIcc_zero]
  have hb := sum_integral_abs_cube_le (P := P) hM hK (π := unifPartIcc s t n) n
    (measurable_maxIncr (fun t ↦ ((hM.stronglyAdapted t).mono (𝓕.le t)).measurable) s t n)
    (maxIncr_nonneg s t n) (maxIncr_le hK s t n) (fun ω k hk ↦ abs_le_maxIncr s t hk ω)
  rw [hL] at hb
  refine hb.trans_eq ?_
  simp only [pow_one, sum_sub_distrib, sum_range_sub (fun k ↦ (unifPartIcc s t n k : ℝ)), hL]

end Limits

end LevyQuadraticSums
end MathFin
