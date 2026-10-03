/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.AdaptedStochasticIntegralFreezing
public import MathFin.Foundations.FiniteMeasureCauchySchwarz
public import MathFin.Foundations.WeightedQuadraticVariation

/-! # Quadratic variation of an Itô process with adapted coefficients

Step B2 of the adapted-coefficient Itô formula
(`docs/specs/2026-07-05-adapted-ito-formula-design.md`, status of 2026-10-03). Let
`X = X₀ + A + σ●B`, with `σ` bounded, adapted and path-continuous and the drift path `A`
Lipschitz in time with one constant for every path, and let `w` be a bounded adapted weight with
continuous paths. Along the uniform partition `tₖ = kT/n` of `[0, T]`,

  `∑ₖ w(tₖ)(ΔXₖ)² → ∫₀ᵀ w σ² ds` in `L¹(μ)`.

`ItoProcessQV` has the unweighted statement for constant `σ`. Write `ΔMₖ` for the increment of
`M = σ●B` and `Dₖ = ΔMₖ − σ(tₖ)ΔBₖ` for its freezing defect (`AdaptedStochasticIntegralFreezing`).
Then `(ΔXₖ)² − σ(tₖ)²(ΔBₖ)² = (ΔAₖ)² + 2ΔAₖΔMₖ + 2DₖΔMₖ − Dₖ²`, which `abs_mul_sq_sub_le` turns
into a bound, and

* the drift part `∑ (ΔAₖ)²` is at most `Cₐ²T²/n`;
* the cross part `∑ 2ΔAₖΔMₖ` is `O(1/√n)` in `L¹`, since `‖ΔMₖ‖² ≤ C²T/n`
  (`norm_sq_increment_le`);
* the freezing part is at most `2√(∑‖Dₖ‖²)·√(C²T) + ∑‖Dₖ‖²` in `L¹`, by Cauchy–Schwarz, and
  `∑‖Dₖ‖² → 0` (`tendsto_sum_norm_sq_freezingDefect`);
* the frozen squares carry the weighted quadratic variation of `B` with weight `w σ²`
  (`tendsto_weighted_qv_process`).

The first three parts use only `|w| ≤ C_w`. The weight's adaptedness, and its continuity on every
path, enter only through the last, because `tendsto_weighted_qv_process` asks for them.

The limit is in `L¹`, where `ItoProcessQV` has `L²`: an `L²` bound on the freezing part would need
fourth moments of `σ●B`, which the tower does not have. The integrals are Bochner integrals, so the
statement has content when the increments of `A` are measurable, as they are for a drift
`∫₀ᵗ b ds`; the proof does not use this. With `A` measurable, `L¹` convergence gives convergence in
probability, which is what identifying a limit almost surely needs.

`X` only has to agree with `X₀ + A + σ●B` almost surely at each time of `[0, T]`, so any
modification qualifies.

## Main results

* `tendsto_weighted_qv_adapted` — the weighted statement above.
* `tendsto_qv_adapted` — `∑ₖ (ΔXₖ)² → ∫₀ᵀ σ² ds` in `L¹(μ)`, the case `w ≡ 1`.
* `norm_sq_increment_le` — the increment of `σ●B` over `(a, b]` has squared `L²` norm at most
  `C²·(b − a)`.
-/

@[expose] public section

namespace MathFin
namespace AdaptedQuadraticVariation

open MeasureTheory ProbabilityTheory Filter Topology
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralRiemannBridge
  ItoIntegralAgainstMartingale ItoIntegralBrownian QuadraticVariationL2
  AdaptedStochasticIntegralFreezing LpMulIsometry
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C)

/-! ### Tools: the partition and the pointwise split -/

/-- The cells of the uniform partition have length `T/n`. -/
theorem unifPart_succ_sub (n k : ℕ) :
    ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) / n := by
  push_cast [unifPart]
  ring

/-- **The pointwise split.** Write `m` for the increment of the martingale part and `D = m − s·b`
for its freezing defect against the frozen increment `s·b`. Then `m² − (s·b)² = 2D·m − D²`, so a
drift increment `|a| ≤ ε` and a weight `|w| ≤ c` give
`|w(a + m)² − w s² b²| ≤ c(ε² + 2ε|m| + 2|D·m| + D²)`. -/
theorem abs_mul_sq_sub_le {w a m s b c ε : ℝ} (hw : |w| ≤ c) (ha : |a| ≤ ε) :
    |w * (a + m) ^ 2 - w * s ^ 2 * b ^ 2|
      ≤ c * (ε ^ 2 + 2 * ε * |m| + 2 * |(m - s * b) * m| + (m - s * b) ^ 2) := by
  have ha2 : a ^ 2 ≤ ε ^ 2 := sq_le_sq.2 (ha.trans (le_abs_self ε))
  have ham : |a * m| ≤ ε * |m| :=
    (abs_mul a m).trans_le (mul_le_mul_of_nonneg_right ha (abs_nonneg m))
  rw [show w * (a + m) ^ 2 - w * s ^ 2 * b ^ 2
      = w * (a ^ 2 + 2 * (a * m) + 2 * ((m - s * b) * m) - (m - s * b) ^ 2) by ring, abs_mul]
  refine mul_le_mul hw (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg _) ((abs_nonneg w).trans hw) <;>
    linarith [neg_abs_le (a * m), le_abs_self (a * m), neg_abs_le ((m - s * b) * m),
      le_abs_self ((m - s * b) * m), sq_nonneg a, sq_nonneg (m - s * b), sq_nonneg ε]

/-! ### The Brownian term, in `L¹` -/

include hB in
/-- The Brownian term `∑ₖ v(tₖ)(ΔBₖ)² − ∫₀ᵀ v ds` of a bounded measurable weight with continuous
paths is in `L²`. -/
theorem memLp_weighted_qv_sub {v : ℝ≥0 → Ω → ℝ} (hv_meas : ∀ s, Measurable (v s))
    (hv_cont : ∀ ω, Continuous fun s ↦ v s ω) {Cv : ℝ} (hv_bdd : ∀ s ω, |v s ω| ≤ Cv) (n : ℕ) :
    MemLp (fun ω ↦ ∑ k ∈ Finset.range n,
        v (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
      - ∫ s in Set.Ioc 0 T, v s ω ∂ItoIntegralL2.timeMeasure) 2 μ := by
  have hsum : MemLp (fun ω ↦ ∑ k ∈ Finset.range n,
      v (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) 2 μ := by
    refine memLp_finsetSum _ fun k _ ↦ ?_
    have hZ : MemLp (fun ω ↦ (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) 2 μ := by
      simpa using memLp_increment_sq_centered_two hB (unifPart T n k) (unifPart T n (k + 1)) 0
    exact hZ.mul' (memLp_top_of_bound (hv_meas _).aestronglyMeasurable Cv
      (ae_of_all _ fun ω ↦ hv_bdd _ ω))
  exact hsum.sub (memLp_pathIntegral_process hv_meas hv_cont
    ((abs_nonneg _).trans (hv_bdd 0 (nonempty_of_isProbabilityMeasure μ).some)) hv_bdd T)

include hB in
/-- **The weighted quadratic variation of `B`, in `L¹`**: `tendsto_weighted_qv_process` read
through `∫|f| ≤ √(∫f²)`. -/
theorem tendsto_integral_abs_weighted_qv {v : ℝ≥0 → Ω → ℝ}
    (hv_adap : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (v s))
    (hv_cont : ∀ ω, Continuous fun s ↦ v s ω) {Cv : ℝ} (hv_bdd : ∀ s ω, |v s ω| ≤ Cv) :
    Tendsto (fun n : ℕ ↦ ∫ ω, |∑ k ∈ Finset.range n,
        v (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
      - ∫ s in Set.Ioc 0 T, v s ω ∂ItoIntegralL2.timeMeasure| ∂μ) atTop (𝓝 0) :=
  squeeze_zero (fun n ↦ integral_nonneg fun ω ↦ abs_nonneg _)
    (fun n ↦ integral_abs_le_sqrt_integral_sq (memLp_weighted_qv_sub hB T
      (fun s ↦ ((hv_adap s).mono ((natFiltration hBmeas).le s)).measurable) hv_cont hv_bdd n))
    (by simpa using (tendsto_weighted_qv_process hB hBmeas
      (fun s ↦ adaptedAt_of_measurable_natural hBmeas (hv_adap s).measurable) hv_cont
      ((abs_nonneg _).trans (hv_bdd 0 (nonempty_of_isProbabilityMeasure μ).some)) hv_bdd T).sqrt)

/-! ### The increments of `M = σ●B` -/

/-- **The increment of `M = σ●B` over `(a, b]` has squared `L²` norm at most `C²·(b − a)`.** By the
bracket identity the squared norm is `⟨M⟩((a,b] × Ω)`, the integral of `σ²` over the band. -/
theorem norm_sq_increment_le {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) :
    ‖itoProcessCLM hB T b hBmeas (processToLp T hBmeas hadap hcont hbdd)
      - itoProcessCLM hB T a hBmeas (processToLp T hBmeas hadap hcont hbdd)‖ ^ 2
      ≤ C ^ 2 * ((b : ℝ) - a) := by
  rw [norm_sq_increment_eq_bracket (hB := hB) T hBmeas _ hab hbT]
  have hS : MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      (Set.Ioc a b ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod a b MeasurableSet.univ
  -- the density `σ²` is at most `C²`
  have hbound : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
      ‖(processToLp (μ := μ) T hBmeas hadap hcont hbdd : ℝ≥0 × Ω → ℝ) z‖ₑ ^ 2
        ≤ ENNReal.ofReal (C ^ 2) := by
    filter_upwards [processToLp_coeFn (μ := μ) T hBmeas hadap hcont hbdd] with z hz
    rw [hz, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (hbdd z.1 z.2) 2)
  -- the trim measure of the band is its length
  have htrim : trimMeasure_T (μ := μ) T hBmeas (Set.Ioc a b ×ˢ (Set.univ : Set Ω))
      = ENNReal.ofReal ((b : ℝ) - a) := by
    unfold trimMeasure_T
    rw [trim_measurableSet_eq _ hS, Measure.prod_prod, measure_univ, mul_one, timeMeasure_T,
      Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_left.2 (Set.Ioc_subset_Ioc zero_le hbT), timeMeasure_Ioc]
  have hle : bracketMeasure (μ := μ) T hBmeas (processToLp T hBmeas hadap hcont hbdd)
      (Set.Ioc a b ×ˢ (Set.univ : Set Ω)) ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal ((b : ℝ) - a) := by
    rw [bracketMeasure_eq, sqWeight, withDensity_apply _ hS, ← htrim, ← setLIntegral_const]
    exact setLIntegral_mono_ae measurable_const.aemeasurable (by
      filter_upwards [hbound] with z hz _ using hz)
  exact (ENNReal.toReal_mono (by finiteness) hle).trans_eq (by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg C),
      ENNReal.toReal_ofReal (sub_nonneg.2 (NNReal.coe_le_coe.2 hab))])

/-- The increment `ΔMₖ` of `M = σ●B` over the `k`-th cell of the uniform partition. -/
noncomputable def cellIncrement (n k : ℕ) : Lp ℝ 2 μ :=
  itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas (processToLp T hBmeas hadap hcont hbdd)
    - itoProcessCLM hB T (unifPart T n k) hBmeas (processToLp T hBmeas hadap hcont hbdd)

/-- The increment over a cell has squared `L²` norm at most `C²·T/n`. -/
theorem norm_sq_cellIncrement_le {n k : ℕ} (hk : k < n) :
    ‖cellIncrement hB T hBmeas hadap hcont hbdd n k‖ ^ 2 ≤ C ^ 2 * (T / n) := by
  simpa only [cellIncrement, unifPart_succ_sub] using norm_sq_increment_le hB T hBmeas hadap hcont
    hbdd (unifPart_mono T n (Nat.le_succ k)) (unifPart_le_T hk)

/-! ### The quadratic variation -/

section QV

variable {X A : ℝ≥0 → Ω → ℝ} {X₀ : Ω → ℝ} {Ca : ℝ}
  (hA : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → ∀ ω, |A t ω - A s ω| ≤ Ca * ((t : ℝ) - s))
  (hX : ∀ t ≤ T, X t =ᵐ[μ] fun ω ↦ X₀ ω + A t ω
    + itoProcessCLM hB T t hBmeas (processToLp T hBmeas hadap hcont hbdd) ω)

section Weighted

variable {w : ℝ≥0 → Ω → ℝ}
  (hw_adap : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (w s))
  (hw_cont : ∀ ω, Continuous fun s ↦ w s ω) {Cw : ℝ} (hw_bdd : ∀ s ω, |w s ω| ≤ Cw)

omit mΩ in
include hbdd hw_bdd in
/-- The weight `w σ²` of the Brownian term is bounded by `C_w C²`. -/
theorem abs_mul_sq_le (s : ℝ≥0) (ω : Ω) : |w s ω * σ s ω ^ 2| ≤ Cw * C ^ 2 := by
  rw [abs_mul, abs_pow]
  exact mul_le_mul (hw_bdd s ω) (pow_le_pow_left₀ (abs_nonneg _) (hbdd s ω) 2) (sq_nonneg _)
    ((abs_nonneg _).trans (hw_bdd s ω))

include hA hX hw_bdd in
/-- **The pathwise bound.** Almost surely, the weighted quadratic-variation error of `X` is at most
the drift, cross and freezing contributions of the cells plus the Brownian term. -/
theorem ae_abs_weighted_qv_sub_le (n : ℕ) : ∀ᵐ ω ∂μ,
    |∑ k ∈ Finset.range n, w (unifPart T n k) ω
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2
        - ∫ s in Set.Ioc 0 T, w s ω * σ s ω ^ 2 ∂ItoIntegralL2.timeMeasure|
      ≤ ∑ k ∈ (Finset.range n).attach, Cw * ((Ca * (T / n)) ^ 2
            + 2 * (Ca * (T / n)) * |cellIncrement hB T hBmeas hadap hcont hbdd n k ω|
            + 2 * |freezingDefect hB T hBmeas hadap hcont hbdd n k ω
                * cellIncrement hB T hBmeas hadap hcont hbdd n k ω|
            + freezingDefect hB T hBmeas hadap hcont hbdd n k ω ^ 2)
        + |∑ k ∈ Finset.range n, w (unifPart T n k) ω * σ (unifPart T n k) ω ^ 2
              * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ∫ s in Set.Ioc 0 T, w s ω * σ s ω ^ 2 ∂ItoIntegralL2.timeMeasure| := by
  have hXn : ∀ᵐ ω ∂μ, ∀ j : ℕ, j ≤ n → X (unifPart T n j) ω = X₀ ω + A (unifPart T n j) ω
      + itoProcessCLM hB T (unifPart T n j) hBmeas (processToLp T hBmeas hadap hcont hbdd) ω := by
    refine ae_all_iff.2 fun j ↦ ?_
    by_cases hj : j ≤ n
    · filter_upwards [hX _ (unifPart_le_T hj)] with ω hω _ using hω
    · exact ae_of_all _ fun ω h ↦ absurd h hj
  have hΔ : ∀ᵐ ω ∂μ, ∀ k : ℕ, cellIncrement hB T hBmeas hadap hcont hbdd n k ω
      = itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas (processToLp T hBmeas hadap hcont hbdd) ω
        - itoProcessCLM hB T (unifPart T n k) hBmeas (processToLp T hBmeas hadap hcont hbdd) ω :=
    ae_all_iff.2 fun k ↦ Lp.coeFn_sub _ _
  have hD := ae_all_iff.2 fun k ↦ coeFn_freezingDefect hB T hBmeas hadap hcont hbdd n k
  filter_upwards [hXn, hΔ, hD] with ω hXω hΔω hDω
  set q : ℕ → ℝ := fun k ↦ w (unifPart T n k) ω
    * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2
  set r : ℕ → ℝ := fun k ↦ w (unifPart T n k) ω * σ (unifPart T n k) ω ^ 2
    * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
  rw [show ∀ x : ℝ, ∑ k ∈ Finset.range n, q k - x
      = ∑ k ∈ (Finset.range n).attach, (q k - r k) + (∑ k ∈ Finset.range n, r k - x) from
    fun x ↦ by
      rw [Finset.sum_sub_distrib, Finset.sum_attach (Finset.range n) q,
        Finset.sum_attach (Finset.range n) r]
      ring]
  refine (abs_add_le _ _).trans (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun k _ ↦ ?_)) le_rfl)
  have hk := Finset.mem_range.mp k.2
  have ha : |A (unifPart T n (k + 1)) ω - A (unifPart T n k) ω| ≤ Ca * (T / n) := by
    simpa only [unifPart_succ_sub] using hA (unifPart_mono T n (Nat.le_succ k)) ω
  rw [hΔω, hDω]
  refine Eq.trans_le ?_ (abs_mul_sq_sub_le (hw_bdd (unifPart T n k) ω) ha)
  simp only [q, r]
  rw [hXω (k + 1) hk, hXω k hk.le]
  congr 1
  ring

include hA hX hw_adap hw_cont hw_bdd in
/-- **The `L¹` bound.** Integrating the pathwise bound, with Cauchy–Schwarz on each cell and then
across the cells: `C_w` times the drift and cross parts `(CₐT)²/n + 2CₐT·√(C²T/n)` and the
freezing part `2√(∑‖Dₖ‖²)·√(C²T) + ∑‖Dₖ‖²`, plus the `L¹` norm of the Brownian term. -/
theorem integral_abs_weighted_qv_sub_le {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, |∑ k ∈ Finset.range n, w (unifPart T n k) ω
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2
        - ∫ s in Set.Ioc 0 T, w s ω * σ s ω ^ 2 ∂ItoIntegralL2.timeMeasure| ∂μ
      ≤ Cw * ((Ca * T) ^ 2 / n + 2 * (Ca * T) * √(C ^ 2 * (T / n))
          + (2 * (√(∑ k ∈ (Finset.range n).attach,
                ‖freezingDefect hB T hBmeas hadap hcont hbdd n k‖ ^ 2) * √(C ^ 2 * T))
            + ∑ k ∈ (Finset.range n).attach, ‖freezingDefect hB T hBmeas hadap hcont hbdd n k‖ ^ 2))
        + ∫ ω, |∑ k ∈ Finset.range n, w (unifPart T n k) ω * σ (unifPart T n k) ω ^ 2
              * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ∫ s in Set.Ioc 0 T, w s ω * σ s ω ^ 2 ∂ItoIntegralL2.timeMeasure| ∂μ := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hCw : 0 ≤ Cw := (abs_nonneg _).trans (hw_bdd 0 ω₀)
  have hCa : 0 ≤ Ca := by simpa using (abs_nonneg _).trans (hA (zero_le_one' ℝ≥0) ω₀)
  have hbr_int := ((memLp_weighted_qv_sub hB T (v := fun s ω ↦ w s ω * σ s ω ^ 2)
    (fun s ↦ (((hw_adap s).mul ((hadap s).pow 2)).mono ((natFiltration hBmeas).le s)).measurable)
    (fun ω ↦ (hw_cont ω).mul ((hcont ω).pow 2)) (abs_mul_sq_le hbdd hw_bdd) n).integrable
    one_le_two).abs
  have hrate : (n : ℝ) * ((Ca * (T / n)) ^ 2 + 2 * (Ca * (T / n)) * √(C ^ 2 * (T / n)))
      = (Ca * T) ^ 2 / n + 2 * (Ca * T) * √(C ^ 2 * (T / n)) := by
    have hnT : (n : ℝ) * (T / n) = T := by field_simp
    linear_combination (Ca ^ 2 * (T / n) + 2 * Ca * √(C ^ 2 * (T / n))) * hnT
  set ε : ℝ := Ca * (T / n)
  set q : ℝ := C ^ 2 * (T / n) with hq
  set Δ := cellIncrement hB T hBmeas hadap hcont hbdd n
  set D := freezingDefect hB T hBmeas hadap hcont hbdd n
  have hε0 : 0 ≤ ε := by positivity
  have hΔ_le (k : {x // x ∈ Finset.range n}) : ‖Δ k‖ ^ 2 ≤ q :=
    norm_sq_cellIncrement_le hB T hBmeas hadap hcont hbdd (Finset.mem_range.mp k.2)
  have hΔi (k : ℕ) : Integrable (fun ω ↦ |Δ k ω|) μ :=
    ((Lp.memLp (Δ k)).integrable one_le_two).abs
  have hDΔi (k : {x // x ∈ Finset.range n}) : Integrable (fun ω ↦ |D k ω * Δ k ω|) μ :=
    ((Lp.memLp (D k)).integrable_mul (Lp.memLp (Δ k))).abs
  have hi1 (k : {x // x ∈ Finset.range n}) :
      Integrable (fun ω ↦ ε ^ 2 + 2 * ε * |Δ k ω|) μ :=
    (integrable_const _).add ((hΔi k).const_mul _)
  have hi2 (k : {x // x ∈ Finset.range n}) :
      Integrable (fun ω ↦ ε ^ 2 + 2 * ε * |Δ k ω| + 2 * |D k ω * Δ k ω|) μ :=
    (hi1 k).add ((hDΔi k).const_mul _)
  have hcell_i (k : {x // x ∈ Finset.range n}) : Integrable (fun ω ↦
      Cw * (ε ^ 2 + 2 * ε * |Δ k ω| + 2 * |D k ω * Δ k ω| + D k ω ^ 2)) μ :=
    ((hi2 k).add (Lp.memLp (D k)).integrable_sq).const_mul _
  -- each cell: Cauchy–Schwarz in expectation
  have hcell (k : {x // x ∈ Finset.range n}) :
      ∫ ω, Cw * (ε ^ 2 + 2 * ε * |Δ k ω| + 2 * |D k ω * Δ k ω| + D k ω ^ 2) ∂μ
        ≤ Cw * (ε ^ 2 + 2 * ε * √q + (2 * (‖D k‖ * ‖Δ k‖) + ‖D k‖ ^ 2)) := by
    have h1 : ∫ ω, |Δ k ω| ∂μ ≤ √q := (integral_abs_le_sqrt_integral_sq (Lp.memLp _)).trans (by
      rw [← lp_two_norm_sq]; exact Real.sqrt_le_sqrt (hΔ_le k))
    have h2 : ∫ ω, |D k ω * Δ k ω| ∂μ ≤ ‖D k‖ * ‖Δ k‖ :=
      (integral_abs_mul_le_sqrt_mul_sqrt (Lp.memLp _) (Lp.memLp _)).trans_eq (by
        rw [← lp_two_norm_sq, ← lp_two_norm_sq, Real.sqrt_sq (norm_nonneg _),
          Real.sqrt_sq (norm_nonneg _)])
    rw [integral_const_mul, integral_add (hi2 k) (Lp.memLp (D k)).integrable_sq,
      integral_add (hi1 k) ((hDΔi k).const_mul _), integral_add (integrable_const _)
        ((hΔi k).const_mul _), integral_const, integral_const_mul, integral_const_mul,
      ← lp_two_norm_sq, probReal_univ, one_smul]
    refine mul_le_mul_of_nonneg_left ?_ hCw
    linarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * ε)]
  -- across the cells: Cauchy–Schwarz for sums, with `∑ ‖ΔMₖ‖² ≤ C²T`
  have hΔsq : ∑ k ∈ (Finset.range n).attach, ‖Δ k‖ ^ 2 ≤ C ^ 2 * T :=
    (Finset.sum_le_card_nsmul _ _ _ fun k _ ↦ hΔ_le k).trans_eq (by
      rw [Finset.card_attach, Finset.card_range, nsmul_eq_mul, hq]; field_simp)
  have hDΔ : ∑ k ∈ (Finset.range n).attach, ‖D k‖ * ‖Δ k‖
      ≤ √(∑ k ∈ (Finset.range n).attach, ‖D k‖ ^ 2) * √(C ^ 2 * T) :=
    (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hΔsq) (Real.sqrt_nonneg _))
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _)
    ((integrable_finsetSum _ fun k _ ↦ hcell_i k).add hbr_int)
    (ae_abs_weighted_qv_sub_le hB T hBmeas hadap hcont hbdd hA hX hw_bdd n)).trans ?_
  rw [integral_add' (integrable_finsetSum _ fun k _ ↦ hcell_i k) hbr_int,
    integral_finsetSum _ fun k _ ↦ hcell_i k]
  gcongr ?_ + _
  calc _ ≤ ∑ k ∈ (Finset.range n).attach,
        Cw * (ε ^ 2 + 2 * ε * √q + (2 * (‖D k‖ * ‖Δ k‖) + ‖D k‖ ^ 2)) :=
      Finset.sum_le_sum fun k _ ↦ hcell k
    _ = Cw * (n * (ε ^ 2 + 2 * ε * √q) + (2 * ∑ k ∈ (Finset.range n).attach, ‖D k‖ * ‖Δ k‖
          + ∑ k ∈ (Finset.range n).attach, ‖D k‖ ^ 2)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_attach,
        Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by rw [hrate]; gcongr

include hA hX hw_adap hw_cont hw_bdd in
/-- **Quadratic variation of an Itô process with adapted coefficients, weighted.** Let
`X = X₀ + A + σ●B`, with `σ` bounded, adapted and path-continuous and the drift path `A`
`Cₐ`-Lipschitz in time, and let `w` be a bounded adapted weight with continuous paths. Along the
uniform partition of `[0, T]`, `∑ₖ w(tₖ)(ΔXₖ)² → ∫₀ᵀ w σ² ds` in `L¹(μ)`.

Each `(ΔXₖ)²` splits (`abs_mul_sq_sub_le`) into a drift part, at most `Cₐ²(T/n)²`; a cross part
`2ΔAₖΔMₖ`, at most `2Cₐ(T/n)|ΔMₖ|`; the freezing part `2DₖΔMₖ − Dₖ²` for the defect
`Dₖ = ΔMₖ − σ(tₖ)ΔBₖ`; and the frozen square `σ(tₖ)²(ΔBₖ)²`. Summed over the cells, the drift
part is `O(1/n)` and the cross part `O(1/√n)` in `L¹`, since `‖ΔMₖ‖² ≤ C²T/n`; the freezing part
tends to `0` because `∑ₖ ‖Dₖ‖² → 0` (`tendsto_sum_norm_sq_freezingDefect`); the frozen squares
carry the weighted quadratic variation of `B` with weight `w σ²` (`tendsto_weighted_qv_process`).
-/
theorem tendsto_weighted_qv_adapted :
    Tendsto (fun n : ℕ ↦ ∫ ω, |∑ k ∈ Finset.range n, w (unifPart T n k) ω
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2
        - ∫ s in Set.Ioc 0 T, w s ω * σ s ω ^ 2 ∂ItoIntegralL2.timeMeasure| ∂μ) atTop (𝓝 0) := by
  -- the drift and cross terms
  have hdc := (tendsto_const_div_atTop_nhds_zero_nat ((Ca * T) ^ 2)).add
    (((tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).const_mul (C ^ 2)).sqrt.const_mul
      (2 * (Ca * T)))
  -- the freezing term
  have hd := tendsto_sum_norm_sq_freezingDefect hB T hBmeas hadap hcont hbdd
  have hfr := ((hd.sqrt.mul_const (√(C ^ 2 * T))).const_mul 2).add hd
  -- the Brownian term
  have hbr := tendsto_integral_abs_weighted_qv hB T hBmeas (v := fun s ω ↦ w s ω * σ s ω ^ 2)
    (fun s ↦ (hw_adap s).mul ((hadap s).pow 2)) (fun ω ↦ (hw_cont ω).mul ((hcont ω).pow 2))
    (abs_mul_sq_le hbdd hw_bdd)
  have hlim := ((hdc.add hfr).const_mul Cw).add hbr
  simp only [mul_zero, Real.sqrt_zero, zero_mul, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun n ↦ integral_nonneg fun ω ↦ abs_nonneg _) ?_ hlim
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact integral_abs_weighted_qv_sub_le hB T hBmeas hadap hcont hbdd hA hX hw_adap hw_cont hw_bdd hn

end Weighted

include hA hX in
/-- **Quadratic variation of an Itô process with adapted coefficients.** For
`X = X₀ + A + σ●B` with `σ` bounded, adapted and path-continuous and the drift path `A`
`Cₐ`-Lipschitz in time, `∑ₖ (ΔXₖ)² → ∫₀ᵀ σ² ds` in `L¹(μ)` along the uniform partition of
`[0, T]`: the drift contributes nothing, and the martingale part contributes its bracket. The
`w ≡ 1` case of `tendsto_weighted_qv_adapted`. -/
theorem tendsto_qv_adapted :
    Tendsto (fun n : ℕ ↦ ∫ ω, |∑ k ∈ Finset.range n,
          (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2
        - ∫ s in Set.Ioc 0 T, σ s ω ^ 2 ∂ItoIntegralL2.timeMeasure| ∂μ) atTop (𝓝 0) := by
  simpa using tendsto_weighted_qv_adapted hB T hBmeas hadap hcont hbdd hA hX
    (w := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
    (Cw := 1) fun _ _ ↦ abs_one.le

end QV

end AdaptedQuadraticVariation

end MathFin
