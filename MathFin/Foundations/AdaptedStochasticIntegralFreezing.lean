/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralRiemannBridgeAdapted
public import MathFin.Foundations.ItoIntegralAgainstMartingale
public import MathFin.Foundations.ItoIntegralCovariation

/-! # Freezing an adapted integrand on a partition

Step B1 of the adapted-coefficient Itô formula
(`docs/specs/2026-07-05-adapted-ito-formula-design.md`, status of 2026-10-03). Take a bounded
adapted `σ` with continuous paths and the Itô integral process `M = σ●B` (`itoProcessCLM` of
`processToLp σ`). On each cell `(tₖ, tₖ₊₁]` of the uniform partition `tₖ = kT/n`, freeze the
integrand at the left end, replacing the increment `ΔMₖ` by `σ(tₖ)·ΔBₖ`. The
defects

  `Dₖ = ΔMₖ − σ(tₖ)·ΔBₖ`

are small in the sense the quadratic variation needs: `∑ₖ ‖Dₖ‖²_{L²} → 0`
(`tendsto_sum_norm_sq_freezingDefect`).

The proof is short because its pieces exist. Each `Dₖ` is the Itô integral of
`𝟙_{(tₖ,tₖ₊₁]}·(σ − σ(tₖ))` (`freezingDefect_eq`: the band identity minus the elementary integral),
so defects on distinct cells are orthogonal (`inner_freezingDefect_eq_zero`: disjoint supports, and
an isometry preserves inner products). By Pythagoras the sum of their squared norms is the squared
norm of their sum. That sum telescopes to the error of the frozen Riemann–Itô sum,
`∫σ dB − ∑ σ(tₖ)·ΔBₖ` (`sum_freezingDefect`), which tends to `0` by
`itoIntegralCLM_T_of_bdd_adapted_cont`.

## Result

* `tendsto_sum_norm_sq_freezingDefect` — `∑ₖ ‖ΔMₖ − σ(tₖ)·ΔBₖ‖² → 0`.
* `coeFn_freezingDefect` — the defect, pointwise.
* `inner_freezingDefect_eq_zero`, `sum_freezingDefect` — orthogonality and telescoping.
* `norm_sum_sq_of_pairwise_inner_eq_zero` — Pythagoras for a finite orthogonal family, from
  `OrthogonalFamily.norm_sum`.
-/

@[expose] public section

namespace MathFin
namespace AdaptedStochasticIntegralFreezing

open MeasureTheory ProbabilityTheory Filter Topology
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralRiemannBridge
  ItoIntegralAgainstMartingale ItoIntegralBrownian ItoIntegralCovariation QuadraticVariationL2
open scoped NNReal ENNReal InnerProductSpace

/-! ### Pythagoras for a finite orthogonal family -/

section Pythagoras

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}

/-- **Pythagoras for a finite family**: the squared norm of a sum of pairwise orthogonal vectors is
the sum of their squared norms. `OrthogonalFamily.norm_sum`, for the lines the vectors span. -/
theorem norm_sum_sq_of_pairwise_inner_eq_zero (s : Finset ι) (f : ι → E)
    (h : Pairwise fun i j ↦ ⟪f i, f j⟫_ℝ = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hV : OrthogonalFamily ℝ (fun i ↦ ↥(ℝ ∙ f i)) fun i ↦ (ℝ ∙ f i).subtypeₗᵢ :=
    orthogonalFamily_iff_pairwise.2 fun i j hij ↦ Submodule.isOrtho_span.2 fun u hu v hv ↦ by
      rw [Set.mem_singleton_iff.1 hu, Set.mem_singleton_iff.1 hv]
      exact h hij
  simpa using hV.norm_sum (fun i ↦ ⟨f i, Submodule.mem_span_singleton_self (f i)⟩) s

end Pythagoras

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The cells of the uniform partition -/

section Cells

variable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C)

/-- The frozen step on the `k`-th cell of the uniform partition, `σ(tₖ)·𝟙_{(tₖ, tₖ₊₁]}`: the
summands of `stepσ`. -/
noncomputable def cellStep (n : ℕ) (k : {x // x ∈ Finset.range n}) : TBoundedSP T hBmeas :=
  stepSP hBmeas (a := unifPart T n k.1) (b := unifPart T n (k.1 + 1))
    (unifPart_mono T n (Nat.le_succ k.1)) (unifPart_le_T (Finset.mem_range.mp k.2))
    (φ := σ (unifPart T n k.1)) (hadap (unifPart T n k.1)).measurable
    (M := C) (fun ω ↦ hbdd (unifPart T n k.1) ω)

theorem stepσ_eq_sum_cellStep (n : ℕ) :
    stepσ hBmeas hadap hbdd T n = ∑ k ∈ (Finset.range n).attach, cellStep T hBmeas hadap hbdd n k :=
  rfl

/-- The frozen step is `σ(tₖ)` on its cell and `0` off it. -/
theorem uncurry_cellStep (n : ℕ) (k : {x // x ∈ Finset.range n}) (z : ℝ≥0 × Ω) :
    Function.uncurry ⇑(cellStep T hBmeas hadap hbdd n k).val z
      = (Set.Ioc (unifPart T n k.1) (unifPart T n (k.1 + 1))).indicator
          (fun _ ↦ σ (unifPart T n k.1) z.2) z.1 := by
  show ⇑(cellStep T hBmeas hadap hbdd n k).val z.1 z.2 = _
  rw [SimpleProcess.apply_eq]
  simp only [cellStep, stepSP]
  rw [Finsupp.sum_single_index (by simp)]
  simp

end Cells

/-! ### The freezing defect -/

section Freezing

variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C)

/-- The integrand of the freezing defect on the `k`-th cell, `𝟙_{(tₖ, tₖ₊₁]}·(σ − σ(tₖ))`, as a
class in the Itô-integrand space. -/
noncomputable def cellIntegrand (n : ℕ) (k : {x // x ∈ Finset.range n}) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  bandRestrict T (unifPart T n k.1) (unifPart T n (k.1 + 1)) hBmeas
      (processToLp T hBmeas hadap hcont hbdd)
    - simpleAssembly_T T hBmeas (cellStep T hBmeas hadap hbdd n k)

/-- **The freezing defect** on the `k`-th cell: the Itô integral of `cellIntegrand`, which is
`ΔMₖ − σ(tₖ)·ΔBₖ` for `M = σ●B` (`coeFn_freezingDefect`). -/
noncomputable def freezingDefect (n : ℕ) (k : {x // x ∈ Finset.range n}) : Lp ℝ 2 μ :=
  itoIntegralCLM_T hB T hBmeas (cellIntegrand T hBmeas hadap hcont hbdd n k)

/-- The cell integrand is `σ − σ(tₖ)` on its cell and `0` off it. -/
theorem coeFn_cellIntegrand (n : ℕ) (k : {x // x ∈ Finset.range n}) :
    ⇑(cellIntegrand (μ := μ) T hBmeas hadap hcont hbdd n k) =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
      fun z ↦ (Set.Ioc (unifPart T n k.1) (unifPart T n (k.1 + 1))).indicator (fun _ ↦ (1 : ℝ)) z.1
        * (σ z.1 z.2 - σ (unifPart T n k.1) z.2) := by
  filter_upwards [Lp.coeFn_sub (bandRestrict T (unifPart T n k.1) (unifPart T n (k.1 + 1)) hBmeas
      (processToLp T hBmeas hadap hcont hbdd))
      (simpleAssembly_T T hBmeas (cellStep T hBmeas hadap hbdd n k)),
    coeFn_bandRestrict T (unifPart T n k.1) (unifPart T n (k.1 + 1))
      (unifPart_mono T n (Nat.le_succ k.1)) hBmeas (processToLp T hBmeas hadap hcont hbdd),
    processToLp_coeFn T hBmeas hadap hcont hbdd,
    (memLp_uncurry_trim_T T hBmeas (cellStep T hBmeas hadap hbdd n k).val).coeFn_toLp]
    with z hsub hband hφ hstep
  rw [cellIntegrand, hsub, Pi.sub_apply, hband, hφ]
  rw [show (simpleAssembly_T T hBmeas (cellStep T hBmeas hadap hbdd n k) : ℝ≥0 × Ω → ℝ) z
      = Function.uncurry ⇑(cellStep T hBmeas hadap hbdd n k).val z from hstep, uncurry_cellStep]
  by_cases hz : z.1 ∈ Set.Ioc (unifPart T n k.1) (unifPart T n (k.1 + 1)) <;>
    simp [hz, Function.uncurry, mul_sub]

/-- **The defect is the increment of `M = σ●B` over the cell, minus its frozen value.** -/
theorem freezingDefect_eq (n : ℕ) (k : {x // x ∈ Finset.range n}) :
    freezingDefect hB T hBmeas hadap hcont hbdd n k
      = (itoProcessCLM hB T (unifPart T n (k.1 + 1)) hBmeas (processToLp T hBmeas hadap hcont hbdd)
          - itoProcessCLM hB T (unifPart T n k.1) hBmeas (processToLp T hBmeas hadap hcont hbdd))
        - itoIntegralCLM_T hB T hBmeas
            (simpleAssembly_T T hBmeas (cellStep T hBmeas hadap hbdd n k)) := by
  rw [freezingDefect, cellIntegrand, map_sub,
    itoIntegralCLM_T_bandRestrict (hB := hB) T hBmeas _ (unifPart_mono T n (Nat.le_succ k.1))
      (unifPart_le_T (Finset.mem_range.mp k.2))]

/-- **The freezing defect, pointwise**: `ΔMₖ − σ(tₖ)·ΔBₖ`, almost surely. -/
theorem coeFn_freezingDefect (n : ℕ) (k : {x // x ∈ Finset.range n}) :
    ⇑(freezingDefect hB T hBmeas hadap hcont hbdd n k) =ᵐ[μ] fun ω ↦
      (itoProcessCLM hB T (unifPart T n (k.1 + 1)) hBmeas (processToLp T hBmeas hadap hcont hbdd) ω
        - itoProcessCLM hB T (unifPart T n k.1) hBmeas (processToLp T hBmeas hadap hcont hbdd) ω)
      - σ (unifPart T n k.1) ω * (B (unifPart T n (k.1 + 1)) ω - B (unifPart T n k.1) ω) := by
  rw [freezingDefect_eq, itoIntegralCLM_T_simpleAssembly_T]
  filter_upwards [Lp.coeFn_sub (itoProcessCLM hB T (unifPart T n (k.1 + 1)) hBmeas
      (processToLp T hBmeas hadap hcont hbdd) - itoProcessCLM hB T (unifPart T n k.1) hBmeas
      (processToLp T hBmeas hadap hcont hbdd))
      (itoSimpleLp hB hBmeas (cellStep T hBmeas hadap hbdd n k).val),
    Lp.coeFn_sub (itoProcessCLM hB T (unifPart T n (k.1 + 1)) hBmeas
      (processToLp T hBmeas hadap hcont hbdd)) (itoProcessCLM hB T (unifPart T n k.1) hBmeas
      (processToLp T hBmeas hadap hcont hbdd)),
    (memLp_itoSimple hB hBmeas (cellStep T hBmeas hadap hbdd n k).val).coeFn_toLp]
    with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.sub_apply]
  congr 1
  exact h3.trans (itoSimple_stepSP hBmeas _ _ _ _ ω)

/-- Distinct cells of the uniform partition are disjoint. -/
theorem disjoint_cells {n : ℕ} {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (Set.Ioc (unifPart T n j) (unifPart T n (j + 1)))
      (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))) := by
  rcases lt_or_gt_of_ne hjk with h | h
  · exact Set.disjoint_left.2 fun s hs hs' ↦
      absurd (hs.2.trans (unifPart_mono T n (Nat.succ_le_of_lt h))) (not_le.2 hs'.1)
  · exact Set.disjoint_left.2 fun s hs hs' ↦
      absurd (hs'.2.trans (unifPart_mono T n (Nat.succ_le_of_lt h))) (not_le.2 hs.1)

/-- **Defects on distinct cells are orthogonal.** Their integrands live on disjoint cells, and the
Itô integral preserves inner products. -/
theorem inner_freezingDefect_eq_zero {n : ℕ} {j k : {x // x ∈ Finset.range n}} (hjk : j ≠ k) :
    ⟪freezingDefect hB T hBmeas hadap hcont hbdd n j,
      freezingDefect hB T hBmeas hadap hcont hbdd n k⟫_ℝ = 0 := by
  rw [freezingDefect, freezingDefect, inner_itoIntegralCLM_T, L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [coeFn_cellIntegrand T hBmeas hadap hcont hbdd n j,
    coeFn_cellIntegrand T hBmeas hadap hcont hbdd n k] with z hj hk
  rw [hj, hk]
  have hd := disjoint_cells T (n := n) (Subtype.coe_injective.ne hjk)
  by_cases hz : z.1 ∈ Set.Ioc (unifPart T n j.1) (unifPart T n (j.1 + 1))
  · have hz' : z.1 ∉ Set.Ioc (unifPart T n k.1) (unifPart T n (k.1 + 1)) :=
      Set.disjoint_left.1 hd hz
    simp [Set.indicator_of_notMem hz']
  · simp [Set.indicator_of_notMem hz]

/-- **The cell integrands telescope** to the whole freezing error `σ − stepσ`. -/
theorem sum_cellIntegrand {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ (Finset.range n).attach, cellIntegrand (μ := μ) T hBmeas hadap hcont hbdd n k
      = processToLp T hBmeas hadap hcont hbdd
        - simpleAssembly_T T hBmeas (stepσ hBmeas hadap hbdd T n) := by
  rw [stepσ_eq_sum_cellStep, map_sum]
  simp only [cellIntegrand, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_attach (Finset.range n) (fun k ↦ bandRestrict T (unifPart T n k)
    (unifPart T n (k + 1)) hBmeas (processToLp T hBmeas hadap hcont hbdd))]
  simp only [bandRestrict]
  rw [Finset.sum_range_sub' (fun k ↦ restrictAfterCLM T (unifPart T n k) hBmeas
    (processToLp T hBmeas hadap hcont hbdd)) n]
  have h0 : unifPart T n 0 = 0 := by simp [unifPart]
  have hT : unifPart T n n = T := by simp [unifPart, hn]
  rw [h0, hT]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (restrictAfterCLM T 0 hBmeas (processToLp T hBmeas hadap hcont hbdd))
      (restrictAfterCLM T T hBmeas (processToLp T hBmeas hadap hcont hbdd)),
    coeFn_restrictAfterCLM T 0 hBmeas (processToLp T hBmeas hadap hcont hbdd),
    coeFn_restrictAfterCLM T T hBmeas (processToLp T hBmeas hadap hcont hbdd),
    ae_fst_mem_Ioc_trimMeasure_T T hBmeas] with z h1 h2 h3 hz
  rw [h1, Pi.sub_apply, h2, h3, if_pos hz.1, if_neg (not_lt.2 hz.2), sub_zero]

/-- **The defects sum to the Itô integral of the freezing error**: `∫σ dB` minus the frozen
Riemann–Itô sum `∑ σ(tₖ)·ΔBₖ`. -/
theorem sum_freezingDefect {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ (Finset.range n).attach, freezingDefect hB T hBmeas hadap hcont hbdd n k
      = itoIntegralCLM_T hB T hBmeas (processToLp T hBmeas hadap hcont hbdd)
        - (memLp_riemannσ hB hBmeas hadap hbdd T n).toLp (riemannσ (B := B) σ T n) := by
  simp only [freezingDefect]
  rw [← map_sum, sum_cellIntegrand T hBmeas hadap hcont hbdd hn, map_sub,
    itoIntegralCLM_T_stepσ hB hBmeas hadap hbdd T n]

/-- **Freezing.** For a bounded adapted continuous `σ` and `M = σ●B`, the squared `L²` norms of
the defects `ΔMₖ − σ(tₖ)·ΔBₖ` over the cells of the uniform partition sum to something tending
to `0`. The defects are orthogonal, so the sum is the squared norm of their total, the error of
the frozen Riemann–Itô sum, which tends to `0` (`itoIntegralCLM_T_of_bdd_adapted_cont`). -/
theorem tendsto_sum_norm_sq_freezingDefect :
    Tendsto (fun n ↦ ∑ k ∈ (Finset.range n).attach,
      ‖freezingDefect hB T hBmeas hadap hcont hbdd n k‖ ^ 2) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun n ↦
      ‖itoIntegralCLM_T hB T hBmeas (processToLp T hBmeas hadap hcont hbdd)
        - (memLp_riemannσ hB hBmeas hadap hbdd T n).toLp (riemannσ (B := B) σ T n)‖)
      atTop (𝓝 0) := by
    simpa [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.1
      (itoIntegralCLM_T_of_bdd_adapted_cont hB hBmeas hadap hcont hbdd T)
  have hsq := hnorm.pow 2
  rw [zero_pow two_ne_zero] at hsq
  refine hsq.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [← sum_freezingDefect hB T hBmeas hadap hcont hbdd hn,
    norm_sum_sq_of_pairwise_inner_eq_zero _ _
      fun j k hjk ↦ inner_freezingDefect_eq_zero hB T hBmeas hadap hcont hbdd hjk]

end Freezing

end AdaptedStochasticIntegralFreezing

end MathFin
