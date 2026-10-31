/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralProcessMartingale
public import MathFin.Foundations.ItoIntegralCLM

/-! # The general-integrand Itô integral as an L² martingale on `[0,T]` (B1b)

B1a built the simple-integrand Itô integral `t ↦ (V●B)_t` as a continuous L²
martingale. This file extends it to a **general** predictable integrand
`φ ∈ Lp ℝ 2 (trimMeasure_T T)` (= Degenne's `L2Predictable` on `[0,T]`) by
density: the process `t ↦ (φ●B)_t := ∫₀ᵗ φ dB` is a continuous L² martingale, with
the Itô contraction `‖(φ●B)_t‖ ≤ ‖φ‖` and the terminal Itô isometry
`‖(φ●B)_T‖ = ‖φ‖`. The explicit time-indexed isometry
`E[(φ●B)_t²] = ∫₀ᵗ E[φ_s²] ds` is proved in the companion module
`ItoIntegralProcessIsometry` (`itoProcessCLM_norm_sq`), by density-transferring the
band-restricted simple-process isometry against a band-truncation CLM.

The process is *defined* as the `𝓕_t`-conditional-expectation projection (`condExpL2`) of the
terminal integral `itoIntegralCLM_T`, so it is the continuous linear map that the infinite-horizon
`itoProcessL2Inf` is, composed with `bandExtend`; its linearity, continuity and the contraction
`‖(φ●B)_t‖ ≤ ‖φ‖` are those of a conditional expectation and of the Itô isometry. The bridge to
B1a's simple-integrand process (`itoProcessCLM_simpleAssembly_T`) is B1a's martingale property.

The infinite-horizon `[0,∞)` integral (σ-finite predictable exhaustion) is the
separate later milestone B2.

## Result

* `itoProcessCLM` — the Itô integral process of a general predictable `L²` integrand.
* `itoProcessCLM_simpleAssembly_T` — the bridge back to B1a.
* `itoProcessCLM_zero_time` — the process starts at `0`.
* `condExp_itoSimple_eq` — B1a's martingale read to the terminal.
* `itoProcessCLM_eq_condExpL2` — **the key identity** (by definition): `(φ●B)_t` is the
  `𝓕_t`-projection of the terminal integral.
* `itoProcessCLM_aeStronglyMeasurable`, `itoIntegralProcessGen_isMartingale` — its two
  corollaries: a.e.-adaptedness and the martingale property.
* `itoProcessCLM_norm_le` — the contraction `‖(φ●B)_t‖ ≤ ‖φ‖`.
* `itoProcessCLM_terminal_eq`, `itoProcessCLM_norm_terminal` — at the horizon the process is
  the terminal integral, so the contraction is the Itô isometry.
* `integral_itoIntegralCLM_T` — the terminal integral is centered.
* `itoIntegralProcessGen_l2_continuous` — `t ↦ (φ●B)_t` is `L²`-continuous. -/

@[expose] public section

namespace MathFin
namespace ItoIntegralProcessGeneral

open MeasureTheory ProbabilityTheory
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- **The Itô integral process on `[0,T]`**: the `𝓕_t`-conditional-expectation projection
(`condExpL2`) of the terminal integral `itoIntegralCLM_T`. For `φ ∈ L²(predictable, [0,T])`, this
is `∫₀ᵗ φ dB ∈ L²(μ)`; it is the band restriction `itoProcessL2Inf t ∘ bandExtend T` of the
infinite-horizon process. -/
noncomputable def itoProcessCLM (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) →L[ℝ] Lp ℝ 2 μ :=
  ((lpMeas ℝ ℝ (natFiltration hBmeas t) 2 μ).subtypeL.comp
    (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t))).comp (itoIntegralCLM_T hB T hBmeas)

/-- **The key identity.** The general Itô integral at time `t` is the
conditional-expectation projection of its terminal value `∫₀ᵀ φ dB` onto `𝓕_t`:
`(φ●B)_t = condExpL2 𝓕_t (itoIntegralCLM_T T φ)`. Adaptedness and the martingale
property are corollaries. -/
theorem itoProcessCLM_eq_condExpL2 (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    itoProcessCLM hB T t hBmeas φ
      = (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t)
          (itoIntegralCLM_T hB T hBmeas φ) : Lp ℝ 2 μ) :=
  rfl

omit [IsProbabilityMeasure μ] in
/-- B1a's martingale to the terminal: `μ[itoSimple V | 𝓕_t] = (V●B)_t` for
`T`-bounded `V` (`(V●B)_{T'} = itoSimple V` at `T' = t ⊔ T`). -/
theorem condExp_itoSimple_eq (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (hVT : ∀ p ∈ V.value.support, p.2 ≤ T) :
    μ[itoSimple hBmeas V | natFiltration hBmeas t]
      =ᵐ[μ] fun ω ↦ itoSimpleProcess hBmeas V t ω := by
  have hT'eq : itoSimpleProcess hBmeas V (max t T) = itoSimple hBmeas V :=
    itoSimpleProcess_eq_itoSimple hBmeas V fun p hp ↦ (hVT p hp).trans (le_max_right t T)
  simpa only [hT'eq] using (itoSimpleProcess_isMartingale hB hBmeas V).2 t (max t T)
      (le_max_left t T)

/-- **The bridge to B1a.** On the embedding of a `T`-bounded simple process, the general CLM
reproduces B1a's t-process `(V●B)_t`: on simple processes the terminal integral is `itoSimple V`
and B1a's martingale reads `μ[itoSimple V | 𝓕_t] = (V●B)_t`. -/
theorem itoProcessCLM_simpleAssembly_T (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP T hBmeas) :
    itoProcessCLM hB T t hBmeas (simpleAssembly_T (μ := μ) T hBmeas V)
      = itoSimpleProcessLp hB hBmeas V.val t := by
  rw [itoProcessCLM_eq_condExpL2, itoIntegralCLM_T_simpleAssembly_T]
  refine Lp.ext ?_
  simp only [itoSimpleProcessLp, itoSimpleLp]
  filter_upwards [(memLp_itoSimpleProcess hB hBmeas V.val t).coeFn_toLp,
    (memLp_itoSimple hB hBmeas V.val).condExpL2_ae_eq_condExp (𝕜 := ℝ)
        ((natFiltration hBmeas).le t),
    condExp_itoSimple_eq hB T t hBmeas V.val V.property] with ω hω1 hω2 hω3
  rw [hω2, hω3, hω1]

/-- **The Itô integral process starts at zero.** On the dense simple processes this is
`itoSimpleProcess_zero_time`, and both sides are continuous-linear in the integrand. -/
@[simp] theorem itoProcessCLM_zero_time (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    itoProcessCLM hB T 0 hBmeas φ = 0 := by
  refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (μ := μ) T hBmeas)
    (itoProcessCLM hB T 0 hBmeas).continuous
    (continuous_const (y := (0 : Lp ℝ 2 μ))) (funext fun V ↦ ?_)) φ
  simp only [Function.comp_apply, itoProcessCLM_simpleAssembly_T, itoSimpleProcessLp]
  refine Lp.ext (((memLp_itoSimpleProcess hB hBmeas V.val 0).coeFn_toLp).trans ?_)
  rw [itoSimpleProcess_zero_time]
  exact (Lp.coeFn_zero ℝ 2 μ).symm

/-- **a.e.-adaptedness.** `(φ●B)_t` is a.e. `𝓕_t`-measurable: by the key identity it
is (a `condExpL2` projection onto) the `𝓕_t`-measurable subspace. -/
theorem itoProcessCLM_aeStronglyMeasurable (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    AEStronglyMeasurable[natFiltration hBmeas t]
      (itoProcessCLM hB T t hBmeas φ : Ω → ℝ) μ := by
  rw [itoProcessCLM_eq_condExpL2]
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t) (itoIntegralCLM_T hB T hBmeas φ)).2

/-- **The general Itô integral is an L² martingale (B1b).** For `i ≤ j`,
`μ[(φ●B)_j | 𝓕_i] =ᵐ (φ●B)_i`. By the key identity each `(φ●B)_k` is the `𝓕_k`-
conditional expectation of the terminal integral `∫₀ᵀ φ dB`, so the martingale
property is the conditional-expectation tower `μ[μ[X | 𝓕_j] | 𝓕_i] = μ[X | 𝓕_i]`. -/
theorem itoIntegralProcessGen_isMartingale (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {i j : ℝ≥0} (hij : i ≤ j) :
    μ[(itoProcessCLM hB T j hBmeas φ : Ω → ℝ) | natFiltration hBmeas i]
      =ᵐ[μ] (itoProcessCLM hB T i hBmeas φ : Ω → ℝ) := by
  -- each value is the conditional expectation of the terminal integral `X`.
  have hbridge : ∀ k : ℝ≥0,
      ((condExpL2 ℝ ℝ ((natFiltration hBmeas).le k)
          (itoIntegralCLM_T hB T hBmeas φ) : Lp ℝ 2 μ) : Ω → ℝ)
        =ᵐ[μ] μ[(itoIntegralCLM_T hB T hBmeas φ : Ω → ℝ) | natFiltration hBmeas k] := by
    intro k
    have h := (Lp.memLp (itoIntegralCLM_T hB T hBmeas φ)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) ((natFiltration hBmeas).le k)
    rwa [Lp.toLp_coeFn] at h
  rw [itoProcessCLM_eq_condExpL2, itoProcessCLM_eq_condExpL2]
  calc μ[((condExpL2 ℝ ℝ ((natFiltration hBmeas).le j)
            (itoIntegralCLM_T hB T hBmeas φ) : Lp ℝ 2 μ) : Ω → ℝ) | natFiltration hBmeas i]
      =ᵐ[μ] μ[μ[(itoIntegralCLM_T hB T hBmeas φ : Ω → ℝ) | natFiltration hBmeas j]
              | natFiltration hBmeas i] := condExp_congr_ae (hbridge j)
    _ =ᵐ[μ] μ[(itoIntegralCLM_T hB T hBmeas φ : Ω → ℝ) | natFiltration hBmeas i] :=
        condExp_condExp_of_le ((natFiltration hBmeas).mono hij) ((natFiltration hBmeas).le j)
    _ =ᵐ[μ] ((condExpL2 ℝ ℝ ((natFiltration hBmeas).le i)
              (itoIntegralCLM_T hB T hBmeas φ) : Lp ℝ 2 μ) : Ω → ℝ) := (hbridge i).symm

/-- **The Itô-isometry contraction.** `‖(φ●B)_t‖ ≤ ‖φ‖`: by the key identity
`(φ●B)_t` is the `𝓕_t`-conditional expectation of `∫₀ᵀ φ dB`, and conditional
expectation is an L² contraction; the terminal integral is an isometry
(`itoIntegralCLM_T_norm`). -/
theorem itoProcessCLM_norm_le (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ‖itoProcessCLM hB T t hBmeas φ‖ ≤ ‖φ‖ := by
  have hae : (itoProcessCLM hB T t hBmeas φ : Ω → ℝ)
      =ᵐ[μ] μ[(itoIntegralCLM_T hB T hBmeas φ : Ω → ℝ) | natFiltration hBmeas t] := by
    rw [itoProcessCLM_eq_condExpL2]
    have h := (Lp.memLp (itoIntegralCLM_T hB T hBmeas φ)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) ((natFiltration hBmeas).le t)
    rwa [Lp.toLp_coeFn] at h
  rw [Lp.norm_def, ← itoIntegralCLM_T_norm hB T hBmeas φ, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.memLp (itoIntegralCLM_T hB T hBmeas φ)).2.ne ?_
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_condExp_le_eLpNorm _ (by simp)

/-- **At the terminal time the process is the terminal integral.** `(φ●B)_T = itoIntegralCLM_T φ`
as `Lp` elements: both are continuous-linear in `φ` and reproduce `itoSimple V` on the dense
simple processes (`(V●B)_T = itoSimple V`). -/
theorem itoProcessCLM_terminal_eq (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    itoProcessCLM hB T T hBmeas φ = itoIntegralCLM_T hB T hBmeas φ :=
  congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (μ := μ) T hBmeas)
    (itoProcessCLM hB T T hBmeas).continuous (itoIntegralCLM_T hB T hBmeas).continuous
    (funext fun V ↦ by
      simp only [Function.comp_apply, itoProcessCLM_simpleAssembly_T,
        itoIntegralCLM_T_simpleAssembly_T, itoSimpleProcessLp, itoSimpleLp,
        itoSimpleProcess_eq_itoSimple hBmeas V.val (fun p hp ↦ V.property p hp)])) φ

/-- **Terminal Itô isometry.** At the horizon the process is the terminal integral
(`itoProcessCLM_terminal_eq`), so `‖(φ●B)_T‖ = ‖φ‖` exactly. -/
theorem itoProcessCLM_norm_terminal (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ‖itoProcessCLM hB T T hBmeas φ‖ = ‖φ‖ := by
  rw [itoProcessCLM_terminal_eq hB T hBmeas φ, itoIntegralCLM_T_norm hB T hBmeas φ]

/-- **The Itô integral is centered**, `𝔼[∫₀ᵀ φ dB] = 0`: the integral process is a
martingale started at `0`, and conditioning preserves the mean. -/
theorem integral_itoIntegralCLM_T (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ∫ ω, itoIntegralCLM_T hB T hBmeas φ ω ∂μ = 0 := by
  have hmart := itoIntegralProcessGen_isMartingale hB T hBmeas φ (i := 0) (j := T) zero_le
  rw [itoProcessCLM_zero_time hB T hBmeas φ] at hmart
  rw [← itoProcessCLM_terminal_eq hB T hBmeas φ,
    ← integral_condExp ((natFiltration hBmeas).le 0), integral_congr_ae hmart]
  simp

/-- **L²-continuity.** `t ↦ (φ●B)_t` is continuous into `Lp ℝ 2 μ`. The simple-
process integrals `t ↦ (Vₙ●B)_t` (continuous by B1a's
`itoSimpleProcessLp_l2_continuous`) approximate it *uniformly in `t`* — the
contraction `‖(φ●B)_t − (Vₙ●B)_t‖ ≤ ‖φ − Vₙ‖` is `t`-free — so the limit is
continuous (`TendstoUniformly.continuous`). -/
theorem itoIntegralProcessGen_l2_continuous (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Continuous (fun t ↦ itoProcessCLM hB T t hBmeas φ) := by
  -- approximate `φ` by a sequence of simple-process embeddings (dense range).
  obtain ⟨g, hg_range, hg_lim⟩ := mem_closure_iff_seq_limit.mp
    ((simpleAssembly_T_denseRange (μ := μ) T hBmeas).closure_range.ge (Set.mem_univ φ))
  choose V hV using hg_range
  -- each approximant's process is continuous in `t` (bridge to B1a's continuity).
  have hcont_n : ∀ n, Continuous (fun t ↦ itoProcessCLM hB T t hBmeas (g n)) := fun n ↦ by
    simp only [← hV n, itoProcessCLM_simpleAssembly_T]
    exact itoSimpleProcessLp_l2_continuous hB hBmeas (V n).val
  -- uniform convergence: `dist ≤ ‖φ − gₙ‖ → 0`, independent of `t`.
  have huniform : TendstoUniformly (fun n t ↦ itoProcessCLM hB T t hBmeas (g n))
      (fun t ↦ itoProcessCLM hB T t hBmeas φ) Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hnorm_lim : Filter.Tendsto (fun n ↦ ‖φ - g n‖) Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := φ)).sub hg_lim
      simpa using this.norm
    filter_upwards [hnorm_lim.eventually (eventually_lt_nhds hε)] with n hn t
    rw [dist_eq_norm, ← map_sub]
    exact lt_of_le_of_lt (itoProcessCLM_norm_le hB T t hBmeas (φ - g n)) hn
  exact huniform.continuous (Filter.Eventually.of_forall hcont_n).frequently

end ItoIntegralProcessGeneral
end MathFin
