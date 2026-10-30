/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaAdaptedProcess
public import MathFin.Foundations.ItoFormulaUnrestricted
public import MathFin.Foundations.LevyCharacterization

/-! # Summit C — the unrestricted-`C³` Itô formula as a local martingale

For a general `C³` function `f` (six partials, all jointly continuous, **no** growth or
boundedness hypothesis) the Itô residual
`M_t = f(t, B_t) − f(0, B_0) − ∫₀ᵗ (f_t + ½ f_xx)(s, B_s) ds` (`itoResidual`) is a continuous local
martingale for the null-augmented Brownian filtration, localised by `σ_N = min(τ_N, N)`, `τ_N` the
exit time of `B` from `[−N, N]` (`sigmaSeq`).

* `ito_formula_unrestricted`: `M` is Degenne's `IsLocalMartingale`.
* `ito_formula_unrestricted_local`: the same in explicit form, a localizing sequence and, for each
  `N`, a continuous true martingale equal to `M` on `{t ≤ σ_N}`.

Both come from `martingale_stoppedProcess_itoResidual`: `M` stopped at `σ_N` is a martingale. It is
a local martingale because it is indistinguishable from the stopped continuous local martingale of
Itô's formula for `B` regarded as an Itô process with `σ = 1`, `b = 0`
(`exists_localMartingale_ito_formula`, `ae_localItoIntegral_one_eq`), and bounded, since up to `σ_N`
`|B| ≤ N` and `t ≤ N` while `f`, `f_t`, `f_xx` are bounded on that compact square; a bounded local
martingale is a martingale (`bounded_localMartingale_is_martingale`). Only `f`, `f_t`, `f_x`,
`f_xx` are used; the hypotheses on `f_tt`, `f_tx`, `f_xxx` are carried by the statements.

`M` is adapted to the null-augmented filtration (`residual_stronglyMeasurable`): the drift primitive
`D_t = ∫₀ᵗ (f_t + ½ f_xx)(s, B_s) ds` is `𝓕_t`-measurable (`driftPrimitive_stronglyMeasurable`)
because, after clamping the integrand's time to `[0, t]` (so each slice is `𝓕_t`-measurable), it is
jointly strongly measurable (Carathéodory: continuous in `s`, `𝓕_t`-measurable in `ω`), and the
integral of a jointly measurable function is measurable (`StronglyMeasurable.integral_prod_right`).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology
open ItoIntegralL2 ItoIntegralBrownian ItoIntegralProcessLocalMartingaleGeneral ItoIntegralLocalised
  LocalisationInMeasure ItoIntegralRiemannBridge

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The drift primitive is adapted.** `D_t = ∫₀ᵗ (f_t + ½f_xx)(s, B_s) ds` is
`𝓕_t`-measurable: clamping the integrand's time to `[0,t]` makes every slice `𝓕_t`-measurable
(`B_{min s t}` with `min s t ≤ t`), so the clamped integrand is jointly strongly measurable
(Carathéodory) and the integral over `s` is `𝓕_t`-measurable. -/
lemma driftPrimitive_stronglyMeasurable (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {f_t f_xx : ℝ → ℝ → ℝ}
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2) (t : ℝ≥0) :
    StronglyMeasurable[natFiltration hBmeas t]
      (fun ω ↦ ∫ s in Set.Ioc 0 t,
        (f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω)) ∂timeMeasure) := by
  -- the time-clamped integrand `g s ω = drift (min s t) ω`
  set g : ℝ≥0 → Ω → ℝ := fun s ω ↦
    f_t (↑(min s t)) (B (min s t) ω) + (1 / 2) * f_xx (↑(min s t)) (B (min s t) ω) with hg
  -- every clamped slice is `𝓕_t`-measurable (`min s t ≤ t`) — proved with `mΩ` still ambient
  have hBmin : ∀ s : ℝ≥0, StronglyMeasurable[natFiltration hBmeas t] (B (min s t)) := fun s ↦
    ((measurable_eval_natFiltration hBmeas (min s t)).mono
      ((natFiltration hBmeas).mono (min_le_right s t)) le_rfl).stronglyMeasurable
  have hg_meas : ∀ s, StronglyMeasurable[natFiltration hBmeas t] (g s) := by
    intro s
    refine StronglyMeasurable.add ?_ (stronglyMeasurable_const.mul ?_)
    · exact (hf_t_cont.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable
        (hBmin s)
    · exact (hf_xx_cont.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable
        (hBmin s)
  -- and `s ↦ g s ω` is continuous (drift continuous, `min` continuous)
  have hg_cont : ∀ ω, Continuous fun s ↦ g s ω := by
    intro ω
    have hdrift : Continuous fun s : ℝ≥0 ↦
        f_t (↑s) (B s ω) + (1 / 2) * f_xx (↑s) (B s ω) :=
      (hf_t_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))).add
        (continuous_const.mul (hf_xx_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))))
    exact hdrift.comp (continuous_id.min continuous_const)
  -- now switch to `𝓕_t` as the ambient σ-algebra for the joint-measurability + integral lemmas
  letI : MeasurableSpace Ω := natFiltration hBmeas t
  -- the uncurried clamped integrand is jointly strongly measurable (Carathéodory + swap +
  -- indicator)
  have huncurry : StronglyMeasurable
      (Function.uncurry fun (ω : Ω) (s : ℝ≥0) ↦
        (Set.Ioc 0 t).indicator (fun s ↦ g s ω) s) := by
    have hjoint : StronglyMeasurable (Function.uncurry g) :=
      stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hg_cont hg_meas
    have hswap : StronglyMeasurable (fun p : Ω × ℝ≥0 ↦ g p.2 p.1) :=
      hjoint.comp_measurable measurable_swap
    have heq : (Function.uncurry fun (ω : Ω) (s : ℝ≥0) ↦
          (Set.Ioc 0 t).indicator (fun s ↦ g s ω) s)
        = (Set.univ ×ˢ Set.Ioc 0 t).indicator (fun p : Ω × ℝ≥0 ↦ g p.2 p.1) := by
      funext p
      simp only [Function.uncurry, Set.indicator]
      by_cases hp : p.2 ∈ Set.Ioc 0 t <;> simp [hp]
    rw [heq]
    exact hswap.indicator (MeasurableSet.univ.prod measurableSet_Ioc)
  -- the integral equals the clamped integral (`g = drift` on `(0,t]`), which is `𝓕_t`-measurable
  have hval : (fun ω ↦ ∫ s in Set.Ioc 0 t,
        (f_t (↑s) (B s ω) + (1 / 2) * f_xx (↑s) (B s ω)) ∂timeMeasure)
      = fun ω ↦ ∫ s, (Set.Ioc 0 t).indicator (fun s ↦ g s ω) s ∂timeMeasure := by
    funext ω
    rw [integral_indicator measurableSet_Ioc]
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs ↦ ?_)
    simp only [hg, min_eq_left hs.2]
  rw [hval]
  exact huncurry.integral_prod_right

/-- **The compensated residual `M` is adapted.** `M_t = f(t,B_t) − f(0,B_0) − D_t` is
`𝓕_t`-measurable: `f(t,B_t)` and `f(0,B_0)` are (`B` adapted, `f` continuous), and `D_t` is by
`driftPrimitive_stronglyMeasurable`. -/
lemma residual_stronglyMeasurable (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {f f_t f_xx : ℝ → ℝ → ℝ}
    (hf_cont : Continuous fun p : ℝ × ℝ ↦ f p.1 p.2)
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2) (t : ℝ≥0) :
    StronglyMeasurable[natFiltration hBmeas t]
      (fun ω ↦ f (t : ℝ) (B t ω) - f 0 (B 0 ω)
        - ∫ s in Set.Ioc 0 t,
            (f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω)) ∂timeMeasure) := by
  have hBt : StronglyMeasurable[natFiltration hBmeas t] (B t) :=
    (measurable_eval_natFiltration hBmeas t).stronglyMeasurable
  have hB0 : StronglyMeasurable[natFiltration hBmeas t] (B 0) :=
    ((measurable_eval_natFiltration hBmeas 0).mono
      ((natFiltration hBmeas).mono zero_le) le_rfl).stronglyMeasurable
  refine (StronglyMeasurable.sub ?_ ?_).sub
    (driftPrimitive_stronglyMeasurable hBmeas hBcont hf_t_cont hf_xx_cont t)
  · exact (hf_cont.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable hBt
  · exact (hf_cont.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable hB0

variable [IsProbabilityMeasure μ]

/-- **The Itô residual** `M_t = f(t, B_t) − f(0, B_0) − ∫₀ᵗ (f_t + ½ f_xx)(s, B_s) ds`: what is left of
`f(t, B_t) − f(0, B_0)` once the drift of Itô's formula is taken out. -/
noncomputable def itoResidual (f f_t f_xx : ℝ → ℝ → ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  f (t : ℝ) (B t ω) - f 0 (B 0 ω)
    - ∫ s in Set.Ioc 0 t, (f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω)) ∂timeMeasure

/-- The Itô residual of a path with jointly continuous `f`, `f_t`, `f_xx` is continuous in time. -/
lemma continuous_itoResidual {f f_t f_xx : ℝ → ℝ → ℝ}
    (hf_cont : Continuous fun p : ℝ × ℝ ↦ f p.1 p.2)
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (ω : Ω) :
    Continuous fun t ↦ itoResidual f f_t f_xx B t ω :=
  ((hf_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))).sub continuous_const).sub
    (continuous_timeMeasure_primitive
      ((hf_t_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))).add
        (continuous_const.mul (hf_xx_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))))))

/-- **The Brownian path is the Itô integral of `1`.** For `σ = 1`, `localItoIntegral` is, almost
surely, at every `t ∈ [0, T]`, the path `B t`: at each `t` its Riemann sums are the telescoping
`B t − B 0 = B t` (`B 0 = 0` almost surely), and two processes with continuous paths that agree at
each time are indistinguishable. -/
theorem ae_localItoIntegral_one_eq (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T,
      localItoIntegral (μ := μ) T hBmeas (σ := fun _ _ ↦ (1 : ℝ))
        (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) t ω = B t ω := by
  have hsum (t : ℝ≥0) {n : ℕ} (hn : n ≠ 0) (ω : Ω) :
      riemannσ (B := B) (fun _ _ ↦ (1 : ℝ)) t n ω = B t ω - B 0 ω := by
    simp only [riemannσ, one_mul]
    rw [Finset.sum_range_sub (fun k ↦ B (unifPart t n k) ω), unifPart_self t hn, unifPart_zero]
  have hconv (t : ℝ≥0) : TendstoInMeasure μ (fun n ω ↦ riemannσ (B := B) (fun _ _ ↦ (1 : ℝ)) t n ω)
      atTop (fun ω ↦ B t ω - B 0 ω) :=
    tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (Finset.measurable_sum _ fun k _ ↦
        measurable_const.mul ((hBmeas _).sub (hBmeas _))).aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ tendsto_const_nhds.congr'
        ((eventually_ne_atTop 0).mono fun n hn ↦ (hsum t hn ω).symm))
  filter_upwards [ae_forall_eq_of_tendstoInMeasure (T := T)
      (Y' := fun t ω ↦ B t ω - B 0 ω)
      (ae_continuousOn_localItoIntegral hB T hBmeas hBcont (σ := fun _ _ ↦ (1 : ℝ))
        (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const))
      (ae_of_all _ fun ω ↦ ((hBcont ω).sub continuous_const).continuousOn)
      (fun t ht ↦ tendstoInMeasure_riemannσ_localItoIntegral hB T hBmeas hBcont _ _ ht.2)
      (fun t _ ↦ hconv t), eval_zero_ae hB hBmeas] with ω h h0 t ht
  rw [h t ht, h0, Pi.zero_apply, sub_zero]

/-- **The residual of Itô's formula, stopped at `σ_N = min(τ_N, N)`, is a bounded martingale.**
For `f` with jointly continuous partials `f_t`, `f_x`, `f_xx`, let `Y` be the continuous local
martingale of `exists_localMartingale_ito_formula` at `σ = 1`, `b = 0` and horizon `N`: by
`ae_localItoIntegral_one_eq` the process there is `B`, so `Y` is almost surely the residual `M` on
`[0, N]`. `σ_N ≤ N`, so `M` stopped at `σ_N` is indistinguishable from `Y` stopped there, a local
martingale (`IsStable.locally`) with continuous adapted paths, hence
a local martingale itself (`isLocalMartingale_congr_ae`). Up to the exit time `|B| ≤ N` and
`t ≤ N`, where `f`, `f_t`, `f_xx` are bounded on a compact square, so it is bounded, hence a
martingale (`bounded_localMartingale_is_martingale`). -/
theorem martingale_stoppedProcess_itoResidual (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {f f_t f_x f_xx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
    (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
    (hf_cont : Continuous fun p : ℝ × ℝ ↦ f p.1 p.2)
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2) (N : ℕ) :
    Martingale (stoppedProcess
      (fun i ↦ {ω | ⊥ < sigmaSeq B N ω}.indicator (itoResidual f f_t f_xx B i)) (sigmaSeq B N))
      (augFiltration (μ := μ) hBmeas) μ := by
  set M := itoResidual f f_t f_xx B
  have hMcont : ∀ ω, Continuous fun t ↦ M t ω := continuous_itoResidual hf_cont hf_t_cont hf_xx_cont hBcont
  have hMadapt : StronglyAdapted (augFiltration (μ := μ) hBmeas) M := fun i ↦ by
    refine (residual_stronglyMeasurable hBmeas hBcont hf_cont hf_t_cont hf_xx_cont i).mono ?_
    rw [augFiltration_apply]; exact le_sup_left
  have hσ := (isLocalizingSequence_sigma (μ := μ) hBmeas hBcont).isStoppingTime N
  have hs_le (t : ℝ≥0) (ω : Ω) : (min (t : WithTop ℝ≥0) (sigmaSeq B N ω)).untopA ≤ (N : ℝ≥0) := by
    refine WithTop.coe_le_coe.1 ?_
    rw [LevyCharacterization.coe_untopA_min]
    exact (min_le_right _ _).trans (min_le_right _ _)
  -- the local martingale of the process formula at `σ = 1`, `b = 0`, horizon `N`
  obtain ⟨Y, hYM, -, hYm⟩ := ItoFormulaAdapted.exists_localMartingale_ito_formula hB (N : ℝ≥0)
    hBmeas hBcont (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const)
    (fun _ ↦ continuous_const) (b := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ stronglyMeasurable_const)
    (fun _ ↦ continuous_const) 0 hf_t hf_x hf_xx hf_t_cont hf_x_cont hf_xx_cont
  have hYM' : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 (N : ℝ≥0), Y t ω = M t ω := by
    filter_upwards [hYM, ae_localItoIntegral_one_eq hB (N : ℝ≥0) hBmeas hBcont,
      eval_zero_ae hB hBmeas] with ω hω hX h0 t ht
    have hXs (s : ℝ≥0) (hs : s ∈ Set.Icc 0 (N : ℝ≥0)) :
        ItoFormulaAdapted.localItoProcess (μ := μ) (N : ℝ≥0) hBmeas (σ := fun _ _ ↦ (1 : ℝ))
          (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) 0 (fun _ _ ↦ (0 : ℝ)) s ω
          = B s ω := by
      simp [ItoFormulaAdapted.localItoProcess, AdaptedDrift.driftPath, hX s hs]
    rw [hω t ht, hXs t ht]
    simp only [M, itoResidual, Pi.zero_apply] at h0 ⊢
    rw [h0]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ by
      rw [hXs s ⟨zero_le, hs.2.trans ht.2⟩]; ring
  have hloc : IsLocalMartingale (stoppedProcess
      (fun i ↦ {ω | ⊥ < sigmaSeq B N ω}.indicator (Y i)) (sigmaSeq B N))
      (augFiltration (μ := μ) hBmeas) μ :=
    (isStable_martingale (𝓕 := augFiltration (μ := μ) hBmeas) (P := μ)).locally Y hYm _ hσ
  have hind : ∀ᵐ ω ∂μ, ∀ t, stoppedProcess
      (fun i ↦ {ω | ⊥ < sigmaSeq B N ω}.indicator (Y i)) (sigmaSeq B N) t ω
      = stoppedProcess (fun i ↦ {ω | ⊥ < sigmaSeq B N ω}.indicator (M i)) (sigmaSeq B N) t ω := by
    filter_upwards [hYM'] with ω hω t
    simp only [stoppedProcess, Set.indicator_apply]
    rw [hω _ ⟨zero_le, hs_le t ω⟩]
  have hadapt := hMadapt.stoppedProcess_indicator
    (fun ω ↦ (hMcont ω).isCadlag.right_continuous) hσ
  have hcad := isStable_isCadlag M (fun ω ↦ (hMcont ω).isCadlag) _ hσ
  -- bounded: `|B| ≤ N` and `t ≤ N` up to `σ_N`, where `f`, `f_t`, `f_xx` are bounded
  have hK : IsCompact (Set.Icc (0 : ℝ) N ×ˢ Set.Icc (-(N : ℝ)) N) :=
    isCompact_Icc.prod isCompact_Icc
  have hg : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2 + 1 / 2 * f_xx p.1 p.2 :=
    hf_t_cont.add (continuous_const.mul hf_xx_cont)
  obtain ⟨Cf, hCf⟩ := hK.exists_bound_of_continuousOn hf_cont.continuousOn
  obtain ⟨Cd, hCd⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ Set.Icc (0 : ℝ) N ×ˢ Set.Icc (-(N : ℝ)) N :=
    ⟨⟨le_rfl, N.cast_nonneg⟩, ⟨neg_nonpos.2 N.cast_nonneg, N.cast_nonneg⟩⟩
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf _ h00)
  have hCd0 : 0 ≤ Cd := (norm_nonneg _).trans (hCd _ h00)
  have hbound : ∀ t ω, ‖stoppedProcess
      (fun i ↦ {ω | ⊥ < sigmaSeq B N ω}.indicator (M i)) (sigmaSeq B N) t ω‖
      ≤ Cf + Cf + Cd * N := by
    intro t ω
    simp only [stoppedProcess]
    by_cases hpos : ⊥ < sigmaSeq B N ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ⊥ < sigmaSeq B N ω} from hpos)]
      set s := (min (t : WithTop ℝ≥0) (sigmaSeq B N ω)).untopA
      have hsN : s ≤ (N : ℝ≥0) := hs_le t ω
      have hBs (u : ℝ≥0) (hu : u ≤ s) : |B u ω| ≤ N := by
        refine abs_le_of_le_exitTime hBcont (lt_min_iff.1 hpos).1 ?_
        calc (u : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0) := WithTop.coe_le_coe.2 hu
          _ = min (t : WithTop ℝ≥0) (sigmaSeq B N ω) := LevyCharacterization.coe_untopA_min _ _
          _ ≤ sigmaSeq B N ω := min_le_right _ _
          _ ≤ exitTime B N ω := min_le_left _ _
      have hmem (u : ℝ≥0) (hu : u ≤ s) :
          ((u : ℝ), B u ω) ∈ Set.Icc (0 : ℝ) N ×ˢ Set.Icc (-(N : ℝ)) N :=
        ⟨⟨u.coe_nonneg, by exact_mod_cast hu.trans hsN⟩, abs_le.1 (hBs u hu)⟩
      have hint : ‖∫ u in Set.Ioc 0 s, (f_t (u : ℝ) (B u ω) + 1 / 2 * f_xx (u : ℝ) (B u ω))
          ∂timeMeasure‖ ≤ Cd * s := by
        refine (norm_setIntegral_le_of_norm_le_const
          (by rw [timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top)
          (fun u hu ↦ hCd _ (hmem u hu.2))).trans_eq ?_
        simp [Measure.real, timeMeasure_Ioc]
      calc ‖M s ω‖ ≤ ‖f (s : ℝ) (B s ω)‖ + ‖f 0 (B 0 ω)‖ + ‖∫ u in Set.Ioc 0 s,
            (f_t (u : ℝ) (B u ω) + 1 / 2 * f_xx (u : ℝ) (B u ω)) ∂timeMeasure‖ :=
            (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
        _ ≤ Cf + Cf + Cd * N := by
          gcongr
          · exact hCf _ (hmem s le_rfl)
          · exact hCf _ (hmem 0 zero_le)
          · exact hint.trans (by gcongr; exact_mod_cast hsN)
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < sigmaSeq B N ω} from hpos)]
      simp only [norm_zero]
      positivity
  exact bounded_localMartingale_is_martingale (isLocalMartingale_congr_ae hloc hadapt hcad hind)
    hadapt hbound

/-- **The unrestricted-`C³` Itô formula — Summit C, in Degenne's `IsLocalMartingale` typeclass.**
For a general `C³` `f` (six partials, all jointly continuous, **no** growth or boundedness), the
compensated residual `M_t = f(t,B_t) − f(0,B_0) − ∫₀ᵗ(f_t+½f_xx)ds` is everywhere-continuous,
satisfies the Itô identity by construction, and is a genuine **`IsLocalMartingale`** on the
null-augmented Brownian filtration, localised by `σ_N = min(τ_N, N)`, `τ_N` the exit time of `B`
from `[−N, N]`: stopped there it is a bounded martingale
(`martingale_stoppedProcess_itoResidual`). Only `f`, `f_t`, `f_x`, `f_xx` and their continuity
enter the proof; the other partials are hypotheses of the statement. -/
theorem ito_formula_unrestricted (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
    (_hf_tt : ∀ t x, HasDerivAt (fun s ↦ f_t s x) (f_tt t x) t)
    (_hf_tx : ∀ t x, HasDerivAt (fun u ↦ f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
    (_hf_xxx : ∀ t x, HasDerivAt (fun u ↦ f_xx t u) (f_xxx t x) x)
    (hf_cont : Continuous fun p : ℝ × ℝ ↦ f p.1 p.2)
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)
    (_hf_tt_cont : Continuous fun p : ℝ × ℝ ↦ f_tt p.1 p.2)
    (_hf_tx_cont : Continuous fun p : ℝ × ℝ ↦ f_tx p.1 p.2)
    (_hf_xxx_cont : Continuous fun p : ℝ × ℝ ↦ f_xxx p.1 p.2) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ ω, Continuous fun t ↦ M t ω) ∧
      IsLocalMartingale M (augFiltration (μ := μ) hBmeas) μ ∧
      (∀ t : ℝ≥0, (fun ω ↦ f (t : ℝ) (B t ω) - f 0 (B 0 ω)) =ᵐ[μ]
        (fun ω ↦ M t ω + ∫ s in Set.Ioc 0 t,
          (f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω)) ∂timeMeasure)) := by
  have hMcont := continuous_itoResidual (f := f) (f_t := f_t) (f_xx := f_xx) hf_cont hf_t_cont
    hf_xx_cont hBcont
  refine ⟨itoResidual f f_t f_xx B, hMcont, ⟨fun N ↦ sigmaSeq B N,
    isLocalizingSequence_sigma hBmeas hBcont, fun N ↦ ⟨martingale_stoppedProcess_itoResidual hB
      hBmeas hBcont hf_t hf_x hf_xx hf_cont hf_t_cont hf_x_cont hf_xx_cont N,
    isStable_isCadlag _ (fun ω ↦ (hMcont ω).isCadlag) _
      ((isLocalizingSequence_sigma (μ := μ) hBmeas hBcont).isStoppingTime N)⟩⟩,
    fun t ↦ Filter.Eventually.of_forall fun ω ↦ by simp only [itoResidual]; ring⟩

/-- **The unrestricted-`C³` Itô formula in explicit local-martingale form.** The same residual `M`
and the localizing sequence `σ_N = min(τ_N, N)`; for each `N` a continuous true martingale `Mₙ`
(`M` stopped at `σ_N`, zeroed where `σ_N = 0`) with `M = Mₙ` on `{t ≤ σ_N}`. -/
theorem ito_formula_unrestricted_local (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
    (_hf_tt : ∀ t x, HasDerivAt (fun s ↦ f_t s x) (f_tt t x) t)
    (_hf_tx : ∀ t x, HasDerivAt (fun u ↦ f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
    (_hf_xxx : ∀ t x, HasDerivAt (fun u ↦ f_xx t u) (f_xxx t x) x)
    (hf_cont : Continuous fun p : ℝ × ℝ ↦ f p.1 p.2)
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)
    (_hf_tt_cont : Continuous fun p : ℝ × ℝ ↦ f_tt p.1 p.2)
    (_hf_tx_cont : Continuous fun p : ℝ × ℝ ↦ f_tx p.1 p.2)
    (_hf_xxx_cont : Continuous fun p : ℝ × ℝ ↦ f_xxx p.1 p.2) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ ω, Continuous fun t ↦ M t ω) ∧
      (∀ t : ℝ≥0, (fun ω ↦ f (t : ℝ) (B t ω) - f 0 (B 0 ω)) =ᵐ[μ]
        (fun ω ↦ M t ω + ∫ s in Set.Ioc 0 t,
          (f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω)) ∂timeMeasure)) ∧
      ∃ σ : ℕ → Ω → WithTop ℝ≥0,
        IsLocalizingSequence (augFiltration (μ := μ) hBmeas) σ μ ∧
        ∀ N : ℕ, ∃ Mₙ : ℝ≥0 → Ω → ℝ,
          Martingale Mₙ (augFiltration (μ := μ) hBmeas) μ ∧
          (∀ ω, Continuous fun t ↦ Mₙ t ω) ∧
          ∀ t : ℝ≥0, ∀ᵐ ω ∂μ, (t : WithTop ℝ≥0) ≤ σ N ω → M t ω = Mₙ t ω := by
  have hMcont := continuous_itoResidual (f := f) (f_t := f_t) (f_xx := f_xx) hf_cont hf_t_cont
    hf_xx_cont hBcont
  refine ⟨itoResidual f f_t f_xx B, hMcont,
    fun t ↦ Filter.Eventually.of_forall fun ω ↦ by simp only [itoResidual]; ring,
    fun N ↦ sigmaSeq B N, isLocalizingSequence_sigma hBmeas hBcont, fun N ↦
      ⟨_, martingale_stoppedProcess_itoResidual hB hBmeas hBcont hf_t hf_x hf_xx hf_cont
        hf_t_cont hf_x_cont hf_xx_cont N, fun ω ↦ ?_, fun t ↦ Filter.Eventually.of_forall
        fun ω hle ↦ ?_⟩⟩
  · by_cases hpos : ⊥ < sigmaSeq B N ω
    · simp only [stoppedProcess, Set.indicator_of_mem (show ω ∈ {ω | ⊥ < sigmaSeq B N ω} from hpos)]
      exact (hMcont ω).comp (LevyCharacterization.continuous_untopA_min _)
    · simp only [stoppedProcess,
        Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < sigmaSeq B N ω} from hpos)]
      exact continuous_const
  · by_cases hpos : ⊥ < sigmaSeq B N ω
    · rw [stoppedProcess_eq_of_le hle,
        Set.indicator_of_mem (show ω ∈ {ω | ⊥ < sigmaSeq B N ω} from hpos)]
    · have ht : t = 0 :=
        le_antisymm (WithTop.coe_le_coe.1 (hle.trans (not_lt.1 hpos))) zero_le
      subst ht
      have h1 : itoResidual f f_t f_xx B 0 ω = 0 := by simp [itoResidual]
      rw [h1]
      simp only [stoppedProcess]
      rw [Set.indicator_of_notMem (show ω ∉ {ω | ⊥ < sigmaSeq B N ω} from hpos)]

end MathFin
