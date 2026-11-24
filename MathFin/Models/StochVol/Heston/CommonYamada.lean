/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonItoTime
public import MathFin.Models.StochVol.Heston.CIRYamada

/-!
# Yamada–Watanabe pathwise uniqueness on the common filtration

## Main results

* `contProcess_of_predictable`
* `lp_eq_of_pathwise`
* `heston_unique_common`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston
open MathFin.FilteredIto
namespace CommonYamada

open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonL2
      MathFin.FilteredIto.CommonPredictable MathFin.FilteredIto.CommonIntegral
  MathFin.FilteredIto.CommonProcess MathFin.FilteredIto.CommonProcessGeneral
        MathFin.FilteredIto.CommonContinuous
  MathFin.FilteredIto.CommonLocality MathFin.FilteredIto.CommonStopping
        MathFin.FilteredIto.CommonRiemann MathFin.FilteredIto.CommonCovariation
  MathFin.FilteredIto.CommonHorizon MathFin.FilteredIto.CommonIto
open scoped NNReal ENNReal

local notation "leb" => MathFin.ItoIntegralL2.timeMeasure

/-! ### One-dimensional test functions -/

lemma norm_proj_unit_le : ‖(ContinuousLinearMap.proj () : (Unit → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul]; exact norm_le_pi_norm y ()

/-- A real `C²` function with bounded first and second derivatives and uniformly continuous
second derivative gives an Itô test function on `Unit → ℝ`. -/
theorem itoTest_unit {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {C₁ C₂ : ℝ}
    (h1 : ∀ x, |deriv g x| ≤ C₁) (h2 : ∀ x, |deriv (deriv g) x| ≤ C₂)
    (hu : ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ, |x - y| < δ →
      |deriv (deriv g) x - deriv (deriv g) y| < ε) :
    ItoTest (fun y : Unit → ℝ ↦ g (y ())) C₁ C₂ ∧
      (∀ i y, pd (fun y : Unit → ℝ ↦ g (y ())) i y = deriv g (y ())) ∧
      (∀ i k y, pd2 (fun y : Unit → ℝ ↦ g (y ())) i k y = deriv (deriv g) (y ())) := by
  set P : (Unit → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj () with hP
  have hd1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hg1 : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hd2 : Differentiable ℝ (deriv g) := hg1.differentiable one_ne_zero
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans (h1 0)
  have hC₂ : 0 ≤ C₂ := (abs_nonneg _).trans (h2 0)
  have hF1 : ∀ y, fderiv ℝ (fun y : Unit → ℝ ↦ g (y ())) y = deriv g (y ()) • P := fun y =>
    ((hd1 (y ())).hasDerivAt.comp_hasFDerivAt y P.hasFDerivAt).fderiv
  have hFfun : fderiv ℝ (fun y : Unit → ℝ ↦ g (y ())) = fun y ↦ deriv g (y ()) • P :=
    funext hF1
  have hSR : ∀ d : ℝ, (d • P).smulRight P = d • P.smulRight P := fun d =>
    ContinuousLinearMap.ext fun h => ContinuousLinearMap.ext fun k => by
      simp only [ContinuousLinearMap.smulRight_apply, _root_.smul_apply, smul_eq_mul]
      ring
  have hF2 : ∀ y, fderiv ℝ (fderiv ℝ (fun y : Unit → ℝ ↦ g (y ()))) y
      = deriv (deriv g) (y ()) • P.smulRight P := by
    intro y
    rw [hFfun, ← hSR]
    exact (((hd2 (y ())).hasDerivAt.comp_hasFDerivAt y P.hasFDerivAt).smul_const P).fderiv
  have hPn : ‖P‖ ≤ 1 := norm_proj_unit_le
  have hPP : ‖P.smulRight P‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc ‖P‖ * ‖P‖ ≤ 1 * 1 := mul_le_mul hPn hPn (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  refine ⟨⟨hg.comp P.contDiff, fun y => ?_, fun y => ?_, fun ε hε => ?_⟩, fun i y => ?_,
    fun i k y => ?_⟩
  · rw [hF1]
    calc ‖deriv g (y ()) • P‖ ≤ ‖deriv g (y ())‖ * ‖P‖ :=
          ContinuousLinearMap.opNorm_smul_le (deriv g (y ())) P
      _ ≤ C₁ * 1 := mul_le_mul (by rw [Real.norm_eq_abs]; exact h1 _) hPn P.opNorm_nonneg hC₁
      _ = C₁ := mul_one _
  · rw [hF2]
    calc ‖deriv (deriv g) (y ()) • P.smulRight P‖
        ≤ ‖deriv (deriv g) (y ())‖ * ‖P.smulRight P‖ :=
          ContinuousLinearMap.opNorm_smul_le (deriv (deriv g) (y ())) (P.smulRight P)
      _ ≤ C₂ * 1 := mul_le_mul (by rw [Real.norm_eq_abs]; exact h2 _) hPP
          (P.smulRight P).opNorm_nonneg hC₂
      _ = C₂ := mul_one _
  · obtain ⟨δ, hδ, hδε⟩ := hu ε hε
    refine ⟨δ, hδ, fun y z hyz => ?_⟩
    rw [hF2, hF2]
    have hc : |y () - z ()| < δ := by
      have : |(y - z) ()| ≤ ‖y - z‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ ()
      exact lt_of_le_of_lt this hyz
    calc ‖deriv (deriv g) (y ()) • P.smulRight P - deriv (deriv g) (z ()) • P.smulRight P‖
        = ‖(deriv (deriv g) (y ()) - deriv (deriv g) (z ())) • P.smulRight P‖ :=
          congrArg norm (sub_smul (deriv (deriv g) (y ())) (deriv (deriv g) (z ()))
            (P.smulRight P)).symm
      _ ≤ ‖deriv (deriv g) (y ()) - deriv (deriv g) (z ())‖ * ‖P.smulRight P‖ :=
          ContinuousLinearMap.opNorm_smul_le (deriv (deriv g) (y ()) - deriv (deriv g) (z ()))
            (P.smulRight P)
      _ ≤ ‖deriv (deriv g) (y ()) - deriv (deriv g) (z ())‖ * 1 :=
          mul_le_mul_of_nonneg_left hPP (norm_nonneg _)
      _ < ε := by rw [mul_one, Real.norm_eq_abs]; exact hδε _ _ hc
  · cases i
    simp [pd, hF1, hP]
  · cases i; cases k
    simp [pd2, hF2, hP]

lemma yamada_psi_abs_unif (p : YamadaParams) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ, |x - y| < δ →
      |yamadaPsi p (|x|) - yamadaPsi p (|y|)| < ε := by
  intro ε hε
  have hc : Continuous fun x : ℝ ↦ yamadaPsi p (|x|) :=
    (yamada_continuous_psi p).comp continuous_abs
  have huc := (isCompact_Icc (a := -(p.b + 1)) (b := p.b + 1)).uniformContinuousOn_of_continuous
    hc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδε⟩ := huc ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun x y hxy => ?_⟩
  have hzero : ∀ z : ℝ, p.b < |z| → yamadaPsi p (|z|) = 0 := fun z hz => yamada_psi_of_gt p hz
  have hxy1 : |x - y| < 1 := lt_of_lt_of_le hxy (min_le_right _ _)
  have hxyδ : |x - y| < δ := lt_of_lt_of_le hxy (min_le_left _ _)
  by_cases hx : |x| ≤ p.b + 1
  · by_cases hy : |y| ≤ p.b + 1
    · have h := hδε x ⟨(abs_le.mp hx).1, (abs_le.mp hx).2⟩ y ⟨(abs_le.mp hy).1, (abs_le.mp hy).2⟩
        (by rwa [Real.dist_eq])
      rwa [Real.dist_eq] at h
    · have hy' : p.b + 1 < |y| := not_le.mp hy
      have hxb : p.b < |x| := by
        have := abs_sub_abs_le_abs_sub y x
        rw [abs_sub_comm] at this
        linarith
      rw [hzero x hxb, hzero y (by linarith), sub_self, abs_zero]
      exact hε
  · have hx' : p.b + 1 < |x| := not_le.mp hx
    have hyb : p.b < |y| := by
      have := abs_sub_abs_le_abs_sub x y
      linarith
    rw [hzero x (by linarith), hzero y hyb, sub_self, abs_zero]
    exact hε

/-! ### Linearity and zero mean of the continuous Itô process -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℝ≥0 mΩ} {B Z W : ℝ≥0 → Ω → ℝ}

lemma itoContinuousMod_sub_ae (hW : BrownianOn ℱ W μ)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) (T : ℝ≥0)
    (φ ψ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, itoContinuousMod T hW.measurable (φ - ψ) t ω
      = itoContinuousMod T hW.measurable φ t ω - itoContinuousMod T hW.measurable ψ t ω := by
  refine ae_forall_eq_of_continuousOn' (itoContinuousMod_continuousOn hW T hW.measurable hWc _)
    ?_ fun t ht => ?_
  · filter_upwards [itoContinuousMod_continuousOn hW T hW.measurable hWc φ,
      itoContinuousMod_continuousOn hW T hW.measurable hWc ψ] with ω h1 h2
    exact h1.sub h2
  · filter_upwards [itoContinuousMod_modification hW T hW.measurable hWc (φ - ψ) ht,
      itoContinuousMod_modification hW T hW.measurable hWc φ ht,
      itoContinuousMod_modification hW T hW.measurable hWc ψ ht,
      Lp.coeFn_sub (itoProcessCLM hW T t hW.measurable φ) (itoProcessCLM hW T t hW.measurable ψ)]
      with ω e1 e2 e3 e4
    rw [e1, map_sub, e4, Pi.sub_apply, ← e2, ← e3]

lemma itoContinuousMod_zero_kernel (hW : BrownianOn ℱ W μ)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T,
      itoContinuousMod T hW.measurable (0 : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) t ω = 0 := by
  refine ae_forall_eq_of_continuousOn' (Y := fun _ _ ↦ (0 : ℝ))
    (itoContinuousMod_continuousOn hW T hW.measurable hWc _)
    (Eventually.of_forall fun _ => continuousOn_const) fun t ht => ?_
  filter_upwards [itoContinuousMod_modification hW T hW.measurable hWc 0 ht,
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with ω e1 e2
  rw [e1, map_zero, e2, Pi.zero_apply]

lemma integral_itoContinuousMod (hW : BrownianOn ℱ W μ)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) {t T : ℝ≥0} (htT : t ≤ T)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    Integrable (fun ω ↦ itoContinuousMod T hW.measurable φ t ω) μ ∧
      ∫ ω, itoContinuousMod T hW.measurable φ t ω ∂μ = 0 := by
  have h1 := itoContinuousMod_modification hW T hW.measurable hWc φ htT
  rw [← itoIntegralCLM_T_restrictKernel hW htT hW.measurable] at h1
  refine ⟨((Lp.memLp _).integrable one_le_two).congr h1.symm, ?_⟩
  rw [integral_congr_ae h1]
  exact integral_itoIntegralCLM_T hW t hW.measurable _

/-! ### The Yamada estimate on the common filtration -/

theorem yamada_estimate_common (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} (p : YamadaParams) {κ A c x₀ : ℝ} (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hc : 0 ≤ c)
    {X₁ X₂ a₁ a₂ b₁ b₂ : ℝ≥0 → Ω → ℝ} {H₁ H₂ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)}
    (hX₁ : ContProcess ℱ μ T X₁) (hX₂ : ContProcess ℱ μ T X₂)
    (hb₁ : ContProcess ℱ μ T b₁) (hb₂ : ContProcess ℱ μ T b₂)
    (ha₁ : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ a₁ t ω) (Set.Icc 0 T))
    (ha₂ : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ a₂ t ω) (Set.Icc 0 T))
    (hH₁ : ⇑H₁ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ b₁ z.1 z.2)
    (hH₂ : ⇑H₂ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ b₂ z.1 z.2)
    (hdrift : ∀ᵐ ω ∂μ, ∀ s ≤ T, a₁ s ω - a₂ s ω = -κ * (X₁ s ω - X₂ s ω))
    (hdiff : ∀ᵐ ω ∂μ, ∀ s ≤ T, (b₁ s ω - b₂ s ω) ^ 2 ≤ A * |X₁ s ω - X₂ s ω| + c)
    (heq₁ : ∀ᵐ ω ∂μ, ∀ t ≤ T, X₁ t ω = x₀ + ∫ s in Set.Ioc 0 t, a₁ s ω ∂leb
      + itoContinuousMod T hP.left.measurable H₁ t ω)
    (heq₂ : ∀ᵐ ω ∂μ, ∀ t ≤ T, X₂ t ω = x₀ + ∫ s in Set.Ioc 0 t, a₂ s ω ∂leb
      + itoContinuousMod T hP.left.measurable H₂ t ω)
    {t : ℝ≥0} (htT : t ≤ T) :
    Integrable (fun ω ↦ |X₁ t ω - X₂ t ω|) μ ∧
      ∫ ω, |X₁ t ω - X₂ t ω| ∂μ ≤ p.b + (A / yamadaM p + c / (yamadaM p * p.a)) * t := by
  have hDproc : ItoProc hP T (fun _ : Unit ↦ fun s ω ↦ X₁ s ω - X₂ s ω) (fun _ ↦ 0)
      (fun _ s ω ↦ a₁ s ω - a₂ s ω) (fun _ s ω ↦ b₁ s ω - b₂ s ω) (fun _ _ _ ↦ (0 : ℝ))
      (fun _ ↦ H₁ - H₂) (fun _ ↦ 0) :=
    { proc := fun _ => ⟨fun s => (hX₁.adapted s).sub (hX₂.adapted s), hX₁.pred.sub hX₂.pred, by
        filter_upwards [hX₁.cont, hX₂.cont] with ω h1 h2
        exact h1.sub h2⟩
      drift := by
        filter_upwards [ha₁, ha₂] with ω h1 h2 _
        exact h1.sub h2
      diffB := fun _ => ⟨fun s => (hb₁.adapted s).sub (hb₂.adapted s), hb₁.pred.sub hb₂.pred, by
        filter_upwards [hb₁.cont, hb₂.cont] with ω h1 h2
        exact h1.sub h2⟩
      diffZ := fun _ => ⟨fun _ => measurable_const, measurable_const,
        Eventually.of_forall fun _ => continuousOn_const⟩
      kerB := fun _ => by
        filter_upwards [Lp.coeFn_sub H₁ H₂, hH₁, hH₂] with z h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3]
      kerZ := fun _ => by
        filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := trimMeasureT (μ := μ) T ℱ)]
          with z hz
        rw [hz, Pi.zero_apply]
      eq := by
        filter_upwards [heq₁, heq₂, ha₁, ha₂, itoContinuousMod_sub_ae hP.left hBc T H₁ H₂,
          itoContinuousMod_zero_kernel hP.right hZc T] with ω e1 e2 h1 h2 e3 e4 _ s hs
        have i1 : IntegrableOn (fun u ↦ a₁ u ω) (Set.Ioc 0 s) leb :=
          integrableOn_of_continuousOn (h1.mono (Set.Icc_subset_Icc le_rfl hs))
        have i2 : IntegrableOn (fun u ↦ a₂ u ω) (Set.Ioc 0 s) leb :=
          integrableOn_of_continuousOn (h2.mono (Set.Icc_subset_Icc le_rfl hs))
        show X₁ s ω - X₂ s ω = 0 + ∫ u in Set.Ioc 0 s, (a₁ u ω - a₂ u ω) ∂leb
          + itoContinuousMod T hP.left.measurable (H₁ - H₂) s ω
          + itoContinuousMod T hP.right.measurable 0 s ω
        rw [e1 s hs, e2 s hs, integral_sub i1 i2, e3 s hs, e4 s hs]
        ring }
  have hd1 : deriv (yamadaPhi p) = yamadaPhiPrime p :=
    funext fun x => (yamada_hasDerivAt_phi p x).deriv
  have hd2 : deriv (deriv (yamadaPhi p)) = fun x ↦ yamadaPsi p (|x|) := by
    rw [hd1]; exact funext fun x => (yamada_hasDerivAt_phiPrime p x).deriv
  obtain ⟨hf, hpd, hpd2⟩ := itoTest_unit (yamada_contDiff_phi p) (C₁ := 1)
    (C₂ := 2 / (yamadaM p * p.a))
    (fun x => by rw [hd1]; exact yamada_abs_phiPrime_le_one p x)
    (fun x => by rw [hd2]; exact abs_yamada_psi_abs_le p x)
    (by rw [hd2]; exact yamada_psi_abs_unif p)
  have hIto := ito_formula_at hP hBc hZc hDproc hf htT
  have hd2' : deriv (yamadaPhiPrime p) = fun x ↦ yamadaPsi p (|x|) :=
    funext fun x => (yamada_hasDerivAt_phiPrime p x).deriv
  simp only [Fintype.sum_unique] at hIto
  set K := A / yamadaM p + c / (yamadaM p * p.a) with hK
  have hm := yamada_m_pos p
  have ha := p.ha_pos
  have hK0 : 0 ≤ K := add_nonneg (div_nonneg hA hm.le) (div_nonneg hc (mul_pos hm ha).le)
  obtain ⟨iM₁, eM₁⟩ := integral_itoContinuousMod hP.left hBc htT
    (mulKernel T (goodProcess_pd hDproc.proc hf default).pred
      (goodProcess_pd hDproc.proc hf default).bdd (H₁ - H₂))
  obtain ⟨iM₂, eM₂⟩ := integral_itoContinuousMod hP.right hZc htT
    (mulKernel T (goodProcess_pd hDproc.proc hf default).pred
      (goodProcess_pd hDproc.proc hf default).bdd (0 : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)))
  have key : ∀ (D b I M N K' t' : ℝ), |D| - b ≤ 0 + I + M + N → I ≤ K' * t' →
      |D| ≤ b + K' * t' + (M + N) := by
    intro D b I M N K' t' h1 h2
    linarith
  have hbound : ∀ᵐ ω ∂μ, |X₁ t ω - X₂ t ω| ≤ p.b + K * t
      + (itoContinuousMod T hP.left.measurable (mulKernel T (goodProcess_pd hDproc.proc hf
            default).pred
          (goodProcess_pd hDproc.proc hf default).bdd (H₁ - H₂)) t ω
        + itoContinuousMod T hP.right.measurable (mulKernel T (goodProcess_pd hDproc.proc hf
              default).pred
          (goodProcess_pd hDproc.proc hf default).bdd (0 : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)))
                t ω) := by
    filter_upwards [hIto, hdrift, hdiff] with ω hω hdr hdf
    have hlow := yamada_sub_le_phi p (X₁ t ω - X₂ t ω)
    rw [hω, yamada_phi_zero] at hlow
    refine key _ _ _ _ _ _ _ hlow ?_
    · refine setIntegral_le_of_ae_le_const hK0
        (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
      have hsT : s ≤ T := hs.2.trans htT
      simp only [hpd, hpd2, hd1, hd2']
      rw [hdr s hsT]
      have h1 : yamadaPhiPrime p (X₁ s ω - X₂ s ω) * (-κ * (X₁ s ω - X₂ s ω)) ≤ 0 := by
        have := yamada_phiPrime_mul_self_nonneg p (X₁ s ω - X₂ s ω)
        nlinarith
      have h2 : yamadaPsi p (|X₁ s ω - X₂ s ω|)
            * ((b₁ s ω - b₂ s ω) * (b₁ s ω - b₂ s ω) + 0 * 0)
          ≤ yamadaPsi p (|X₁ s ω - X₂ s ω|) * (A * |X₁ s ω - X₂ s ω| + c) := by
        have := hdf s hsT
        refine mul_le_mul_of_nonneg_left ?_ (yamada_psi_nonneg p _)
        nlinarith
      have h3 : yamadaPsi p (|X₁ s ω - X₂ s ω|) * (A * |X₁ s ω - X₂ s ω| + c) ≤ 2 * K := by
        have e1 := yamada_psi_abs_mul_abs_le p (X₁ s ω - X₂ s ω)
        have e3 : yamadaPsi p (|X₁ s ω - X₂ s ω|) ≤ 2 / (yamadaM p * p.a) :=
          (le_abs_self _).trans (abs_yamada_psi_abs_le p (X₁ s ω - X₂ s ω))
        calc yamadaPsi p (|X₁ s ω - X₂ s ω|) * (A * |X₁ s ω - X₂ s ω| + c)
            = A * (yamadaPsi p (|X₁ s ω - X₂ s ω|) * |X₁ s ω - X₂ s ω|)
              + c * yamadaPsi p (|X₁ s ω - X₂ s ω|) := by ring
          _ ≤ A * (2 / yamadaM p) + c * (2 / (yamadaM p * p.a)) :=
              add_le_add (mul_le_mul_of_nonneg_left e1 hA) (mul_le_mul_of_nonneg_left e3 hc)
          _ = 2 * K := by rw [hK]; ring
      linarith
  have iMM : Integrable (fun ω ↦ itoContinuousMod T hP.left.measurable (mulKernel T
        (goodProcess_pd hDproc.proc hf default).pred
          (goodProcess_pd hDproc.proc hf default).bdd (H₁ - H₂)) t ω
      + itoContinuousMod T hP.right.measurable (mulKernel T (goodProcess_pd hDproc.proc hf
            default).pred
          (goodProcess_pd hDproc.proc hf default).bdd (0 : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)))
                t ω) μ := iM₁.add iM₂
  have iub : Integrable (fun ω ↦ p.b + K * t + (itoContinuousMod T hP.left.measurable (mulKernel
        T (goodProcess_pd hDproc.proc hf default).pred
          (goodProcess_pd hDproc.proc hf default).bdd (H₁ - H₂)) t ω
      + itoContinuousMod T hP.right.measurable (mulKernel T (goodProcess_pd hDproc.proc hf
            default).pred
          (goodProcess_pd hDproc.proc hf default).bdd (0 : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)))
                t ω)) μ := (integrable_const (p.b + K * t)).add iMM
  have hmeas : AEStronglyMeasurable (fun ω ↦ |X₁ t ω - X₂ t ω|) μ :=
    ((((hX₁.adapted t).mono (ℱ.le t) le_rfl).sub
      ((hX₂.adapted t).mono (ℱ.le t) le_rfl)).abs).aestronglyMeasurable
  refine ⟨iub.mono' hmeas ?_, ?_⟩
  · filter_upwards [hbound] with ω hω
    rwa [Real.norm_eq_abs, abs_abs]
  · calc ∫ ω, |X₁ t ω - X₂ t ω| ∂μ ≤ ∫ ω, (p.b + K * t + (itoContinuousMod T hP.left.measurable
        (mulKernel T (goodProcess_pd hDproc.proc hf default).pred
          (goodProcess_pd hDproc.proc hf default).bdd (H₁ - H₂)) t ω
          + itoContinuousMod T hP.right.measurable (mulKernel T (goodProcess_pd hDproc.proc hf
                default).pred
          (goodProcess_pd hDproc.proc hf default).bdd (0 : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)))
                t ω)) ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) iub hbound
      _ = p.b + K * t := by
          rw [integral_add (integrable_const _) iMM, integral_add iM₁ iM₂, eM₁, eM₂,
            integral_const]
          simp

/-- **Pathwise uniqueness for dissipative Itô equations with Hölder-½ diffusion**, on the
common filtration (Yamada–Watanabe). -/
theorem pathwise_unique_common (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} {κ A x₀ : ℝ} (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    {X₁ X₂ a₁ a₂ b₁ b₂ : ℝ≥0 → Ω → ℝ} {H₁ H₂ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)}
    (hX₁ : ContProcess ℱ μ T X₁) (hX₂ : ContProcess ℱ μ T X₂)
    (hb₁ : ContProcess ℱ μ T b₁) (hb₂ : ContProcess ℱ μ T b₂)
    (ha₁ : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ a₁ t ω) (Set.Icc 0 T))
    (ha₂ : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ a₂ t ω) (Set.Icc 0 T))
    (hH₁ : ⇑H₁ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ b₁ z.1 z.2)
    (hH₂ : ⇑H₂ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ b₂ z.1 z.2)
    (hdrift : ∀ᵐ ω ∂μ, ∀ s ≤ T, a₁ s ω - a₂ s ω = -κ * (X₁ s ω - X₂ s ω))
    (hdiff : ∀ᵐ ω ∂μ, ∀ s ≤ T, (b₁ s ω - b₂ s ω) ^ 2 ≤ A * |X₁ s ω - X₂ s ω|)
    (heq₁ : ∀ᵐ ω ∂μ, ∀ t ≤ T, X₁ t ω = x₀ + ∫ s in Set.Ioc 0 t, a₁ s ω ∂leb
      + itoContinuousMod T hP.left.measurable H₁ t ω)
    (heq₂ : ∀ᵐ ω ∂μ, ∀ t ≤ T, X₂ t ω = x₀ + ∫ s in Set.Ioc 0 t, a₂ s ω ∂leb
      + itoContinuousMod T hP.left.measurable H₂ t ω) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, X₁ t ω = X₂ t ω := by
  have hdiff' : ∀ᵐ ω ∂μ, ∀ s ≤ T, (b₁ s ω - b₂ s ω) ^ 2 ≤ A * |X₁ s ω - X₂ s ω| + 0 := by
    filter_upwards [hdiff] with ω hω s hs
    rw [add_zero]; exact hω s hs
  refine ae_forall_eq_of_continuousOn' hX₁.cont hX₂.cont fun t htT => ?_
  have hest : ∀ n : ℕ, ∫ ω, |X₁ t ω - X₂ t ω| ∂μ ≤ (1 + A * t) * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hb : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h := (yamada_estimate_common hP hBc hZc (yamadaParamsOf _ _ hb hm) hκ hA le_rfl
      hX₁ hX₂ hb₁ hb₂ ha₁ ha₂ hH₁ hH₂ hdrift hdiff' heq₁ heq₂ htT).2
    rw [yamada_m_yamadaParamsOf, yamadaParamsOf_b, zero_div, add_zero] at h
    calc _ ≤ _ := h
      _ = (1 + A * t) * (1 / ((n : ℝ) + 1)) := by ring
  have hlim : Tendsto (fun n : ℕ => (1 + A * t) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 + A * (t : ℝ))
  have h0 : ∫ ω, |X₁ t ω - X₂ t ω| ∂μ ≤ 0 := ge_of_tendsto' hlim hest
  have hint := (yamada_estimate_common hP hBc hZc (yamadaParamsOf 1 1 one_pos one_pos) hκ hA
    le_rfl hX₁ hX₂ hb₁ hb₂ ha₁ ha₂ hH₁ hH₂ hdrift hdiff' heq₁ heq₂ htT).1
  have hzero := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg _) hint).1
    (le_antisymm h0 (integral_nonneg fun ω => abs_nonneg _))
  filter_upwards [hzero] with ω hω
  exact sub_eq_zero.1 (abs_eq_zero.1 hω)

lemma xi_sqrt_eq_cirSqrtDiffusion (p : Parameters) (x : ℝ) :
    p.xi * Real.sqrt x = cirSqrtDiffusion p x := by
  unfold cirSqrtDiffusion
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx]
  · rw [max_eq_right hx, Real.sqrt_eq_zero'.mpr hx, Real.sqrt_zero]

omit [IsProbabilityMeasure μ] in
lemma contProcess_xi_sqrt {T : ℝ≥0} (p : Parameters) {V : ℝ≥0 → Ω → ℝ}
    (hV : ContProcess ℱ μ T V) :
    ContProcess ℱ μ T (fun s ω ↦ p.xi * Real.sqrt (V s ω)) where
  adapted s := (Real.continuous_sqrt.measurable.comp (hV.adapted s)).const_mul p.xi
  pred := (Real.continuous_sqrt.measurable.comp hV.pred).const_mul p.xi
  cont := by
    filter_upwards [hV.cont] with ω hω
    exact continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hω)

/-- **CIR pathwise uniqueness on the common filtration.** Any two continuous adapted solutions
of `dV = κ(θ − V) dt + ξ √V dB` with the same initial value agree almost surely on `[0, T]`. -/
theorem cir_unique_common (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} (p : Parameters) (hκ : 0 ≤ p.kappa) {v₀ : ℝ}
    {V₁ V₂ : ℝ≥0 → Ω → ℝ} {H₁ H₂ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)}
    (hV₁ : ContProcess ℱ μ T V₁) (hV₂ : ContProcess ℱ μ T V₂)
    (hH₁ : ⇑H₁ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ p.xi * Real.sqrt (V₁ z.1 z.2))
    (hH₂ : ⇑H₂ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ p.xi * Real.sqrt (V₂ z.1 z.2))
    (heq₁ : ∀ᵐ ω ∂μ, ∀ t ≤ T, V₁ t ω = v₀
      + ∫ s in Set.Ioc 0 t, p.kappa * (p.theta - V₁ s ω) ∂leb
      + itoContinuousMod T hP.left.measurable H₁ t ω)
    (heq₂ : ∀ᵐ ω ∂μ, ∀ t ≤ T, V₂ t ω = v₀
      + ∫ s in Set.Ioc 0 t, p.kappa * (p.theta - V₂ s ω) ∂leb
      + itoContinuousMod T hP.left.measurable H₂ t ω) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, V₁ t ω = V₂ t ω := by
  refine pathwise_unique_common hP hBc hZc (κ := p.kappa) (A := p.xi ^ 2)
    (a₁ := fun s ω ↦ p.kappa * (p.theta - V₁ s ω))
    (a₂ := fun s ω ↦ p.kappa * (p.theta - V₂ s ω)) hκ (sq_nonneg _) hV₁ hV₂
    (contProcess_xi_sqrt p hV₁) (contProcess_xi_sqrt p hV₂) ?_ ?_ hH₁ hH₂ ?_ ?_ heq₁ heq₂
  · filter_upwards [hV₁.cont] with ω hω
    exact continuousOn_const.mul (continuousOn_const.sub hω)
  · filter_upwards [hV₂.cont] with ω hω
    exact continuousOn_const.mul (continuousOn_const.sub hω)
  · exact Eventually.of_forall fun ω s _ => by ring
  · refine Eventually.of_forall fun ω s _ => ?_
    rw [xi_sqrt_eq_cirSqrtDiffusion, xi_sqrt_eq_cirSqrtDiffusion]
    exact cirSqrtDiffusion_sub_sq_le p _ _

/-! ### Heston pair uniqueness -/

omit [IsProbabilityMeasure μ] in
/-- A predictable process with a.s. continuous paths on `[0, T]` is a `ContProcess`. -/
lemma contProcess_of_predictable {T : ℝ≥0} {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyPredictable ℱ X)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Set.Icc 0 T)) : ContProcess ℱ μ T X :=
  ⟨fun t => (hX.stronglyAdapted t).measurable, hX.measurable, hc⟩

/-- Two `L²` kernels representing integrands that agree pathwise a.s. on `[0, T]` coincide. -/
lemma lp_eq_of_pathwise {T : ℝ≥0} {H₁ H₂ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)}
    {f₁ f₂ : ℝ≥0 × Ω → ℝ}
    (hf₁ : Measurable[ℱ.predictable] f₁) (hf₂ : Measurable[ℱ.predictable] f₂)
    (hH₁ : ⇑H₁ =ᵐ[trimMeasureT (μ := μ) T ℱ] f₁) (hH₂ : ⇑H₂ =ᵐ[trimMeasureT (μ := μ) T ℱ] f₂)
    (h : ∀ᵐ ω ∂μ, ∀ t ≤ T, f₁ (t, ω) = f₂ (t, ω)) : H₁ = H₂ := by
  have hset : MeasurableSet[ℱ.predictable] {z : ℝ≥0 × Ω | f₁ z = f₂ z} :=
    measurableSet_eq_fun hf₁ hf₂
  have h12 : ∀ᵐ z ∂(trimMeasureT (μ := μ) T ℱ), f₁ z = f₂ z := by
    refine ae_trim_of_ae_ae (P := fun z ↦ f₁ z = f₂ z) hset ?_
    filter_upwards [(ae_restrict_mem measurableSet_Ioc :
      ∀ᵐ s ∂(timeMeasureT T), s ∈ Set.Ioc 0 T)] with s hs
    filter_upwards [h] with ω hω using hω s hs.2
  apply Lp.ext
  filter_upwards [hH₁, hH₂, h12] with z h1 h2 h3
  rw [h1, h2, h3]

/-- **Pathwise uniqueness of the Heston state on the common filtration.** Two continuous
predictable solutions `(X, V)` of the Heston system with the same initial data, driven by the
same pair of independent Brownian motions, agree almost surely on `[0, T]`. -/
theorem heston_unique_common (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} (p : Parameters) (hκ : 0 ≤ p.kappa) (hρ : |p.rho| ≤ 1) {x₀ v₀ : ℝ}
    {X₁ V₁ X₂ V₂ : ℝ≥0 → Ω → ℝ} {Hv₁ Hx₁ Hv₂ Hx₂ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)}
    (hpV₁ : IsStronglyPredictable ℱ V₁) (hpV₂ : IsStronglyPredictable ℱ V₂)
    (hcV₁ : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ V₁ t ω) (Set.Icc 0 T))
    (hcV₂ : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ V₂ t ω) (Set.Icc 0 T))
    (hHv₁ : ⇑Hv₁ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ p.xi * Real.sqrt (V₁ z.1 z.2))
    (hHv₂ : ⇑Hv₂ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ p.xi * Real.sqrt (V₂ z.1 z.2))
    (hHx₁ : ⇑Hx₁ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ Real.sqrt (V₁ z.1 z.2))
    (hHx₂ : ⇑Hx₂ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ Real.sqrt (V₂ z.1 z.2))
    (heqV₁ : ∀ᵐ ω ∂μ, ∀ t ≤ T, V₁ t ω = v₀
      + (∫ s in Set.Ioc 0 t, p.kappa * (p.theta - V₁ s ω) ∂leb)
      + itoContinuousMod T hP.left.measurable Hv₁ t ω)
    (heqV₂ : ∀ᵐ ω ∂μ, ∀ t ≤ T, V₂ t ω = v₀
      + (∫ s in Set.Ioc 0 t, p.kappa * (p.theta - V₂ s ω) ∂leb)
      + itoContinuousMod T hP.left.measurable Hv₂ t ω)
    (heqX₁ : ∀ᵐ ω ∂μ, ∀ t ≤ T, X₁ t ω = x₀
      + (∫ s in Set.Ioc 0 t, (p.r - p.q) - (1 / 2 : ℝ) * V₁ s ω ∂leb)
      + itoContinuousMod T (hP.correlated_brownian hρ).measurable Hx₁ t ω)
    (heqX₂ : ∀ᵐ ω ∂μ, ∀ t ≤ T, X₂ t ω = x₀
      + (∫ s in Set.Ioc 0 t, (p.r - p.q) - (1 / 2 : ℝ) * V₂ s ω ∂leb)
      + itoContinuousMod T (hP.correlated_brownian hρ).measurable Hx₂ t ω) :
    (∀ᵐ ω ∂μ, ∀ t ≤ T, V₁ t ω = V₂ t ω) ∧ (∀ᵐ ω ∂μ, ∀ t ≤ T, X₁ t ω = X₂ t ω) := by
  have hV := cir_unique_common hP hBc hZc p hκ (contProcess_of_predictable hpV₁ hcV₁)
    (contProcess_of_predictable hpV₂ hcV₂) hHv₁ hHv₂ heqV₁ heqV₂
  refine ⟨hV, ?_⟩
  have hHx : Hx₁ = Hx₂ := by
    refine lp_eq_of_pathwise (Real.continuous_sqrt.measurable.comp hpV₁.measurable)
      (Real.continuous_sqrt.measurable.comp hpV₂.measurable) hHx₁ hHx₂ ?_
    filter_upwards [hV] with ω hω t ht
    show Real.sqrt (V₁ t ω) = Real.sqrt (V₂ t ω)
    rw [hω t ht]
  rw [hHx] at heqX₁
  filter_upwards [heqX₁, heqX₂, hV] with ω h1 h2 hv t ht
  rw [h1 t ht, h2 t ht]
  have hI : ∫ s in Set.Ioc 0 t, (p.r - p.q) - (1 / 2 : ℝ) * V₁ s ω ∂leb
      = ∫ s in Set.Ioc 0 t, (p.r - p.q) - (1 / 2 : ℝ) * V₂ s ω ∂leb :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs => by
      simp only [hv s (hs.2.trans ht)]
  rw [hI]

end CommonYamada
end MathFin.Heston
