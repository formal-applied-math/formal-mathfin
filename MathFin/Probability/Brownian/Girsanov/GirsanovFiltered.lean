/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.Girsanov.GirsanovPredictableTheta
public import MathFin.Probability.Brownian.ExpMartingaleBrownian
public import MathFin.Probability.Brownian.BrownianExpMoment
public import MathFin.Probability.Gaussian.GaussianMoments

/-! # Girsanov's theorem for the filtration: `B^θ` is a `Q`-Brownian motion

`Btheta_isQBrownianMotion_predictable_of_bdd` fixes the finite-dimensional laws of the
drift-corrected process `B^θ_u = B_u + driftContinuousMod θ̂ u` under `Q = Z_T·μ` on `[0, T]`.
This file upgrades the conclusion for a bounded predictable `θ` to Brownian motion *for the
filtration*, on the whole time axis, and, when `B` has almost surely continuous paths, with
continuous paths:

* `B^θ` is constant-drift after `T` (`driftContinuousMod_of_ge`): for `t ≥ T` it is
  `B_t + (drift at T)`, so past `T` it moves as `B` does.
* The density `Z_T` is a.e. `𝓕_T`-measurable (`aestronglyMeasurable_ZTpred`): it is the a.e. limit
  of the simple Doléans densities, which are `𝓕_T`-measurable.
* Hence, for `T ≤ s ≤ t`, the exponential `exp(a B^θ_t − a²t/2)` is a `Q`-martingale step: under `μ`
  its ratio to the `s`-value is `exp(a(B_t − B_s) − a²(t−s)/2)`, independent of `𝓕_s` of mean one
  (`setIntegral_expBthetaPred_tail`). With the existing martingale identity on `[0, T]`
  (`isExpQMartingale_BthetaPredictable`) this gives `IsExpQMartingale Q 𝓕 B^θ T'` for every `T'`
  (`isExpQMartingale_BthetaPredictable_all`).
* The exponential-martingale characterisation of the library
  (`isFilteredPreBrownian_of_expMartingale`) then reads off `IsFilteredPreBrownian B^θ 𝓕 Q`:
  independence of every increment `B^θ_t − B^θ_s` from `𝓕_s`.
* Path continuity: the elementary drifts converge uniformly on `[0, T]` almost surely
  (`drift_ae_eventually_sup_lt`), so the limit drift has continuous paths
  (`ae_continuous_driftContinuousMod`); with a continuous `B` and `Q ≪ μ`, `B^θ` has `Q`-a.s.
  continuous paths.

The measure `Q = Z_T·μ` is the horizon-`T` Girsanov measure: it depends on `T`, and the statement is
for that fixed `Q` with `B^θ` on all of `ℝ≥0` (after `T` the process continues as `B` plus the
frozen drift). Nothing here concerns unbounded `θ` or a Novikov condition.

## Main results

* `MathFin.ItoIntegralProcessContinuousModification.ae_continuous_driftContinuousMod`: almost
  surely the limit drift has continuous paths.
* `MathFin.aestronglyMeasurable_ZTpred`: `Z_T` is a.e. `𝓕_T`-measurable.
* `MathFin.isExpQMartingale_BthetaPredictable_all`: `IsExpQMartingale Q 𝓕 B^θ T'` for every `T'`.
* `MathFin.Btheta_isFilteredPreBrownian_predictable_of_bdd`: for bounded predictable `θ`,
  `B^θ` is an `𝓕`-pre-Brownian motion under `Q`.
* `MathFin.Btheta_isBrownianReal_predictable_of_bdd`: if `B` has a.s. continuous paths, `B^θ` is a
  Brownian motion (`IsBrownianReal`) under `Q`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 9.1.8
* [I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  Theorem 3.5.1

## Tags

Girsanov theorem, filtered Brownian motion, Lévy characterization, exponential martingale,
independent increments, continuous paths, MSC 60H05, MSC 60J65, MSC 60G44
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology NNReal
open scoped NNReal ENNReal
open ItoIntegralL2 ItoIntegralProcess ItoIntegralCLM ItoIsometryAdapted ItoIntegralBrownian
open ItoIntegralRiemannBridge SimpleDoleansMoments ItoIntegralProcessContinuousModification

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

/-! ### The drift is frozen after the horizon and has continuous paths -/

namespace ItoIntegralProcessContinuousModification

/-- A simple process supported in `[0, T]` has elementary drift constant on `[T, ∞)`. -/
lemma driftSimpleProcess_of_ge (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) {T t : ℝ≥0}
    (hV : ∀ p ∈ V.value.support, p.2 ≤ T) (hTt : T ≤ t) (ω : Ω) :
    driftSimpleProcess hBmeas V t ω = driftSimpleProcess hBmeas V T ω := by
  unfold driftSimpleProcess
  refine Finsupp.sum_congr fun p hp ↦ ?_
  have h2 := hV p hp
  have h1 := V.le_of_mem_support_value p hp
  simp only [min_eq_left h2, min_eq_left (h2.trans hTt), min_eq_left (h1.trans h2),
    min_eq_left (h1.trans (h2.trans hTt))]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The limit drift is frozen after `T`.** `driftContinuousMod T φ t = driftContinuousMod T φ T`
for `t ≥ T`: each approximant is `T`-bounded, so its drift is constant past `T`. -/
lemma driftContinuousMod_of_ge (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {t : ℝ≥0} (hTt : T ≤ t) (ω : Ω) :
    driftContinuousMod T hBmeas φ t ω = driftContinuousMod T hBmeas φ T ω := by
  unfold driftContinuousMod
  congr 1
  funext n
  exact driftSimpleProcess_of_ge hBmeas _ ((approxSeq T hBmeas φ).choose n).property hTt ω

/-- **Path continuity of the limit drift.** Almost surely `t ↦ driftContinuousMod T φ t ω` is
continuous. On `[0, T]` the elementary drifts `Dₙ` of the approximating sequence have
`sup |Dₙ − Dₙ₊₁| < (3/4)ⁿ` eventually (`drift_ae_eventually_sup_lt`), so `D_N + ∑ₖ (D_{N+k+1} −
D_{N+k})` is a Weierstrass series of continuous functions (`continuousOn_tsum`) and equals the
pointwise limit; past `T` the drift is frozen (`driftContinuousMod_of_ge`). -/
theorem ae_continuous_driftContinuousMod (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, Continuous fun t ↦ driftContinuousMod T hBmeas φ t ω := by
  set V := (approxSeq T hBmeas φ).choose with hVdef
  have hV := (approxSeq T hBmeas φ).choose_spec
  filter_upwards [drift_ae_eventually_sup_lt T hBmeas φ V hV,
    driftContinuousMod_tendsto T hBmeas φ] with ω hω htend
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  have hDcont (n : ℕ) : Continuous fun t ↦ driftSimpleProcess hBmeas (V n).val t ω :=
    driftSimpleProcess_continuous hBmeas (V n).val ω
  have hbound (k : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
      ‖driftSimpleProcess hBmeas (V (N + (k + 1))).val t ω
          - driftSimpleProcess hBmeas (V (N + k)).val t ω‖ ≤ (3 / 4 : ℝ) ^ (N + k) := by
    have hlin : driftSimpleProcess hBmeas (V (N + k)).val t ω
          - driftSimpleProcess hBmeas (V (N + (k + 1))).val t ω
        = driftSimpleProcess hBmeas (V (N + k) - V (N + (k + 1))).val t ω := by
      have hcoe : ((V (N + k) - V (N + (k + 1))).val : SimpleProcess ℝ (natFiltration hBmeas))
          = (V (N + k)).val - (V (N + (k + 1))).val := rfl
      rw [hcoe]
      exact (congrFun (driftSimpleProcess_sub hBmeas (V (N + k)).val (V (N + (k + 1))).val t)
        ω).symm
    rw [Real.norm_eq_abs, abs_sub_comm, hlin]
    exact (drift_norm_le_iSup_Iic hBmeas (V (N + k) - V (N + (k + 1))).val ω ht).trans
      (hN (N + k) (Nat.le_add_right N k)).le
  have hsum : Summable fun k : ℕ ↦ (3 / 4 : ℝ) ^ (N + k) := by
    simp_rw [pow_add]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hon : ContinuousOn (fun t ↦ driftContinuousMod T hBmeas φ t ω) (Set.Iic T) := by
    have hcts : ContinuousOn (fun t ↦ driftSimpleProcess hBmeas (V N).val t ω
        + ∑' k, (driftSimpleProcess hBmeas (V (N + (k + 1))).val t ω
          - driftSimpleProcess hBmeas (V (N + k)).val t ω)) (Set.Iic T) :=
      (hDcont N).continuousOn.add (continuousOn_tsum
        (fun k ↦ ((hDcont _).sub (hDcont _)).continuousOn) hsum
        (fun k t ht ↦ hbound k t ht))
    refine hcts.congr fun t ht ↦ ?_
    have hS : Summable fun k : ℕ ↦ (driftSimpleProcess hBmeas (V (N + (k + 1))).val t ω
        - driftSimpleProcess hBmeas (V (N + k)).val t ω) :=
      Summable.of_norm (Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _)
        (fun k ↦ hbound k t ht) hsum)
    have h1 : Tendsto (fun K ↦ driftSimpleProcess hBmeas (V (N + K)).val t ω) atTop
        (𝓝 (driftContinuousMod T hBmeas φ t ω)) :=
      (htend t ht).comp (tendsto_atTop_mono (fun K ↦ Nat.le_add_left K N) tendsto_id)
    have h2 : Tendsto (fun K ↦ driftSimpleProcess hBmeas (V N).val t ω
        + ∑ k ∈ Finset.range K, (driftSimpleProcess hBmeas (V (N + (k + 1))).val t ω
          - driftSimpleProcess hBmeas (V (N + k)).val t ω)) atTop
        (𝓝 (driftSimpleProcess hBmeas (V N).val t ω
          + ∑' k, (driftSimpleProcess hBmeas (V (N + (k + 1))).val t ω
            - driftSimpleProcess hBmeas (V (N + k)).val t ω))) :=
      hS.hasSum.tendsto_sum_nat.const_add _
    have h3 : (fun K ↦ driftSimpleProcess hBmeas (V (N + K)).val t ω)
        = fun K ↦ driftSimpleProcess hBmeas (V N).val t ω
          + ∑ k ∈ Finset.range K, (driftSimpleProcess hBmeas (V (N + (k + 1))).val t ω
            - driftSimpleProcess hBmeas (V (N + k)).val t ω) := by
      funext K
      have := Finset.sum_range_sub (fun k ↦ driftSimpleProcess hBmeas (V (N + k)).val t ω) K
      simp only [add_zero] at this
      linarith
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  have hmin : (fun t ↦ driftContinuousMod T hBmeas φ t ω)
      = fun t ↦ driftContinuousMod T hBmeas φ (min t T) ω := by
    funext t
    rcases le_total t T with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h]
      exact driftContinuousMod_of_ge T hBmeas φ h ω
  rw [hmin]
  exact hon.comp_continuous (continuous_id.min continuous_const) (fun t ↦ min_le_right t T)

end ItoIntegralProcessContinuousModification

/-! ### The density is `𝓕_T`-measurable and Brownian increments are mean-one exponentials -/

section Assembly

variable {μ : Measure Ω} [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ)

include hB in
/-- **`Z_T` is a.e. `𝓕_T`-measurable.** It is the a.e. limit along a subsequence
(`tendsto_ZTpred_ae_subseq`) of the simple Doléans densities of the marshalled approximants, each of
which is `𝓕_T`-measurable (`simpleDoleansExp_isMartingale`, adaptedness at `T`). -/
theorem aestronglyMeasurable_ZTpred (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ}
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    AEStronglyMeasurable[natFiltration hBmeas T] (ZTpred hB T hBmeas hpred hbdd) μ := by
  obtain ⟨V, hV⟩ := exists_approxSeq (μ := μ) hBmeas T hpred hbdd
  have hC : 0 ≤ C := nonneg_of_bdd μ hbdd
  have hFB : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  obtain ⟨ms, -, hms⟩ :=
    tendsto_ZTpred_ae_subseq hB T hBmeas hpred hbdd V hV (fun n ↦ n) tendsto_id
  let Zn : ℕ → Ω → ℝ := fun k ω ↦ simpleDoleansExp (X := B)
    (marshalPart hBmeas T (V (ms k)).val)
    (fun i ω ↦ -(clampM C (marshalMult hBmeas T (V (ms k)).val i ω)))
    ((marshalEndpoints hBmeas T (V (ms k)).val).card - 1) T ω
  have hZn (k : ℕ) : StronglyMeasurable[natFiltration hBmeas T] (Zn k) :=
    (simpleDoleansExp_isMartingale (X := B) (P := μ) (𝓕 := natFiltration hBmeas)
      (marshalPart hBmeas T (V (ms k)).val)
      (marshalPart_mono hBmeas T (V (ms k)).val (V (ms k)).property)
      (fun i ω ↦ -(clampM C (marshalMult hBmeas T (V (ms k)).val i ω)))
      (fun i ↦ (stronglyMeasurable_clampM_marshalMult hBmeas T (V (ms k)) i).neg)
      (K := C) (fun i ω ↦ by
        rw [abs_neg]; exact clampM_marshalMult_abs_le hC hBmeas T (V (ms k)) i ω)
      ((marshalEndpoints hBmeas T (V (ms k)).val).card - 1)).1 T
  have hmeas : StronglyMeasurable[natFiltration hBmeas T]
      (fun ω ↦ limUnder atTop (fun k ↦ Zn k ω)) := by
    let _ : MeasurableSpace Ω := natFiltration hBmeas T
    exact StronglyMeasurable.limUnder hZn
  refine ⟨_, hmeas, ?_⟩
  filter_upwards [hms] with ω hω
  exact hω.limUnder_eq.symm

omit [IsProbabilityMeasure μ] in
/-- **A Brownian increment's normalised exponential has mean one.**
`𝔼 exp(a(B_t − B_s) − a²(t−s)/2) = 1`, from the Gaussian law of the increment. -/
lemma integral_exp_increment (hBr : IsPreBrownianReal B μ) {s t : ℝ≥0} (hst : s ≤ t) (a : ℝ) :
    ∫ ω, Real.exp (a * (B t ω - B s ω) - a ^ 2 * ((t : ℝ) - s) / 2) ∂μ = 1 := by
  have hL := hasLaw_increment hBr hst
  have hg : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (a * x))
      (Measure.map (fun ω ↦ B t ω - B s ω) μ) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have h1 : ∫ ω, Real.exp (a * (B t ω - B s ω)) ∂μ = Real.exp (a ^ 2 * ((t : ℝ) - s) / 2) := by
    rw [(integral_map hL.aemeasurable hg).symm, hL.map_eq, integral_exp_mul_gaussianReal_zero,
      NNReal.coe_sub hst]
  have h2 : (fun ω ↦ Real.exp (a * (B t ω - B s ω) - a ^ 2 * ((t : ℝ) - s) / 2))
      = fun ω ↦ Real.exp (-(a ^ 2 * ((t : ℝ) - s) / 2)) * Real.exp (a * (B t ω - B s ω)) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h2, integral_const_mul, h1, ← Real.exp_add]
  simp

include hB in
/-- **The exponential martingale step past the horizon.** For `T ≤ s ≤ t` and `A ∈ 𝓕_s`,
`∫_A exp(a B^θ_t − a²t/2) dQ = ∫_A exp(a B^θ_s − a²s/2) dQ` for `Q = Z_T·μ`. Past `T` the drift is
frozen, so `exp(a B^θ_t − a²t/2) = exp(a B^θ_s − a²s/2) · exp(a(B_t − B_s) − a²(t−s)/2)`; the first
factor times `Z_T` is `𝓕_s`-measurable (a.e., `aestronglyMeasurable_ZTpred`), the second is
independent of `𝓕_s` with mean one (`integral_exp_increment`). -/
theorem setIntegral_expBthetaPred_tail (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ}
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (a : ℝ) {s t : ℝ≥0} (hTs : T ≤ s) (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet[natFiltration hBmeas s] A) :
    ∫ ω in A, Real.exp (a * BthetaPred (μ := μ) T hBmeas hpred hbdd t ω - a ^ 2 * (t : ℝ) / 2)
        ∂(μ.withDensity fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω))
      = ∫ ω in A, Real.exp (a * BthetaPred (μ := μ) T hBmeas hpred hbdd s ω
          - a ^ 2 * (s : ℝ) / 2)
        ∂(μ.withDensity fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω)) := by
  obtain ⟨V, hV⟩ := exists_approxSeq (μ := μ) hBmeas T hpred hbdd
  have hFB : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  have hT := isExpQMartingale_BthetaPredictable hB hBmeas hpred hbdd T V hV
  have hAm : MeasurableSet A := (natFiltration hBmeas).le s A hA
  have hZ := aestronglyMeasurable_ZTpred hB hBmeas hpred hbdd T
  have hZamb : AEStronglyMeasurable (ZTpred hB T hBmeas hpred hbdd) μ :=
    (hZ.stronglyMeasurable_mk.mono ((natFiltration hBmeas).le T)).aestronglyMeasurable.congr
      hZ.ae_eq_mk.symm
  have hZpos : ∀ ω, 0 ≤ ZTpred hB T hBmeas hpred hbdd ω := fun ω ↦ (contDoleansExp_pos _ _ _ _).le
  rw [setIntegral_withDensity_ofReal hZamb hZpos _ hAm,
    setIntegral_withDensity_ofReal hZamb hZpos _ hAm]
  obtain ⟨Ns, hNsdef⟩ : ∃ Ns : Ω → ℝ, ∀ ω, Ns ω = Real.exp (a * BthetaPred (μ := μ) T hBmeas hpred
      hbdd s ω - a ^ 2 * (s : ℝ) / 2) := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Ω → ℝ, ∀ ω,
      G ω = Real.exp (a * (B t ω - B s ω) - a ^ 2 * ((t : ℝ) - s) / 2) := ⟨_, fun _ ↦ rfl⟩
  have hM : ∀ ω, driftContinuousMod T hBmeas
        (processToLpPredictable (μ := μ) T hBmeas hpred hbdd) t ω
      = driftContinuousMod T hBmeas (processToLpPredictable (μ := μ) T hBmeas hpred hbdd) s ω :=
    fun ω ↦ (driftContinuousMod_of_ge T hBmeas _ (hTs.trans hst) ω).trans
      (driftContinuousMod_of_ge T hBmeas _ hTs ω).symm
  have hsplit (ω : Ω) : Real.exp (a * BthetaPred (μ := μ) T hBmeas hpred hbdd t ω
      - a ^ 2 * (t : ℝ) / 2) = Ns ω * G ω := by
    rw [hNsdef, hGdef, ← Real.exp_add]
    congr 1
    simp only [BthetaPred]
    rw [hM ω]
    ring
  set Z' := hZ.mk (ZTpred hB T hBmeas hpred hbdd) with hZ'
  have hZ'sm : StronglyMeasurable[natFiltration hBmeas s] Z' :=
    hZ.stronglyMeasurable_mk.mono ((natFiltration hBmeas).mono hTs)
  have hNssm : StronglyMeasurable[natFiltration hBmeas s] Ns := by
    have : Ns = fun ω ↦ Real.exp (a * BthetaPred (μ := μ) T hBmeas hpred hbdd s ω
        - a ^ 2 * (s : ℝ) / 2) := funext hNsdef
    rw [this]
    exact Real.continuous_exp.comp_stronglyMeasurable
      (((hT.adapted s).const_mul a).sub stronglyMeasurable_const)
  have hfsm : StronglyMeasurable[natFiltration hBmeas s]
      (A.indicator fun ω ↦ Ns ω * Z' ω) := (hNssm.mul hZ'sm).indicator hA
  have hGfun : G = fun ω ↦ Real.exp (a * (B t ω - B s ω) - a ^ 2 * ((t : ℝ) - s) / 2) :=
    funext hGdef
  have hGm : Measurable[MeasurableSpace.comap (B t - B s) inferInstance] G := by
    have hΔ : Measurable[MeasurableSpace.comap (B t - B s) inferInstance] (B t - B s) :=
      comap_measurable _
    rw [hGfun]
    exact (((hΔ.const_mul a).sub_const _).exp)
  have hGamb : AEStronglyMeasurable G μ := by
    rw [hGfun]
    exact ((((hBmeas t).sub (hBmeas s)).const_mul a).sub_const _).exp.aestronglyMeasurable
  have hindep : IndepFun (A.indicator fun ω ↦ Ns ω * Z' ω) G μ := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left (indep_of_indep_of_le_right (hFB.indep s t hst).symm
      hGm.comap_le) hfsm.measurable.comap_le
  have hG1 : ∫ ω, G ω ∂μ = 1 := by
    rw [hGfun]; exact integral_exp_increment hB hst a
  have key : ∫ ω in A, (Ns ω * G ω) * ZTpred hB T hBmeas hpred hbdd ω ∂μ
      = ∫ ω in A, Ns ω * ZTpred hB T hBmeas hpred hbdd ω ∂μ := by
    calc ∫ ω in A, (Ns ω * G ω) * ZTpred hB T hBmeas hpred hbdd ω ∂μ
        = ∫ ω, (A.indicator fun ω ↦ Ns ω * Z' ω) ω * G ω ∂μ := by
          rw [← integral_indicator hAm]
          refine integral_congr_ae ?_
          filter_upwards [hZ.ae_eq_mk] with ω hω
          by_cases hωA : ω ∈ A
          · rw [Set.indicator_of_mem hωA, Set.indicator_of_mem hωA, hω]
            ring
          · rw [Set.indicator_of_notMem hωA, Set.indicator_of_notMem hωA]
            simp
      _ = (∫ ω, (A.indicator fun ω ↦ Ns ω * Z' ω) ω ∂μ) * ∫ ω, G ω ∂μ :=
          hindep.integral_fun_mul_eq_mul_integral
            (hfsm.mono ((natFiltration hBmeas).le s)).aestronglyMeasurable hGamb
      _ = ∫ ω in A, Ns ω * Z' ω ∂μ := by rw [hG1, mul_one, integral_indicator hAm]
      _ = ∫ ω in A, Ns ω * ZTpred hB T hBmeas hpred hbdd ω ∂μ := by
          refine setIntegral_congr_ae hAm ?_
          filter_upwards [hZ.ae_eq_mk] with ω hω _
          rw [hω]
  calc ∫ ω in A, Real.exp (a * BthetaPred (μ := μ) T hBmeas hpred hbdd t ω
          - a ^ 2 * (t : ℝ) / 2) * ZTpred hB T hBmeas hpred hbdd ω ∂μ
      = ∫ ω in A, (Ns ω * G ω) * ZTpred hB T hBmeas hpred hbdd ω ∂μ := by
        simp only [hsplit]
    _ = ∫ ω in A, Ns ω * ZTpred hB T hBmeas hpred hbdd ω ∂μ := key
    _ = _ := by simp only [hNsdef]

include hB in
/-- **The exponential-martingale data for `B^θ` under `Q = Z_T·μ` at every horizon.**
`IsExpQMartingale Q 𝓕 B^θ T'` for all `T'`, not just `T' ≤ T`: on `[0, T]` it is
`isExpQMartingale_BthetaPredictable`, past `T` it is `setIntegral_expBthetaPred_tail`, and a pair
`s < T < t` goes through `T`. -/
theorem isExpQMartingale_BthetaPredictable_all (hBmeas : ∀ t, Measurable (B t))
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ}
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (T T' : ℝ≥0) :
    IsExpQMartingale (μ.withDensity fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω))
      (natFiltration hBmeas) (BthetaPred (μ := μ) T hBmeas hpred hbdd) T' := by
  obtain ⟨V, hV⟩ := exists_approxSeq (μ := μ) hBmeas T hpred hbdd
  have hT := isExpQMartingale_BthetaPredictable hB hBmeas hpred hbdd T V hV
  refine ⟨hT.adapted, hT.zero_start, ?_⟩
  intro a s t hst _ A hA
  by_cases hsT : T ≤ s
  · exact setIntegral_expBthetaPred_tail hB hBmeas hpred hbdd T a hsT hst hA
  · rw [not_le] at hsT
    by_cases htT : t ≤ T
    · exact hT.martingale a hst htT hA
    · rw [not_le] at htT
      have hAT : MeasurableSet[natFiltration hBmeas T] A :=
        (natFiltration hBmeas).mono hsT.le A hA
      exact (setIntegral_expBthetaPred_tail hB hBmeas hpred hbdd T a le_rfl htT.le hAT).trans
        (hT.martingale a hsT.le le_rfl hA)

include hB in
/-- **Girsanov's theorem for the filtration (bounded predictable `θ`).** For a bounded predictable
market price of risk `θ`, under `Q = μ.withDensity(Z_T)` with
`Z_T = exp(−∫₀ᵀθdB − ½∫₀ᵀθ²ds)`, the drift-corrected process `B^θ_u = B_u + driftContinuousMod θ̂ u`
is an `𝓕`-pre-Brownian motion for the natural filtration `𝓕` of `B`: adapted, starting at `0`,
with `N(0, t−s)` increments, and with every increment `B^θ_t − B^θ_s` independent of `𝓕_s`, on all
of `ℝ≥0` (past `T` it continues as `B` plus the frozen drift). Path continuity is
`Btheta_isBrownianReal_predictable_of_bdd`. -/
theorem Btheta_isFilteredPreBrownian_predictable_of_bdd (hBmeas : ∀ t, Measurable (B t))
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ}
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    IsFilteredPreBrownian (BthetaPred (μ := μ) T hBmeas hpred hbdd) (natFiltration hBmeas)
      (μ.withDensity fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω)) := by
  obtain ⟨V, hV⟩ := exists_approxSeq (μ := μ) hBmeas T hpred hbdd
  have : IsProbabilityMeasure (μ.withDensity fun ω ↦
      ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω)) :=
    isProbabilityMeasure_predGirsanov hB hBmeas T hpred hbdd V hV
  exact isFilteredPreBrownian_of_expMartingale
    (isExpQMartingale_BthetaPredictable_all hB hBmeas hpred hbdd T)

include hB in
/-- **Girsanov's theorem with continuous paths (bounded predictable `θ`).** If `B` has almost surely
continuous paths (so is a Brownian motion), then under `Q = μ.withDensity(Z_T)` the drift-corrected
process `B^θ` is a Brownian motion (`IsBrownianReal`): pre-Brownian, with `Q`-almost surely
continuous paths. `Q ≪ μ`, `B` is continuous, and the limit drift has continuous paths
(`ae_continuous_driftContinuousMod`). -/
theorem Btheta_isBrownianReal_predictable_of_bdd (hBmeas : ∀ t, Measurable (B t))
    (hcont : ∀ᵐ ω ∂μ, Continuous fun t ↦ B t ω) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ}
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    IsBrownianReal (BthetaPred (μ := μ) T hBmeas hpred hbdd)
      (μ.withDensity fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω)) := by
  obtain ⟨V, hV⟩ := exists_approxSeq (μ := μ) hBmeas T hpred hbdd
  have : IsProbabilityMeasure (μ.withDensity fun ω ↦
      ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω)) :=
    isProbabilityMeasure_predGirsanov hB hBmeas T hpred hbdd V hV
  have hae : ∀ᵐ ω ∂μ, Continuous fun t ↦ BthetaPred (μ := μ) T hBmeas hpred hbdd t ω := by
    filter_upwards [hcont, ae_continuous_driftContinuousMod T hBmeas
      (processToLpPredictable (μ := μ) T hBmeas hpred hbdd)] with ω h1 h2
    exact h1.add h2
  exact isBrownianReal_of_expMartingale
    (isExpQMartingale_BthetaPredictable_all hB hBmeas hpred hbdd T)
    ((withDensity_absolutelyContinuous _ _).ae_le hae)

end Assembly

end MathFin
