/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.CommonYamada
public import MathFin.Models.StochVol.Heston.CommonHestonState
public import MathFin.Probability.Brownian.Ito.Filtered.CorrelatedIntegral

/-!
# The Heston state as a three-dimensional Itô process

The clock `t`, the log-price `X` and the variance `V` form an `ItoProc` on `Fin 3` driven by
the independent pair `(B, Z)`: the integral against the correlated price noise
`W = ρ B + √(1 - ρ²) Z` is rotated into its `B`- and `Z`-components, simultaneously for all
times.

## Main definitions

* `hestonDiffZ`
* `hestonKerB`
* `hestonKerZ`

## Main results

* `itoContinuousMod_smul_ae`
* `itoContinuousMod_correlated`
* `hestonItoProc`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston
open MathFin.FilteredIto
namespace CommonHestonIto

open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonPredictable
      MathFin.FilteredIto.CommonIntegral
  MathFin.FilteredIto.CommonProcessGeneral MathFin.FilteredIto.CommonContinuous
        MathFin.FilteredIto.CommonStopping
  MathFin.FilteredIto.CommonCovariation MathFin.FilteredIto.CommonHorizon
        MathFin.FilteredIto.CommonIto MathFin.Heston.CommonYamada
open scoped NNReal ENNReal

local notation "leb" => MathFin.ItoIntegralL2.timeMeasure

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℝ≥0 mΩ} {B Z W : ℝ≥0 → Ω → ℝ}

/-! ### Elementary processes -/

omit [IsProbabilityMeasure μ] in
lemma measurable_time_predictable :
    Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ (p.1 : ℝ)) := by
  have hfst : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ p.1) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    refine measurable_of_Ioi fun x => ?_
    have h : (fun p : ℝ≥0 × Ω ↦ p.1) ⁻¹' Set.Ioi x = Set.Ioi x ×ˢ Set.univ := by
      ext p; simp
    rw [h]
    exact measurableSet_predictable_Ioi_prod (@MeasurableSet.univ Ω (ℱ x))
  exact measurable_coe_nnreal_real.comp hfst

omit [IsProbabilityMeasure μ] in
lemma contProcess_time (T : ℝ≥0) : ContProcess ℱ μ T (fun t _ ↦ (t : ℝ)) :=
  ⟨fun _ => measurable_const, measurable_time_predictable,
    Eventually.of_forall fun _ => NNReal.continuous_coe.continuousOn⟩

omit [IsProbabilityMeasure μ] in
lemma contProcess_zero (T : ℝ≥0) : ContProcess ℱ μ T (fun _ _ ↦ (0 : ℝ)) :=
  ⟨fun _ => measurable_const, measurable_const, Eventually.of_forall fun _ => continuousOn_const⟩

omit [IsProbabilityMeasure μ] in
lemma contProcess_const_mul_sqrt {T : ℝ≥0} (c : ℝ) {V : ℝ≥0 → Ω → ℝ}
    (hV : ContProcess ℱ μ T V) : ContProcess ℱ μ T (fun s ω ↦ c * Real.sqrt (V s ω)) where
  adapted s := (Real.continuous_sqrt.measurable.comp (hV.adapted s)).const_mul c
  pred := (Real.continuous_sqrt.measurable.comp hV.pred).const_mul c
  cont := by
    filter_upwards [hV.cont] with ω hω
    exact continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hω)

/-! ### Linearity and rotation of continuous Itô integrals -/

theorem itoContinuousMod_smul_ae (hW : BrownianOn ℱ W μ)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) {T : ℝ≥0} (c : ℝ)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, itoContinuousMod T hW.measurable (c • φ) t ω
      = c * itoContinuousMod T hW.measurable φ t ω := by
  refine ae_forall_eq_of_continuousOn' (itoContinuousMod_continuousOn hW T hW.measurable hWc _)
    ?_ fun t ht => ?_
  · filter_upwards [itoContinuousMod_continuousOn hW T hW.measurable hWc φ] with ω h
    exact continuousOn_const.mul h
  · filter_upwards [itoContinuousMod_modification hW T hW.measurable hWc (c • φ) ht,
      itoContinuousMod_modification hW T hW.measurable hWc φ ht,
      Lp.coeFn_smul c (itoProcessCLM hW T t hW.measurable φ)] with ω e1 e2 e3
    rw [e1, map_smul, e3, Pi.smul_apply, smul_eq_mul, ← e2]

/-- **Rotation of the continuous integrals.** Almost surely, for every `t ≤ T`, the continuous
integral against the correlated noise is `ρ` times the `B`-integral plus `√(1 - ρ²)` times the
`Z`-integral. -/
theorem itoContinuousMod_correlated (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {ρ : ℝ} (hρ : |ρ| ≤ 1) {T : ℝ≥0} (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, itoContinuousMod T (hP.correlated_brownian hρ).measurable φ t ω
      = ρ * itoContinuousMod T hP.left.measurable φ t ω
        + orthogonalWeight ρ * itoContinuousMod T hP.right.measurable φ t ω := by
  have hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ correlatedNoise ρ B Z u ω := fun ω =>
    ((hBc ω).const_mul ρ).add ((hZc ω).const_mul (orthogonalWeight ρ))
  refine ae_forall_eq_of_continuousOn'
    (itoContinuousMod_continuousOn (hP.correlated_brownian hρ) T
      (hP.correlated_brownian hρ).measurable hWc φ) ?_ fun t ht => ?_
  · filter_upwards [itoContinuousMod_continuousOn hP.left T hP.left.measurable hBc φ,
      itoContinuousMod_continuousOn hP.right T hP.right.measurable hZc φ] with ω h1 h2
    exact (continuousOn_const.mul h1).add (continuousOn_const.mul h2)
  · have hrot := hP.itoIntegral_correlated hρ t (restrictKernel ht φ)
    rw [itoIntegralCLM_T_restrictKernel (hP.correlated_brownian hρ) ht
        (hP.correlated_brownian hρ).measurable,
      itoIntegralCLM_T_restrictKernel hP.left ht hP.left.measurable,
      itoIntegralCLM_T_restrictKernel hP.right ht hP.right.measurable] at hrot
    filter_upwards [itoContinuousMod_modification (hP.correlated_brownian hρ) T
        (hP.correlated_brownian hρ).measurable hWc φ ht,
      itoContinuousMod_modification hP.left T hP.left.measurable hBc φ ht,
      itoContinuousMod_modification hP.right T hP.right.measurable hZc φ ht,
      Lp.coeFn_add (ρ • itoProcessCLM hP.left T t hP.left.measurable φ)
        (orthogonalWeight ρ • itoProcessCLM hP.right T t hP.right.measurable φ),
      Lp.coeFn_smul ρ (itoProcessCLM hP.left T t hP.left.measurable φ),
      Lp.coeFn_smul (orthogonalWeight ρ) (itoProcessCLM hP.right T t hP.right.measurable φ)]
      with ω e1 e2 e3 e4 e5 e6
    rw [e1, hrot, e4, Pi.add_apply, e5, e6, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, ← e2, ← e3]

/-! ### The Heston state as an `ItoProc` on `Fin 3` -/

/-- The clock–log-price–variance state `(t, X_t, V_t)`. -/
def hestonY (X V : ℝ≥0 → Ω → ℝ) : Fin 3 → ℝ≥0 → Ω → ℝ := ![fun t _ ↦ (t : ℝ), X, V]

/-- Initial state `(0, x₀, v₀)`. -/
def hestonY0 (x₀ v₀ : ℝ) : Fin 3 → ℝ := ![0, x₀, v₀]

/-- Drift coefficients `(1, r - q - V/2, κ(θ - V))`. -/
def hestonDrift (p : Parameters) (V : ℝ≥0 → Ω → ℝ) : Fin 3 → ℝ≥0 → Ω → ℝ :=
  ![fun _ _ ↦ 1, fun s ω ↦ (p.r - p.q) - (1 / 2 : ℝ) * V s ω,
    fun s ω ↦ p.kappa * (p.theta - V s ω)]

/-- `B`-diffusion coefficients `(0, ρ √V, ξ √V)`. -/
def hestonDiffB (p : Parameters) (V : ℝ≥0 → Ω → ℝ) : Fin 3 → ℝ≥0 → Ω → ℝ :=
  ![fun _ _ ↦ 0, fun s ω ↦ p.rho * Real.sqrt (V s ω), fun s ω ↦ p.xi * Real.sqrt (V s ω)]

/-- `Z`-diffusion coefficients `(0, √(1 - ρ²) √V, 0)`. -/
def hestonDiffZ (p : Parameters) (V : ℝ≥0 → Ω → ℝ) : Fin 3 → ℝ≥0 → Ω → ℝ :=
  ![fun _ _ ↦ 0, fun s ω ↦ orthogonalWeight p.rho * Real.sqrt (V s ω), fun _ _ ↦ 0]

/-- `L²` kernels of the `B`-integrals. -/
def hestonKerB (p : Parameters) {T : ℝ≥0} (Hv Hx : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    Fin 3 → Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) := ![0, p.rho • Hx, Hv]

/-- `L²` kernels of the `Z`-integrals. -/
def hestonKerZ (p : Parameters) {T : ℝ≥0} (Hx : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    Fin 3 → Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) := ![0, orthogonalWeight p.rho • Hx, 0]

/-- **The Heston state is a three-dimensional Itô process** driven by `(B, Z)`. -/
theorem hestonItoProc (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} (p : Parameters) (hρ : |p.rho| ≤ 1) {x₀ v₀ : ℝ}
    {X V : ℝ≥0 → Ω → ℝ} {Hv Hx : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)}
    (hpX : IsStronglyPredictable ℱ X) (hpV : IsStronglyPredictable ℱ V)
    (hcX : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Set.Icc 0 T))
    (hcV : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ V t ω) (Set.Icc 0 T))
    (hHv : ⇑Hv =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun z ↦ p.xi * Real.sqrt (V z.1 z.2))
    (hHx : ⇑Hx =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun z ↦ Real.sqrt (V z.1 z.2))
    (heqV : ∀ᵐ ω ∂μ, ∀ t ≤ T, V t ω = v₀
      + (∫ s in Set.Ioc 0 t, p.kappa * (p.theta - V s ω) ∂leb)
      + itoContinuousMod T hP.left.measurable Hv t ω)
    (heqX : ∀ᵐ ω ∂μ, ∀ t ≤ T, X t ω = x₀
      + (∫ s in Set.Ioc 0 t, (p.r - p.q) - (1 / 2 : ℝ) * V s ω ∂leb)
      + itoContinuousMod T (hP.correlated_brownian hρ).measurable Hx t ω) :
    ItoProc hP T (hestonY X V) (hestonY0 x₀ v₀) (hestonDrift p V) (hestonDiffB p V)
      (hestonDiffZ p V) (hestonKerB p Hv Hx) (hestonKerZ p Hx) where
  proc i := by
    fin_cases i
    · exact contProcess_time T
    · exact contProcess_of_predictable hpX hcX
    · exact contProcess_of_predictable hpV hcV
  drift := by
    filter_upwards [hcV] with ω hω i
    fin_cases i
    · exact continuousOn_const
    · exact continuousOn_const.sub (continuousOn_const.mul hω)
    · exact continuousOn_const.mul (continuousOn_const.sub hω)
  diffB i := by
    have hV := contProcess_of_predictable hpV hcV
    fin_cases i
    · exact contProcess_zero T
    · exact contProcess_const_mul_sqrt p.rho hV
    · exact contProcess_const_mul_sqrt p.xi hV
  diffZ i := by
    have hV := contProcess_of_predictable hpV hcV
    fin_cases i
    · exact contProcess_zero T
    · exact contProcess_const_mul_sqrt (orthogonalWeight p.rho) hV
    · exact contProcess_zero T
  kerB i := by
    fin_cases i
    · exact Lp.coeFn_zero (E := ℝ) (p := 2) (μ := trimMeasure_T (μ := μ) T ℱ)
    · show ⇑(p.rho • Hx) =ᵐ[trimMeasure_T (μ := μ) T ℱ]
        fun z ↦ p.rho * Real.sqrt (V z.1 z.2)
      filter_upwards [Lp.coeFn_smul p.rho Hx, hHx] with z h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    · exact hHv
  kerZ i := by
    fin_cases i
    · exact Lp.coeFn_zero (E := ℝ) (p := 2) (μ := trimMeasure_T (μ := μ) T ℱ)
    · show ⇑(orthogonalWeight p.rho • Hx) =ᵐ[trimMeasure_T (μ := μ) T ℱ]
        fun z ↦ orthogonalWeight p.rho * Real.sqrt (V z.1 z.2)
      filter_upwards [Lp.coeFn_smul (orthogonalWeight p.rho) Hx, hHx] with z h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    · exact Lp.coeFn_zero (E := ℝ) (p := 2) (μ := trimMeasure_T (μ := μ) T ℱ)
  eq := by
    filter_upwards [heqX, heqV, itoContinuousMod_zero_kernel hP.left hBc T,
      itoContinuousMod_zero_kernel hP.right hZc T,
      itoContinuousMod_correlated hP hBc hZc hρ Hx,
      itoContinuousMod_smul_ae hP.left hBc p.rho Hx,
      itoContinuousMod_smul_ae hP.right hZc (orthogonalWeight p.rho) Hx]
      with ω hX hV h0B h0Z hW hsB hsZ i t ht
    fin_cases i
    · show (t : ℝ) = 0 + ∫ s in Set.Ioc 0 t, (1 : ℝ) ∂leb
        + itoContinuousMod T hP.left.measurable 0 t ω
        + itoContinuousMod T hP.right.measurable 0 t ω
      rw [h0B t ht, h0Z t ht, setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
        MathFin.ItoIntegralL2.timeMeasure_Ioc, NNReal.coe_zero, sub_zero,
        ENNReal.toReal_ofReal (NNReal.coe_nonneg t)]
      ring
    · show X t ω = x₀ + ∫ s in Set.Ioc 0 t, ((p.r - p.q) - (1 / 2 : ℝ) * V s ω) ∂leb
        + itoContinuousMod T hP.left.measurable (p.rho • Hx) t ω
        + itoContinuousMod T hP.right.measurable (orthogonalWeight p.rho • Hx) t ω
      rw [hX t ht, hW t ht, hsB t ht, hsZ t ht]
      ring
    · show V t ω = v₀ + ∫ s in Set.Ioc 0 t, p.kappa * (p.theta - V s ω) ∂leb
        + itoContinuousMod T hP.left.measurable Hv t ω
        + itoContinuousMod T hP.right.measurable 0 t ω
      rw [hV t ht, h0Z t ht]
      ring

end CommonHestonIto
end MathFin.Heston
