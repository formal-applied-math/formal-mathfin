/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.GirsanovPredictableTheta

/-! # Continuous bounded-adapted-θ Girsanov — the bounded predictable case, read at a continuous `θ`

A bounded (`|θ| ≤ C`) adapted (`𝓕_t`-measurable in each `t`) path-continuous market price of risk is
strongly predictable (`isStronglyPredictable_of_bdd_adapted_cont`: left-continuous and adapted), so
the bounded predictable Girsanov theorem `Btheta_isQBrownianMotion_predictable_of_bdd` applies. This
file identifies its objects with the pathwise ones of the continuous case, and transports the
conclusion across the identification:

* `itoIntCont` is `itoIntPred` at the predictable realization of `θ`
  (`itoIntPred_eq_itoIntCont`, by `rfl`: both are the Itô integral of the class of `θ` in
  `Lp ℝ 2 (trimMeasure_T T)`);
* the predictable density `ZTpred` agrees `μ`-a.e. with `contDoleansExp` of the continuous `θ`
  (`ZTpred_ae_eq_contDoleansExp`), because the representative `θ̂` of the class of `θ` equals `θ` on
  almost every `ω`-slice (`processToLpPredictable_ae_slice`);
* the predictable process `BthetaPred` is a modification of `BthetaCont` on `[0,T]`
  (`BthetaPred_ae_eq_BthetaCont`, by `driftContinuousMod_eq_setIntegral`);
* being Brownian on `[0,T]` (`IsBrownianOn`) under `Q` is invariant under an a.e.-equal change of
  density (`Measure.withDensity_congr_ae`) and a modification of the process
  (`IsBrownianOn.congr_modification`).

For a bounded adapted continuous `θ`, under `Q = μ.withDensity Z_T` with the Doléans density
`Z_T = exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds)`, the drift-corrected process `B^θ_u = B_u + ∫₀ᵘθ ds`
starts at `0`, has `N(0,t−s)` increments, and has independent increments (`HasIndepIncrements`)
on `[0,T]`, which together fix every finite-dimensional law of `B^θ` under `Q` on `[0,T]` to that of a standard
Brownian motion; path continuity is not stated.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter NNReal
open scoped NNReal ENNReal
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessContinuousModification

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- The pathwise linear drift `∫₀ᵘ θ_s ds` (against `timeMeasure`). -/
noncomputable def contDrift (θ : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Set.Ioc (0 : ℝ≥0) u, θ s ω ∂timeMeasure

/-- The drift-corrected process `B^θ_u = B_u + ∫₀ᵘ θ ds`. -/
noncomputable def BthetaCont (B θ : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  B u ω + contDrift θ u ω

variable (hB : IsPreBrownianReal B μ)

/-- The Itô integral `∫₀ᵀ θ dB` as a genuine function — the chosen `Lp`-representative of
`itoIntegralCLM_T (processToLp θ)`. -/
noncomputable def itoIntCont (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 ↦ θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    Ω → ℝ :=
  ⇑(itoIntegralCLM_T hB T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd))

section Bridge

variable (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
  (hcont : ∀ ω, Continuous (fun s : ℝ≥0 ↦ θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0)

/-- **The continuous Itô integral is the predictable one.** A continuous adapted `θ` is
predictable, and its two realizations in `Lp ℝ 2 (trimMeasure_T T)` are the same class. -/
theorem itoIntPred_eq_itoIntCont :
    itoIntPred hB T hBmeas (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont) hbdd
      = itoIntCont hB hBmeas hadap hcont hbdd T := rfl

/-- **The predictable Doléans density is the continuous one, a.e.** The two `exp`-forms differ only
in the quadratic-variation integrand, `θ̂` against `θ`, and these agree on almost every
`ω`-slice. -/
theorem ZTpred_ae_eq_contDoleansExp :
    ZTpred hB T hBmeas (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont) hbdd
      =ᵐ[μ] contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T := by
  filter_upwards [processToLpPredictable_ae_slice (μ := μ) T hBmeas
    (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont) hbdd] with ω hω
  have hint : ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(processToLpPredictable (μ := μ) T hBmeas
        (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont) hbdd) (s, ω)) ^ 2
          ∂timeMeasure
      = ∫ s in Set.Ioc (0 : ℝ≥0) T, (θ s ω) ^ 2 ∂timeMeasure :=
    integral_congr_ae (hω.mono fun s hs ↦ by simp only [hs])
  change contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) (fun s ω ↦
    ⇑(processToLpPredictable (μ := μ) T hBmeas
      (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont) hbdd) (s, ω)) T ω
    = contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω
  simp only [contDoleansExp]
  rw [hint]

/-- **The predictable drift-corrected process is a modification of the continuous one** on `[0,T]`:
`driftContinuousMod θ̂ u = ∫₀ᵘ θ ds` a.e. (`driftContinuousMod_eq_setIntegral`, with `θ̂ = θ` on
almost every `ω`-slice). -/
theorem BthetaPred_ae_eq_BthetaCont {u : ℝ≥0} (hu : u ≤ T) :
    BthetaPred (μ := μ) T hBmeas (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont) hbdd
        u =ᵐ[μ] BthetaCont B θ u := by
  filter_upwards [driftContinuousMod_eq_setIntegral (μ := μ) T hBmeas
      (processToLpPredictable (μ := μ) T hBmeas
        (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont) hbdd) hu,
    processToLpPredictable_ae_slice (μ := μ) T hBmeas
      (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont) hbdd] with ω h1 h2
  change B u ω + driftContinuousMod T hBmeas (processToLpPredictable (μ := μ) T hBmeas
      (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont) hbdd) u ω
    = B u ω + contDrift θ u ω
  rw [h1, contDrift]
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset
    (Set.Ioc_subset_Ioc_right hu) (h2.mono fun s hs ↦ by simp only [hs]))

include hB in
/-- **Continuous bounded-adapted-θ distributional Girsanov: the increments of `B^θ` under `Q`.** For
a bounded, adapted, path-continuous market price of risk `θ`, under `Q = μ.withDensity(Z_T)` with
the Doléans density `Z_T = exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds)`, the drift-corrected process
`B^θ_u = B_u + ∫₀ᵘθ ds` has, on `[0,T]`: zero start, Gaussian increments `𝒩(0,t−s)`, and
independent increments (`HasIndepIncrements`), which fix its finite-dimensional laws on `[0,T]`;
path continuity is not stated. The bounded predictable theorem
`Btheta_isQBrownianMotion_predictable_of_bdd` at the (predictable) continuous `θ`, transported along
`ZTpred_ae_eq_contDoleansExp` and `BthetaPred_ae_eq_BthetaCont`. -/
theorem Btheta_isQBrownianMotion_adapted :
    IsBrownianOn (μ.withDensity fun ω ↦
      ENNReal.ofReal (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω)) T
      (BthetaCont B θ) := by
  have hpred := isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont
  have hZ : (fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω))
      =ᵐ[μ] fun ω ↦ ENNReal.ofReal
        (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω) :=
    (ZTpred_ae_eq_contDoleansExp hB hBmeas hadap hcont hbdd T).mono fun _ h ↦
      congrArg ENNReal.ofReal h
  have h := Btheta_isQBrownianMotion_predictable_of_bdd hB hBmeas hpred hbdd T
  rw [withDensity_congr_ae hZ] at h
  exact IsBrownianOn.congr_modification
    (fun u hu ↦ (withDensity_absolutelyContinuous μ _).ae_eq
      (BthetaPred_ae_eq_BthetaCont hBmeas hadap hcont hbdd T hu)) h

end Bridge

end MathFin
