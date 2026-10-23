/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.LSVLeverage
public import MathFin.BlackScholes.JumpDiffusionDigital

/-!
# The coin-toss posterior is a conditional expectation

`BlackScholes/LSVLeverage.lean` defines the posterior variance of the coin-toss example of LSV
calibration by its Bayes formula,

  `m(K) = (v_lo·φ_lo(K) + v_hi·φ_hi(K)) / (φ_lo(K) + φ_hi(K))`   (`cointossM`),

with `φ_c` the zero-rate, unit-maturity lognormal density of branch volatility `σ_c`
(`cointossPhi`), and proves its analytic properties (below the unconditional mean at the money,
the wing limit `v_hi`, not constant in the strike). This file proves the interpretation that the
Bayes formula stands for. On the two-branch mixture (`cointossMix`: a standard normal draw on
the low or the high branch, each with probability `1/2`), with terminal price
`S_T = F·exp(σ_c z − σ_c²/2)` (`cointossST`) and branch variance `v` (`cointossV`),

  `m(S_T) = E[v | σ(S_T)]`   almost surely   (`cointossM_comp_ae_eq_condExp`),

and the posterior weight of the high branch is the conditional probability of that branch
(`cointossPostHi_comp_ae_eq_condExp`).

The proof is Mathlib's characterization of the conditional expectation
(`ae_eq_condExp_of_forall_setIntegral_eq`): on each branch the law of `S_T` is the density
`φ_c(K) dK` on `(0, ∞)` (`map_cointossBranch`, from the library's
`jumpDiffusionIncrementLaw_zero_map_mul_exp`), so for every Borel set `B` both
`∫_{S_T ∈ B} m(S_T)` and `∫_{S_T ∈ B} v` equal `½∫_B (v_lo·φ_lo + v_hi·φ_hi)`.

Not proved here: that an LSV model calibrated to a flat local volatility has leverage
`σ_loc/√m` (Gyöngy's mimicking theorem and the McKean–Vlasov existence question).
-/

@[expose] public section

namespace MathFin.LSV

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal


/-- **The coin-toss mixture**: on `ℝ ⊕ ℝ`, a standard normal draw `z` on the low branch
(`Sum.inl z`) or on the high branch (`Sum.inr z`), each branch with probability `1/2`. -/
noncomputable def cointossMix : Measure (ℝ ⊕ ℝ) :=
  (2⁻¹ : ℝ≥0) • (gaussianReal 0 1).map Sum.inl + (2⁻¹ : ℝ≥0) • (gaussianReal 0 1).map Sum.inr

instance cointossMix_isProbabilityMeasure : IsProbabilityMeasure cointossMix := by
  constructor
  rw [cointossMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply measurable_inl MeasurableSet.univ,
    Measure.map_apply measurable_inr MeasurableSet.univ]
  simp only [preimage_univ, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one]
  rw [← ENNReal.coe_add]
  norm_num

/-- **The terminal price** on each branch: `F·exp(σ_c z − σ_c²/2)`, the zero-rate, unit-maturity
lognormal price with branch volatility `σ_c`. -/
noncomputable def cointossST (F σ_lo σ_hi : ℝ) : ℝ ⊕ ℝ → ℝ :=
  Sum.elim (fun z ↦ F * Real.exp (σ_lo * z - σ_lo ^ 2 / 2))
    (fun z ↦ F * Real.exp (σ_hi * z - σ_hi ^ 2 / 2))

/-- **The branch variance**: `v_lo` on the low branch, `v_hi` on the high branch. -/
def cointossV (v_lo v_hi : ℝ) : ℝ ⊕ ℝ → ℝ := Sum.elim (fun _ ↦ v_lo) (fun _ ↦ v_hi)

/-- The terminal price is measurable. -/
lemma measurable_cointossST (F σ_lo σ_hi : ℝ) : Measurable (cointossST F σ_lo σ_hi) :=
  Measurable.sumElim (by fun_prop) (by fun_prop)

/-- The branch variance is measurable. -/
lemma measurable_cointossV (v_lo v_hi : ℝ) : Measurable (cointossV v_lo v_hi) :=
  Measurable.sumElim measurable_const measurable_const

/-- The branch density is measurable. -/
lemma measurable_cointossPhi (F σ : ℝ) : Measurable (cointossPhi F σ) := by
  unfold cointossPhi lognormalTerminalPDF bsd2 bsd1
  fun_prop

/-- The posterior variance is measurable. -/
lemma measurable_cointossM (F σ_lo σ_hi v_lo v_hi : ℝ) :
    Measurable (cointossM F σ_lo σ_hi v_lo v_hi) := by
  have h1 := measurable_cointossPhi F σ_lo
  have h2 := measurable_cointossPhi F σ_hi
  unfold cointossM
  fun_prop

/-- **The law of one branch's price is the branch density**: the pushforward of `N(0, 1)` under
`z ↦ F·exp(σz − σ²/2)` is `φ_σ(K) dK` on `(0, ∞)`, `φ_σ = cointossPhi F σ`. This is
`jumpDiffusionIncrementLaw_zero_map_mul_exp` at rate `0` and maturity `1`, after
`σz − σ²/2 ∼ N(−σ²/2, σ²)` (`gaussianReal_map_const_mul`, `gaussianReal_map_add_const`). -/
lemma map_cointossBranch {F σ : ℝ} (hF : 0 < F) (hσ : 0 < σ) :
    (gaussianReal 0 1).map (fun z ↦ F * Real.exp (σ * z - σ ^ 2 / 2)) =
      (volume.restrict (Ioi 0)).withDensity fun K ↦ ENNReal.ofReal (cointossPhi F σ K) := by
  have h1 : (gaussianReal 0 1).map (fun z ↦ σ * z - σ ^ 2 / 2) =
      jumpDiffusionIncrementLaw (0 - σ ^ 2 / 2) σ 0 (Measure.dirac 0) 1 := by
    rw [jumpDiffusionIncrementLaw_zero,
      show (fun z ↦ σ * z - σ ^ 2 / 2) = (fun y ↦ y + -(σ ^ 2 / 2)) ∘ (fun z ↦ σ * z) from by
        funext z; simp [sub_eq_add_neg],
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    congr 1
    simp
  have h2 := jumpDiffusionIncrementLaw_zero_map_mul_exp (S := F) (r := 0) hF hσ
    (Measure.dirac (0 : ℝ)) (τ := 1) one_pos
  rw [show (fun z ↦ F * Real.exp (σ * z - σ ^ 2 / 2)) =
      (fun y ↦ F * Real.exp y) ∘ (fun z ↦ σ * z - σ ^ 2 / 2) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), h1, h2]
  simp [cointossPhi]


/-- The terminal price is positive. -/
lemma cointossST_pos {F : ℝ} (hF : 0 < F) (σ_lo σ_hi : ℝ) (p : ℝ ⊕ ℝ) :
    0 < cointossST F σ_lo σ_hi p := by
  cases p <;> exact mul_pos hF (Real.exp_pos _)

/-- The branch variance is bounded by `|v_lo| + |v_hi|`. -/
lemma abs_cointossV_le (v_lo v_hi : ℝ) (p : ℝ ⊕ ℝ) : |cointossV v_lo v_hi p| ≤ |v_lo| + |v_hi| := by
  cases p
  · simp [cointossV]
  · simp [cointossV]

/-- At positive strikes the posterior variance is bounded by `2(|v_lo| + |v_hi|)`: it is
`v_lo + (v_hi − v_lo)·P(hi | K)` with `P(hi | K) ∈ [0, 1]`. -/
lemma abs_cointossM_le {F σ_lo σ_hi v_lo v_hi K : ℝ} (hlo : 0 < σ_lo) (hhi : 0 < σ_hi)
    (hK : 0 < K) : |cointossM F σ_lo σ_hi v_lo v_hi K| ≤ 2 * (|v_lo| + |v_hi|) := by
  have hφlo := cointossPhi_pos (F := F) hlo hK
  have hφhi := cointossPhi_pos (F := F) hhi hK
  have h0 : 0 ≤ cointossPostHi F σ_lo σ_hi K := div_nonneg hφhi.le (add_pos hφlo hφhi).le
  have h1 : cointossPostHi F σ_lo σ_hi K ≤ 1 :=
    (div_le_one (add_pos hφlo hφhi)).mpr (by linarith)
  have hp : |cointossPostHi F σ_lo σ_hi K| ≤ 1 := abs_le.mpr ⟨by linarith, h1⟩
  rw [cointossM_eq_of_pos hlo hhi hK]
  have hsub := abs_add_le v_hi (-v_lo)
  rw [abs_neg, ← sub_eq_add_neg] at hsub
  have hadd := abs_add_le v_lo ((v_hi - v_lo) * cointossPostHi F σ_lo σ_hi K)
  have hprod : |(v_hi - v_lo) * cointossPostHi F σ_lo σ_hi K| ≤ |v_hi - v_lo| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hp
  linarith [abs_nonneg v_lo, abs_nonneg v_hi]

/-- Integrals against the mixture are the average of the two branch integrals. -/
lemma integral_cointossMix {Ψ : ℝ ⊕ ℝ → ℝ} (hΨ : Measurable Ψ) {C : ℝ} (hC : ∀ p, |Ψ p| ≤ C) :
    ∫ p, Ψ p ∂cointossMix = 2⁻¹ * ∫ z, Ψ (Sum.inl z) ∂gaussianReal 0 1
      + 2⁻¹ * ∫ z, Ψ (Sum.inr z) ∂gaussianReal 0 1 := by
  have hint (μ : Measure (ℝ ⊕ ℝ)) [IsFiniteMeasure μ] : Integrable Ψ μ :=
    Integrable.of_bound hΨ.aestronglyMeasurable C
      (ae_of_all _ fun p ↦ by simpa [Real.norm_eq_abs] using hC p)
  rw [cointossMix, integral_add_measure (hint _) (hint _), integral_smul_nnreal_measure,
    integral_smul_nnreal_measure,
    integral_map measurable_inl.aemeasurable hΨ.aestronglyMeasurable,
    integral_map measurable_inr.aemeasurable hΨ.aestronglyMeasurable]
  simp [NNReal.smul_def]

/-- A branch integral of `1_B · h` at the branch price, as an integral against the branch
density on `(0, ∞)` (the density written `φ.toNNReal`, which is `φ` there). -/
lemma integral_indicator_branch {F σ : ℝ} (hF : 0 < F) (hσ : 0 < σ) {B : Set ℝ}
    (hB : MeasurableSet B) {h : ℝ → ℝ} (hh : Measurable h) :
    ∫ z, B.indicator h (F * Real.exp (σ * z - σ ^ 2 / 2)) ∂gaussianReal 0 1 =
      ∫ K, (cointossPhi F σ K).toNNReal • B.indicator h K ∂volume.restrict (Ioi 0) := by
  rw [← integral_map (μ := gaussianReal 0 1) (φ := fun z ↦ F * Real.exp (σ * z - σ ^ 2 / 2))
      (by fun_prop) (hh.indicator hB).aestronglyMeasurable, map_cointossBranch hF hσ]
  exact integral_withDensity_eq_integral_smul (measurable_cointossPhi F σ).real_toNNReal _

/-- The branch-density integrand of `integral_indicator_branch` is integrable when `h` is
bounded on the positive strikes. -/
lemma integrable_indicator_branch {F σ : ℝ} (hF : 0 < F) (hσ : 0 < σ) {B : Set ℝ}
    (hB : MeasurableSet B) {h : ℝ → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ K, 0 < K → |h K| ≤ C) :
    Integrable (fun K ↦ (cointossPhi F σ K).toNNReal • B.indicator h K)
      (volume.restrict (Ioi 0)) := by
  rw [← integrable_withDensity_iff_integrable_smul (measurable_cointossPhi F σ).real_toNNReal]
  change Integrable (B.indicator h)
    ((volume.restrict (Ioi 0)).withDensity fun K ↦ ENNReal.ofReal (cointossPhi F σ K))
  rw [← map_cointossBranch hF hσ,
    integrable_map_measure (hh.indicator hB).aestronglyMeasurable (by fun_prop)]
  refine Integrable.of_bound (((hh.indicator hB).comp (by fun_prop)).aestronglyMeasurable) C
    (ae_of_all _ fun z ↦ ?_)
  have hpos : 0 < F * Real.exp (σ * z - σ ^ 2 / 2) := mul_pos hF (Real.exp_pos _)
  exact (norm_indicator_le_norm_self _ _).trans (by simpa [Real.norm_eq_abs] using hC _ hpos)

/-- **The defining identity of the conditional expectation.** For every Borel set `B` of
strikes, `∫_{S_T ∈ B} m(S_T) dμ = ∫_{S_T ∈ B} v dμ` on the mixture. Each side splits into the two
branches; on `(0, ∞)` the branch densities turn it into
`∫_B m·(φ_lo + φ_hi) = ∫_B (v_lo·φ_lo + v_hi·φ_hi)`, which is the definition of `m`. -/
theorem setIntegral_cointossM_comp_eq {F σ_lo σ_hi v_lo v_hi : ℝ} (hF : 0 < F)
    (hlo : 0 < σ_lo) (hhi : 0 < σ_hi) {B : Set ℝ} (hB : MeasurableSet B) :
    ∫ p in cointossST F σ_lo σ_hi ⁻¹' B,
        cointossM F σ_lo σ_hi v_lo v_hi (cointossST F σ_lo σ_hi p) ∂cointossMix =
      ∫ p in cointossST F σ_lo σ_hi ⁻¹' B, cointossV v_lo v_hi p ∂cointossMix := by
  have hS := measurable_cointossST F σ_lo σ_hi
  have hm := measurable_cointossM F σ_lo σ_hi v_lo v_hi
  have hSB : MeasurableSet (cointossST F σ_lo σ_hi ⁻¹' B) := hS hB
  have hC (K : ℝ) (hK : 0 < K) : |cointossM F σ_lo σ_hi v_lo v_hi K| ≤ 2 * (|v_lo| + |v_hi|) :=
    abs_cointossM_le hlo hhi hK
  rw [← integral_indicator hSB, ← integral_indicator hSB,
    integral_cointossMix ((show Measurable fun p ↦
        cointossM F σ_lo σ_hi v_lo v_hi (cointossST F σ_lo σ_hi p) from hm.comp hS).indicator hSB)
      (C := 2 * (|v_lo| + |v_hi|))
      (fun p ↦ by
        rw [← Real.norm_eq_abs]
        refine (norm_indicator_le_norm_self _ _).trans ?_
        rw [Real.norm_eq_abs]
        exact hC _ (cointossST_pos hF _ _ p)),
    integral_cointossMix ((measurable_cointossV v_lo v_hi).indicator hSB) (C := |v_lo| + |v_hi|)
      (fun p ↦ by
        rw [← Real.norm_eq_abs]
        refine (norm_indicator_le_norm_self _ _).trans ?_
        rw [Real.norm_eq_abs]
        exact abs_cointossV_le _ _ p)]
  have i1 (z : ℝ) : (cointossST F σ_lo σ_hi ⁻¹' B).indicator
      (fun p ↦ cointossM F σ_lo σ_hi v_lo v_hi (cointossST F σ_lo σ_hi p)) (Sum.inl z) =
      B.indicator (cointossM F σ_lo σ_hi v_lo v_hi) (F * Real.exp (σ_lo * z - σ_lo ^ 2 / 2)) :=
    rfl
  have i2 (z : ℝ) : (cointossST F σ_lo σ_hi ⁻¹' B).indicator
      (fun p ↦ cointossM F σ_lo σ_hi v_lo v_hi (cointossST F σ_lo σ_hi p)) (Sum.inr z) =
      B.indicator (cointossM F σ_lo σ_hi v_lo v_hi) (F * Real.exp (σ_hi * z - σ_hi ^ 2 / 2)) :=
    rfl
  have i3 (z : ℝ) : (cointossST F σ_lo σ_hi ⁻¹' B).indicator (cointossV v_lo v_hi) (Sum.inl z) =
      B.indicator (fun _ ↦ v_lo) (F * Real.exp (σ_lo * z - σ_lo ^ 2 / 2)) :=
    rfl
  have i4 (z : ℝ) : (cointossST F σ_lo σ_hi ⁻¹' B).indicator (cointossV v_lo v_hi) (Sum.inr z) =
      B.indicator (fun _ ↦ v_hi) (F * Real.exp (σ_hi * z - σ_hi ^ 2 / 2)) :=
    rfl
  simp_rw [i1, i2, i3, i4]
  rw [integral_indicator_branch hF hlo hB hm, integral_indicator_branch hF hhi hB hm,
    integral_indicator_branch hF hlo hB measurable_const,
    integral_indicator_branch hF hhi hB measurable_const, ← mul_add, ← mul_add,
    ← integral_add (integrable_indicator_branch hF hlo hB hm hC)
      (integrable_indicator_branch hF hhi hB hm hC),
    ← integral_add (integrable_indicator_branch hF hlo hB measurable_const
        (C := |v_lo|) fun _ _ ↦ le_rfl)
      (integrable_indicator_branch hF hhi hB measurable_const (C := |v_hi|) fun _ _ ↦ le_rfl)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun K hK ↦ ?_
  have hφlo := cointossPhi_pos (F := F) hlo hK
  have hφhi := cointossPhi_pos (F := F) hhi hK
  have hsum : cointossPhi F σ_lo K + cointossPhi F σ_hi K ≠ 0 := (add_pos hφlo hφhi).ne'
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hφlo.le,
    Real.coe_toNNReal _ hφhi.le]
  by_cases hKB : K ∈ B
  · simp only [Set.indicator_of_mem hKB, cointossM]
    rw [← add_mul, mul_div_cancel₀ _ hsum]
    ring
  · simp [Set.indicator_of_notMem hKB]

/-- **The posterior variance is the conditional expectation of the variance given the
terminal price.** For `F, σ_lo, σ_hi > 0`, on the coin-toss mixture
`m(S_T) = E[v | σ(S_T)]` almost surely, `m = cointossM F σ_lo σ_hi v_lo v_hi` the Bayes formula
of Ex. 11.2. Mathlib's characterization `ae_eq_condExp_of_forall_setIntegral_eq` with
`setIntegral_cointossM_comp_eq`. -/
theorem cointossM_comp_ae_eq_condExp {F σ_lo σ_hi v_lo v_hi : ℝ} (hF : 0 < F)
    (hlo : 0 < σ_lo) (hhi : 0 < σ_hi) :
    (fun p ↦ cointossM F σ_lo σ_hi v_lo v_hi (cointossST F σ_lo σ_hi p)) =ᵐ[cointossMix]
      cointossMix[cointossV v_lo v_hi |
        MeasurableSpace.comap (cointossST F σ_lo σ_hi) inferInstance] := by
  have hS := measurable_cointossST F σ_lo σ_hi
  have hm := measurable_cointossM F σ_lo σ_hi v_lo v_hi
  have hV : Integrable (cointossV v_lo v_hi) cointossMix :=
    Integrable.of_bound (measurable_cointossV v_lo v_hi).aestronglyMeasurable (|v_lo| + |v_hi|)
      (ae_of_all _ fun p ↦ by simpa [Real.norm_eq_abs] using abs_cointossV_le v_lo v_hi p)
  have hg : Integrable (fun p ↦ cointossM F σ_lo σ_hi v_lo v_hi (cointossST F σ_lo σ_hi p))
      cointossMix :=
    Integrable.of_bound (hm.comp hS).aestronglyMeasurable (2 * (|v_lo| + |v_hi|))
      (ae_of_all _ fun p ↦ by
        simpa [Real.norm_eq_abs] using abs_cointossM_le (v_lo := v_lo) (v_hi := v_hi) hlo hhi
          (cointossST_pos hF σ_lo σ_hi p))
  refine ae_eq_condExp_of_forall_setIntegral_eq hS.comap_le hV (fun s _ _ ↦ hg.integrableOn) ?_
    ((hm.comp (comap_measurable _)).aestronglyMeasurable)
  rintro s ⟨B, hB, rfl⟩ _
  exact setIntegral_cointossM_comp_eq hF hlo hhi hB

/-- **The posterior weight is the conditional probability of the high branch.** For
`F, σ_lo, σ_hi > 0`, `P(hi | S_T) = φ_hi(S_T)/(φ_lo(S_T) + φ_hi(S_T))` almost surely: the case
`v_lo = 0`, `v_hi = 1` of `cointossM_comp_ae_eq_condExp`, `cointossV 0 1` being the indicator of
the high branch. -/
theorem cointossPostHi_comp_ae_eq_condExp {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : 0 < σ_hi) :
    (fun p ↦ cointossPostHi F σ_lo σ_hi (cointossST F σ_lo σ_hi p)) =ᵐ[cointossMix]
      cointossMix[cointossV 0 1 | MeasurableSpace.comap (cointossST F σ_lo σ_hi) inferInstance] :=
  (Filter.EventuallyEq.of_eq (funext fun p ↦ by simp [cointossM, cointossPostHi])).trans
    (cointossM_comp_ae_eq_condExp (v_lo := 0) (v_hi := 1) hF hlo hhi)

end MathFin.LSV
