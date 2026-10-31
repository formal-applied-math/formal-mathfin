/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FiltrationExtension
public import MathFin.BlackScholes.AmericanPut.Stopping.ClassicalSupermartingale

/-! # American values under right-continuous ambient-null augmentation

This extension stays inside the given ambient measurable space. It must not
be confused with completing that space by all subsets of null sets.

## Result

Public entry points include `StoppingRule.enlargeFiltration`, `americanPutValue_mono_filtration`,
`brownianRightAugFiltration`, `brownianFiltration_le_rightAug`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology
open MathFin.ItoLocalMartingale (nullAugmentation supermartingale_nullAugmentation)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The rule `θ` reread in a larger filtration `𝓖 ≥ 𝓕`: the same exercise time, still a
stopping time and still bounded by `T`. -/
def StoppingRule.enlargeFiltration {𝓕 𝓖 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {T : ℝ≥0} (θ : StoppingRule 𝓕 T) (hFG : 𝓕 ≤ 𝓖) : StoppingRule 𝓖 T where
  time := θ.time
  stopping := fun t => hFG t _ (θ.stopping t)
  le_horizon := θ.le_horizon

theorem americanPutValue_mono_filtration {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 𝓖 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
    {K r q σ S : ℝ} {T : ℝ≥0} (hFG : 𝓕 ≤ 𝓖)
    (hW : Measurable W.uncurry) (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    americanPutValue P 𝓕 W K r q σ S T ≤ americanPutValue P 𝓖 W K r q σ S T := by
  refine stoppingValue_le univ_nonempty fun θ _ ↦ ?_
  exact expectedReward_le_value hW hK hr hS (θ.enlargeFiltration hFG)

/-- The right-continuous regularization of the raw Brownian filtration after adjoining the
`gaussianLimit`-null ambient sets. -/
noncomputable def brownianRightAugFiltration :=
  (nullAugmentation brownianFiltration gaussianLimit).rightCont

theorem brownianFiltration_le_rightAug : brownianFiltration ≤ brownianRightAugFiltration :=
  le_trans le_sup_left (nullAugmentation brownianFiltration gaussianLimit).le_rightCont

instance brownianRightAugFiltration_isRightContinuous :
    brownianRightAugFiltration.IsRightContinuous :=
  inferInstanceAs
      ((nullAugmentation brownianFiltration gaussianLimit).rightCont.IsRightContinuous)

theorem brownianRightAugFiltration_contains_null {s : Set (ℝ≥0 → ℝ)}
    (hs : MeasurableSet s) (hnull : gaussianLimit s = 0) (t : ℝ≥0) :
    MeasurableSet[brownianRightAugFiltration t] s := by
  apply (nullAugmentation brownianFiltration gaussianLimit).le_rightCont t
  apply (show MathFin.ItoLocalMartingale.nullsAlg _ gaussianLimit ≤
    nullAugmentation brownianFiltration gaussianLimit t from le_sup_right)
  exact MeasurableSpace.measurableSet_generateFrom ⟨hs,hnull⟩

/-- The finite-horizon American put value of the constructed Brownian model, taken over the
rules of `brownianRightAugFiltration`. -/
noncomputable def brownianRightAugAmericanPut (K r q σ S : ℝ) (T : ℝ≥0) : ℝ :=
  americanPutValue gaussianLimit brownianRightAugFiltration brownian K r q σ S T

theorem brownianClassicalCandidate_rightAug_supermartingale {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hσ : 0 < σ) (T : ℝ≥0) :
    Supermartingale (classicalCandidate brownian K r q σ S p T) brownianRightAugFiltration
        gaussianLimit := by
  apply bounded_continuous_supermartingale_rightCont
    (supermartingale_nullAugmentation
        (brownianClassicalCandidate_supermartingale hp.toPutEnvelope hp.putWaiting hK hr hσ T))
    (classicalCandidate_continuous hp.toPutEnvelope continuous_brownian T) (C := K)
  intro t ω
  obtain ⟨hlo,hhi⟩ := classicalCandidate_bounds (q := q) (σ := σ) (S := S) hp.toPutEnvelope brownian hK hr T t ω
  simpa only [Real.norm_eq_abs,abs_of_nonneg hlo] using hhi

theorem brownianRightAugAmericanPut_eq_raw {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) (hS : 0 < S) (T : ℝ≥0) :
    brownianRightAugAmericanPut K r q σ S T = brownianAmericanPut K r q σ S T := by
  apply le_antisymm
  · have hu := value_le_supermartingale_candidate measurable_brownian_uncurry hK.le hr hS.le
      (brownianClassicalCandidate_rightAug_supermartingale hp hK.le hr hσ T)
      (classicalCandidate_continuous hp.toPutEnvelope continuous_brownian T) (C := K)
      (fun t ω => by
        obtain ⟨hlo,hhi⟩ :=
            classicalCandidate_bounds (q := q) (σ := σ) (S := S) hp.toPutEnvelope brownian hK.le hr T t ω
        simpa only [Real.norm_eq_abs,abs_of_nonneg hlo] using hhi)
      (fun _ ht ω => classicalCandidate_dominates hp.toPutEnvelope brownian hK hS ht ω)
    rw [integral_congr_ae (classicalCandidate_initial isBrownianReal_brownian.eval_zero_ae_eq_zero
      K r q σ S p T)] at hu
    simp only [integral_const,probReal_univ,one_smul] at hu
    rw [brownian_price_identification hp hK hr hS hσ]
    convert! hu using 1
  · exact americanPutValue_mono_filtration brownianFiltration_le_rightAug
      measurable_brownian_uncurry hK.le hr hS.le

end MathFin.BlackScholes.AmericanPut.Stopping
