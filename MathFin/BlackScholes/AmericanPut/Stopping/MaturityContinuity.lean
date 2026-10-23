/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.MaturityTruncation
public import MathFin.BlackScholes.AmericanPut.Stopping.UsualBrownianValue

/-! # Maturity continuity of the actual American stopping supremum

No classical PDE solution, boundary regularity, or existence of an optimal
stopping rule is assumed. Nearly optimal admissible rules suffice.

## Result

Public entry points include `americanPutValue_continuous_horizon`,
`brownianAmericanPut_continuous_horizon`, `brownianUsualAmericanPut_continuous_horizon`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

theorem americanPutValue_continuous_horizon {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {W : ℝ≥0 → Ω → ℝ} (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    {K r q σ S : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    Continuous (americanPutValue P 𝓕 W K r q σ S) := by
  apply continuous_iff_seqContinuous.mpr
  intro Tn T hT
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨_,⟨θ,rfl⟩,hθ⟩ := exists_lt_of_lt_csSup
      (exerciseValues_nonempty (P := P) (𝓕 := 𝓕) (W := W) (K := K) (r := r) (q := q) (σ := σ)
          (S := S) (T := T)) ha
    have he := expectedReward_fixed_truncate_tendsto (P := P) (q := q) (σ := σ)
      hW hpaths hK hr hS hT θ
    filter_upwards [he.eventually (Ioi_mem_nhds hθ)] with n hn
    exact hn.trans_le (expectedReward_le_value hW hK hr hS (θ.truncate (Tn n)))
  · intro c hc
    have happrox (n : ℕ) : ∃ θ : BoundedRule 𝓕 (Tn n),
        americanPutValue P 𝓕 W K r q σ S (Tn n)-localizationEps n <
          ∫ ω, putReward W K r q σ S θ.time ω ∂P := by
      obtain ⟨_,⟨θ,rfl⟩,hθ⟩ := exists_lt_of_lt_csSup
        (exerciseValues_nonempty (P := P) (𝓕 := 𝓕) (W := W) (K := K) (r := r) (q := q) (σ := σ)
            (S := S) (T := Tn n))
        (sub_lt_self _ (localizationEps_pos n))
      exact ⟨θ,hθ⟩
    choose θ hθ using happrox
    have hd := expectedReward_truncate_tendsto (P := P) (q := q) (σ := σ)
      hW hpaths hK hr hS hT θ
    have he : Tendsto (fun n => ((∫ ω, putReward W K r q σ S (θ n).time ω ∂P) -
        ∫ ω, putReward W K r q σ S ((θ n).truncate T).time ω ∂P)+localizationEps n)
        atTop (𝓝 0) := by simpa only [add_zero] using hd.add localizationEps_tendsto
    filter_upwards [he.eventually (Iio_mem_nhds (sub_pos.mpr hc))] with n hn
    have hle := expectedReward_le_value (P := P) (q := q) (σ := σ) hW hK hr hS ((θ n).truncate T)
    have hh := hθ n
    change americanPutValue P 𝓕 W K r q σ S (Tn n) < c
    linarith

theorem brownianAmericanPut_continuous_horizon {K r q σ S : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) : Continuous (brownianAmericanPut K r q σ S) :=
  americanPutValue_continuous_horizon measurable_brownian_uncurry continuous_brownian hK hr hS

theorem brownianUsualAmericanPut_continuous_horizon {K r q σ S : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) : Continuous (brownianUsualAmericanPut K r q σ S) := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact americanPutValue_continuous_horizon (P := μ) (𝓕 := brownianUsualFiltration)
    brownian_completed_measurable continuous_brownian hK hr hS

end MathFin.BlackScholes.AmericanPut.Stopping
