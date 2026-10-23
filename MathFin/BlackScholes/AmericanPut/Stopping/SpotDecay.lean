/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.MaturityContinuity

/-! # Large-spot decay of the actual stopping supremum

On each continuous path, the GBM multiplier has a strictly positive minimum
over a fixed finite horizon. Hence even varying stopping rules eventually
have zero payoff as their initial spots tend to infinity. Bounded convergence
and nearly optimal rules transfer this fact to the American supremum.

## Result

Public entry points include `putReward_eventually_zero`, `expectedReward_tendsto_zero_spot`,
`americanPutValue_spot_seq_decay`, `americanPutValue_spot_decay`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

theorem putReward_eventually_zero {Ω : Type*} {W : ℝ≥0 → Ω → ℝ}
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (K r q σ : ℝ)
    {S : ℕ → ℝ} (hS : Tendsto S atTop atTop) {T : ℝ≥0}
    {θ : ℕ → Ω → ℝ≥0} (hθ : ∀ n ω, θ n ω ≤ T) (ω : Ω) :
    ∀ᶠ n in atTop, putReward W K r q σ (S n) (θ n) ω = 0 := by
  let G : ℝ≥0 → ℝ := fun t => Real.exp (((r-q)-σ^2/2)*(t : ℝ)+σ*W t ω)
  have hc : Continuous G := by dsimp [G]; fun_prop
  obtain ⟨u,_,hu⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (show (0 : ℝ≥0) ≤ T from bot_le)) hc.continuousOn
  have hg : 0 < G u := Real.exp_pos _
  filter_upwards [hS.eventually_ge_atTop (max 0 (K/G u))] with n hn
  have hn0 : 0 ≤ S n := (le_max_left _ _).trans hn
  have hK : K ≤ S n * G u := (div_le_iff₀ hg).mp ((le_max_right _ _).trans hn)
  have hmin : G u ≤ G (θ n ω) := hu ⟨bot_le,hθ n ω⟩
  have hstock : K ≤ S n * G (θ n ω) := hK.trans (mul_le_mul_of_nonneg_left hmin hn0)
  change Real.exp _ * max (K-S n*G (θ n ω)) 0 = 0
  rw [max_eq_right (sub_nonpos.mpr hstock),mul_zero]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
  {K r q σ : ℝ} {T : ℝ≥0}

theorem expectedReward_tendsto_zero_spot (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 ≤ K) (hr : 0 ≤ r) {S : ℕ → ℝ}
    (hS0 : ∀ n, 0 ≤ S n) (hS : Tendsto S atTop atTop)
    (θ : ℕ → BoundedRule 𝓕 T) :
    Tendsto (fun n => ∫ ω, putReward W K r q σ (S n) (θ n).time ω ∂P)
      atTop (𝓝 0) := by
  have hh : Tendsto (fun n => ∫ ω, putReward W K r q σ (S n) (θ n).time ω ∂P)
      atTop (𝓝 (∫ _ : Ω, (0 : ℝ) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => K)
    · intro n
      exact (putReward_measurable hW K r q σ (S n) (θ n).measurable_time).aestronglyMeasurable
    · exact integrable_const K
    · intro n
      apply Eventually.of_forall
      intro ω
      rw [Real.norm_eq_abs,abs_of_nonneg (putReward_nonneg W K r q σ _ _ ω)]
      exact putReward_le_strike W hK hr (hS0 n) _ ω
    · apply Eventually.of_forall
      intro ω
      have hz : (fun n => putReward W K r q σ (S n) (θ n).time ω) =ᶠ[atTop] fun _ => 0 :=
        putReward_eventually_zero hpaths K r q σ hS (fun n ω => (θ n).le_horizon ω) ω
      exact tendsto_const_nhds.congr' hz.symm
  simpa only [integral_zero] using hh

theorem americanPutValue_spot_seq_decay (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    (hK : 0 ≤ K) (hr : 0 ≤ r) {S : ℕ → ℝ}
    (hS0 : ∀ n, 0 ≤ S n) (hS : Tendsto S atTop atTop) :
    Tendsto (fun n => americanPutValue P 𝓕 W K r q σ (S n) T) atTop (𝓝 0) := by
  have happrox (n : ℕ) : ∃ θ : BoundedRule 𝓕 T,
      americanPutValue P 𝓕 W K r q σ (S n) T-localizationEps n <
        ∫ ω, putReward W K r q σ (S n) θ.time ω ∂P := by
    obtain ⟨_,⟨θ,rfl⟩,hθ⟩ := exists_lt_of_lt_csSup
      (exerciseValues_nonempty (P := P) (𝓕 := 𝓕) (W := W) (K := K) (r := r)
        (q := q) (σ := σ) (S := S n) (T := T))
      (sub_lt_self _ (localizationEps_pos n))
    exact ⟨θ,hθ⟩
  choose θ hθ using happrox
  have he := expectedReward_tendsto_zero_spot (P := P) (q := q) (σ := σ)
    hW hpaths hK hr hS0 hS θ
  have hu : Tendsto (fun n => (∫ ω, putReward W K r q σ (S n) (θ n).time ω ∂P)+
      localizationEps n) atTop (𝓝 0) := by
    simpa only [add_zero] using he.add localizationEps_tendsto
  apply squeeze_zero (fun n => value_nonneg hW hK hr (hS0 n)) ?_ hu
  intro n
  linarith [hθ n]

theorem americanPutValue_spot_decay (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    Tendsto (fun S => americanPutValue P 𝓕 W K r q σ S T) atTop (𝓝 0) := by
  have hn := americanPutValue_spot_seq_decay (P := P) (𝓕 := 𝓕) (q := q) (σ := σ) (T := T)
    hW hpaths hK hr (fun n : ℕ => (Nat.cast_nonneg n : (0 : ℝ) ≤ n)) tendsto_natCast_atTop_atTop
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with S hS
    exact ha.trans_le (value_nonneg hW hK hr hS)
  · intro c hc
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hn.eventually (Iio_mem_nhds hc))
    filter_upwards [eventually_ge_atTop (N : ℝ)] with S hS
    have hS0 : 0 ≤ S := (Nat.cast_nonneg N).trans hS
    exact (value_antitone_spot hW hK hr
      (by change (0 : ℝ) ≤ (N : ℝ); positivity) hS0 hS).trans_lt (hN N le_rfl)

/-- The tail estimate is uniform over every bounded interval of maturities. -/
theorem americanPutValue_spot_decay_uniform (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S in atTop, ∀ t : ℝ≥0, t ≤ T →
      0 ≤ americanPutValue P 𝓕 W K r q σ S t ∧ americanPutValue P 𝓕 W K r q σ S t < ε := by
  have hd := americanPutValue_spot_decay (P := P) (𝓕 := 𝓕) (q := q) (σ := σ) (T := T)
    hW hpaths hK hr
  filter_upwards [eventually_ge_atTop (0 : ℝ),hd.eventually (Iio_mem_nhds hε)] with S hS htail
  intro t ht
  exact ⟨value_nonneg hW hK hr hS,(value_mono_horizon hW hK hr hS ht).trans_lt htail⟩

end MathFin.BlackScholes.AmericanPut.Stopping
