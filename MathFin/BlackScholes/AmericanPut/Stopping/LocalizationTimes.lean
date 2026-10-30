/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FirstContact

/-!
# Interior stopping-time approximations to first contact

Stop before the price/payoff gap becomes small, before the driver leaves a
bounded interval, or before remaining maturity becomes small. These margins
are continuous and adapted, so their first zeros are actual stopping rules.

## Result

Public entry points include `localizationEps`, `localizationEps_pos`, `localizationEps_tendsto`,
`localizationMargin`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set Filter
open scoped NNReal Topology

/-- The margin `((n : ℝ)+1)⁻¹` of the `n`-th localization. -/
noncomputable def localizationEps (n : ℕ) : ℝ := ((n : ℝ)+1)⁻¹

theorem localizationEps_pos (n : ℕ) : 0 < localizationEps n := by
  unfold localizationEps
  positivity

theorem localizationEps_tendsto : Tendsto localizationEps atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

variable {Ω : Type*} [MeasurableSpace Ω]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Z W : ℝ≥0 → Ω → ℝ}

/-- The nonnegative slack in the three interior margins at time `t`: `Z` above `localizationEps n`,
`|W|` below `(n : ℝ)+1`, and remaining maturity above `localizationEps n`. -/
noncomputable def localizationMargin (Z W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max 0 (min (Z t ω-localizationEps n)
    (min ((n : ℝ)+1-|W t ω|) ((T : ℝ)-(t : ℝ)-localizationEps n)))

omit [MeasurableSpace Ω] in
theorem localizationMargin_continuous
    (hZ : ∀ ω, Continuous (fun t => Z t ω)) (hW : ∀ ω, Continuous (fun t => W t ω))
    (T : ℝ≥0) (n : ℕ) (ω : Ω) : Continuous (fun t => localizationMargin Z W T n t ω) := by
  unfold localizationMargin
  fun_prop

theorem localizationMargin_adapted (hZ : Adapted 𝓕 Z) (hW : Adapted 𝓕 W)
    (T : ℝ≥0) (n : ℕ) : Adapted 𝓕 (localizationMargin Z W T n) := by
  intro t
  have hzt := hZ t
  have hwt := hW t
  letI : MeasurableSpace Ω := 𝓕 t
  exact measurable_const.max ((hzt.sub measurable_const).min
    ((measurable_const.sub hwt.abs).min measurable_const))

omit [MeasurableSpace Ω] in
theorem localizationMargin_nonneg (Z W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    0 ≤ localizationMargin Z W T n t ω := le_max_left _ _

omit [MeasurableSpace Ω] in
theorem localizationMargin_terminal (Z W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    localizationMargin Z W T n T ω = 0 := by
  apply max_eq_left
  exact (min_le_right _ _).trans ((min_le_right _ _).trans (by
    have hh := (localizationEps_pos n).le
    linarith))

/-- The rule stopping at the first zero of `localizationMargin Z W T n`, capped at `T`. -/
noncomputable def interiorRule (hZ : Adapted 𝓕 Z) (hW : Adapted 𝓕 W)
    (hcZ : ∀ ω, Continuous (fun t => Z t ω)) (hcW : ∀ ω, Continuous (fun t => W t ω))
    (T : ℝ≥0) (n : ℕ) : StoppingRule 𝓕 T :=
  firstContactRule (localizationMargin_adapted hZ hW T n)
    (localizationMargin_continuous hcZ hcW T n)
    (localizationMargin_nonneg Z W T n) T (localizationMargin_terminal Z W T n)

theorem interiorRule_before (hZ : Adapted 𝓕 Z) (hW : Adapted 𝓕 W)
    (hcZ : ∀ ω, Continuous (fun t => Z t ω)) (hcW : ∀ ω, Continuous (fun t => W t ω))
    {T t : ℝ≥0} {n : ℕ} (ω : Ω) (ht : t < (interiorRule hZ hW hcZ hcW T n).time ω) :
    localizationEps n < Z t ω ∧ |W t ω| < (n : ℝ)+1 ∧
      (t : ℝ)+localizationEps n < T := by
  have hh := firstContactTime_pos_before (localizationMargin_continuous hcZ hcW T n)
    (localizationMargin_nonneg Z W T n) (localizationMargin_terminal Z W T n) ω ht
  change 0 < max 0 (min _ (min _ _)) at hh
  simp only [lt_max_iff,lt_self_iff_false,false_or,lt_min_iff] at hh
  exact ⟨by linarith [hh.1],by linarith [hh.2.1],by linarith [hh.2.2]⟩

/-- At a positive exit time the closed margins still hold. The positivity
condition is essential: an initially violated margin causes immediate stopping. -/
theorem interiorRule_at_positive_exit (hZ : Adapted 𝓕 Z) (hW : Adapted 𝓕 W)
    (hcZ : ∀ ω, Continuous (fun t => Z t ω)) (hcW : ∀ ω, Continuous (fun t => W t ω))
    {T : ℝ≥0} {n : ℕ} (ω : Ω)
    (hτ : 0 < (interiorRule hZ hW hcZ hcW T n).time ω) :
    let τ := (interiorRule hZ hW hcZ hcW T n).time ω
    localizationEps n ≤ Z τ ω ∧ |W τ ω| ≤ (n : ℝ)+1 ∧
      (τ : ℝ)+localizationEps n ≤ T := by
  let τ := (interiorRule hZ hW hcZ hcW T n).time ω
  have extend (F : ℝ≥0 → ℝ) (hF : Continuous F) (a : ℝ)
      (h : ∀ t < τ, a ≤ F t) : a ≤ F τ := by
    have hc : IsClosed {t | a ≤ F t} := isClosed_le continuous_const hF
    have hs : Iio τ ⊆ {t | a ≤ F t} := fun t ht => h t ht
    have hm : τ ∈ closure (Iio τ) := by
      rw [closure_Iio' (show (Iio τ).Nonempty from ⟨0,hτ⟩)]
      exact (show τ ≤ τ from le_rfl)
    exact hc.closure_subset_iff.mpr hs hm
  have hz := extend (fun t => Z t ω) (hcZ ω) (localizationEps n)
    (fun t ht => (interiorRule_before hZ hW hcZ hcW ω ht).1.le)
  have hw := extend (fun t => -|W t ω|) (hcW ω).abs.neg (-(n : ℝ)-1)
    (fun t ht => by linarith [(interiorRule_before hZ hW hcZ hcW ω ht).2.1])
  have ht := extend (fun t => -(t : ℝ)) continuous_subtype_val.neg
    (localizationEps n-(T : ℝ))
    (fun t ht => by linarith [(interiorRule_before hZ hW hcZ hcW ω ht).2.2])
  exact ⟨hz,by linarith,by linarith⟩

theorem interiorRule_le_contact (hZ : Adapted 𝓕 Z) (hW : Adapted 𝓕 W)
    (hcZ : ∀ ω, Continuous (fun t => Z t ω)) (hcW : ∀ ω, Continuous (fun t => W t ω))
    {T : ℝ≥0} (hterminal : ∀ ω, Z T ω = 0) (n : ℕ) (ω : Ω) :
    (interiorRule hZ hW hcZ hcW T n).time ω ≤ firstContactTime Z T ω := by
  obtain ⟨hT,hzero⟩ := firstContactTime_mem hcZ hterminal ω
  apply csInf_le ⟨0,fun _ _ => zero_le⟩
  refine ⟨hT,?_⟩
  change max 0 (min _ _) = 0
  apply max_eq_left
  exact (min_le_left _ _).trans (by rw [hzero]; linarith [localizationEps_pos n])

theorem interiorRule_eventually_after (hZ : Adapted 𝓕 Z) (hW : Adapted 𝓕 W)
    (hcZ : ∀ ω, Continuous (fun t => Z t ω)) (hcW : ∀ ω, Continuous (fun t => W t ω))
    (hnonneg : ∀ t ω, 0 ≤ Z t ω) {T : ℝ≥0} (hterminal : ∀ ω, Z T ω = 0)
    (ω : Ω) {u : ℝ≥0} (hu : u < firstContactTime Z T ω) :
    ∀ᶠ n in atTop, u < (interiorRule hZ hW hcZ hcW T n).time ω := by
  have huT : u < T := hu.trans_le (firstContactTime_mem hcZ hterminal ω).1
  obtain ⟨a,ha,hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (show (0 : ℝ≥0) ≤ u from zero_le)) (hcZ ω).continuousOn
  have hpos : 0 < Z a ω := firstContactTime_pos_before hcZ hnonneg hterminal ω (ha.2.trans_lt hu)
  obtain ⟨d,hd,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (show (0 : ℝ≥0) ≤ u from zero_le)) (hcW ω).abs.continuousOn
  have heps : ∀ᶠ n in atTop, localizationEps n < Z a ω :=
    localizationEps_tendsto.eventually (Iio_mem_nhds hpos)
  have htime : ∀ᶠ n in atTop, localizationEps n < (T : ℝ)-(u : ℝ) :=
    localizationEps_tendsto.eventually (Iio_mem_nhds (sub_pos.mpr (by exact_mod_cast huT)))
  have hradius : ∀ᶠ n : ℕ in atTop, |W d ω| < (n : ℝ)+1 :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop |W d ω|)
  filter_upwards [heps,htime,hradius] with n hn ht hnR
  by_contra! hle
  let τ := (interiorRule hZ hW hcZ hcW T n).time ω
  have hτ : τ ∈ Icc 0 u := ⟨zero_le,hle⟩
  have hzero := (firstContactTime_mem (localizationMargin_continuous hcZ hcW T n)
    (localizationMargin_terminal Z W T n) ω).2
  change localizationMargin Z W T n τ ω = 0 at hzero
  have hpositive : 0 < localizationMargin Z W T n τ ω := by
    apply lt_max_of_lt_right
    apply lt_min
    · exact sub_pos.mpr (hn.trans_le (hmin hτ))
    · apply lt_min
      · exact sub_pos.mpr ((hmax hτ).trans_lt hnR)
      · have hτu : (τ : ℝ) ≤ u := by exact_mod_cast hτ.2
        linarith
  exact (ne_of_gt hpositive) hzero

theorem interiorRule_tendsto_contact (hZ : Adapted 𝓕 Z) (hW : Adapted 𝓕 W)
    (hcZ : ∀ ω, Continuous (fun t => Z t ω)) (hcW : ∀ ω, Continuous (fun t => W t ω))
    (hnonneg : ∀ t ω, 0 ≤ Z t ω) {T : ℝ≥0} (hterminal : ∀ ω, Z T ω = 0) (ω : Ω) :
    Tendsto (fun n => (interiorRule hZ hW hcZ hcW T n).time ω) atTop
      (𝓝 (firstContactTime Z T ω)) := by
  apply tendsto_order.mpr
  constructor
  · intro u hu
    exact interiorRule_eventually_after hZ hW hcZ hcW hnonneg hterminal ω hu
  · intro u hu
    exact Eventually.of_forall
        (fun n => (interiorRule_le_contact hZ hW hcZ hcW hterminal n ω).trans_lt hu)

end MathFin.BlackScholes.AmericanPut.Stopping
