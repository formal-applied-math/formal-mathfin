/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.Rules

/-!
# First contact for a nonnegative continuous adapted process

The first zero by a fixed horizon is an admissible stopping rule if the
process vanishes at that horizon. The proof uses compact minima and measurable
infima, not a usual-filtration or continuous-time debut theorem assumption.

## Result

Public entry points include `measurable_zero_hit`, `firstContactTime`, `firstContactTime_mem`,
`firstContactTime_le_iff`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Z : ℝ≥0 → Ω → ℝ}

theorem measurable_zero_hit (hadapt : Adapted 𝓕 Z)
    (hcont : ∀ ω, Continuous (fun t => Z t ω))
    (hnonneg : ∀ t ω, 0 ≤ Z t ω) (u t : ℝ≥0) (hut : u ≤ t) :
    MeasurableSet[𝓕 t] {ω | ∃ s ∈ Icc 0 u, Z s ω = 0} := by
  let M : Ω → ℝ≥0∞ := fun ω => ⨅ s : Icc (0 : ℝ≥0) u, ENNReal.ofReal (Z s ω)
  have hm : @Measurable Ω ℝ≥0∞ (𝓕 t) _ M := by
    have hh : @Measurable Ω ℝ≥0∞ (𝓕 t) _
        (⨅ s : Icc (0 : ℝ≥0) u, fun ω => ENNReal.ofReal (Z s ω)) := by
      apply measurable_iInf_of_upperSemicontinuous
      · intro s
        exact (hadapt s).mono (𝓕.mono (s.property.2.trans hut)) le_rfl |>.ennreal_ofReal
      · intro ω
        exact (ENNReal.continuous_ofReal.comp
            ((hcont ω).comp continuous_subtype_val)).upperSemicontinuous
    have heq : (⨅ s : Icc (0 : ℝ≥0) u, fun ω => ENNReal.ofReal (Z s ω)) = M := by
      funext ω
      simp only [iInf_apply,M]
    rwa [heq] at hh
  have he : {ω | ∃ s ∈ Icc 0 u, Z s ω = 0} = {ω | M ω = 0} := by
    ext ω
    constructor
    · rintro ⟨s,hs,hzero⟩
      apply le_antisymm _ bot_le
      exact (iInf_le (fun s : Icc (0 : ℝ≥0) u => ENNReal.ofReal (Z s ω)) ⟨s,hs⟩).trans
        (by simp [hzero])
    · intro hz
      obtain ⟨s,hs,hmin⟩ := isCompact_Icc.exists_isMinOn
        (nonempty_Icc.mpr (show (0 : ℝ≥0) ≤ u from zero_le)) (hcont ω).continuousOn
      have hle : ENNReal.ofReal (Z s ω) ≤ M ω :=
        le_iInf (fun j => ENNReal.ofReal_le_ofReal (hmin j.property))
      rw [hz] at hle
      exact ⟨s,hs,le_antisymm (ENNReal.ofReal_eq_zero.mp (le_antisymm hle bot_le)) (hnonneg s ω)⟩
  rw [he]
  exact measurableSet_eq_fun hm measurable_const

/-- The infimum of the times `t ≤ T` at which `Z t ω` vanishes. -/
noncomputable def firstContactTime (Z : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  sInf {t | t ≤ T ∧ Z t ω = 0}

omit [MeasurableSpace Ω] in
theorem firstContactTime_mem (hcont : ∀ ω, Continuous (fun t => Z t ω))
    {T : ℝ≥0} (hterminal : ∀ ω, Z T ω = 0) (ω : Ω) :
    firstContactTime Z T ω ≤ T ∧ Z (firstContactTime Z T ω) ω = 0 := by
  have hc : IsClosed {t | t ≤ T ∧ Z t ω = 0} :=
    isClosed_Iic.inter (isClosed_eq (hcont ω) continuous_const)
  exact hc.csInf_mem ⟨T,le_rfl,hterminal ω⟩ ⟨0,fun _ _ => zero_le⟩

omit [MeasurableSpace Ω] in
theorem firstContactTime_le_iff (hcont : ∀ ω, Continuous (fun t => Z t ω))
    {T : ℝ≥0} (hterminal : ∀ ω, Z T ω = 0) (ω : Ω) (t : ℝ≥0) :
    firstContactTime Z T ω ≤ t ↔ ∃ s ∈ Icc 0 (min t T), Z s ω = 0 := by
  constructor
  · intro ht
    obtain ⟨hT,hzero⟩ := firstContactTime_mem hcont hterminal ω
    exact ⟨firstContactTime Z T ω,⟨zero_le,le_min ht hT⟩,hzero⟩
  · rintro ⟨s,hs,hzero⟩
    exact (csInf_le (show BddBelow {u | u ≤ T ∧ Z u ω = 0} from ⟨0,fun _ _ => zero_le⟩)
      ⟨hs.2.trans (min_le_right t T),hzero⟩).trans (hs.2.trans (min_le_left t T))

/-- The first contact time as an admissible bounded rule, for a nonnegative continuous adapted
`Z` that vanishes at the horizon `T`. -/
noncomputable def firstContactRule (hadapt : Adapted 𝓕 Z)
    (hcont : ∀ ω, Continuous (fun t => Z t ω)) (hnonneg : ∀ t ω, 0 ≤ Z t ω)
    (T : ℝ≥0) (hterminal : ∀ ω, Z T ω = 0) : StoppingRule 𝓕 T where
  time := firstContactTime Z T
  stopping := by
    intro t
    simpa only [WithTop.coe_le_coe,firstContactTime_le_iff hcont hterminal] using
      measurable_zero_hit hadapt hcont hnonneg (min t T) t (min_le_left t T)
  le_horizon := fun ω => (firstContactTime_mem hcont hterminal ω).1

omit [MeasurableSpace Ω] in
theorem firstContactTime_pos_before (hcont : ∀ ω, Continuous (fun t => Z t ω))
    (hnonneg : ∀ t ω, 0 ≤ Z t ω) {T : ℝ≥0} (hterminal : ∀ ω, Z T ω = 0)
    {t : ℝ≥0} (ω : Ω) (ht : t < firstContactTime Z T ω) : 0 < Z t ω := by
  apply lt_of_le_of_ne (hnonneg t ω)
  intro he
  have hT := (firstContactTime_mem hcont hterminal ω).1
  exact (not_le.mpr ht) (csInf_le ⟨0,fun _ _ => zero_le⟩ ⟨ht.le.trans hT,he.symm⟩)

end MathFin.BlackScholes.AmericanPut.Stopping
