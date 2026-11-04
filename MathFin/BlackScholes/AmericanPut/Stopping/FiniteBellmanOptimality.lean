/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.DiscreteContactMartingale
public import MathFin.Foundations.SnellEnvelope

/-! # First-contact attainment of the finite Snell envelope (the Bellman recursion)

## Result

Public entry points include `snellContact`, `snellContact_le`,
`snellContact_stopping`, `snellContact_contact`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ}

/-- The first index in `[0,N]` at which the Snell envelope meets the reward, that is at which
`snellEnvelope P 𝓕 Set.univ Z N i-Z (min i N)` vanishes. -/
noncomputable def snellContact (P : Measure Ω) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›)
    (Z : ℕ → Ω → ℝ) (N : ℕ) : Ω → ℕ :=
  hittingBtwn (fun i ω => snellEnvelope P 𝓕 Set.univ Z N i ω-Z (min i N) ω) {0} 0 N

theorem snellContact_le (N : ℕ) (ω : Ω) : snellContact P 𝓕 Z N ω ≤ N :=
  hittingBtwn_le ω

theorem snellContact_stopping (ha : Adapted 𝓕 Z) (N : ℕ) :
    IsStoppingTime 𝓕 (fun ω => (snellContact P 𝓕 Z N ω : WithTop ℕ)) := by
  apply Adapted.isStoppingTime_hittingBtwn ?_ (measurableSet_singleton 0)
  intro i
  exact ((snellEnvelope_stronglyAdapted ha N i).measurable).sub
    ((ha (min i N)).mono (𝓕.mono (min_le_left _ _)) le_rfl)

theorem snellContact_contact (N : ℕ) (ω : Ω) :
    snellEnvelope P 𝓕 Set.univ Z N (snellContact P 𝓕 Z N ω) ω =
      Z (snellContact P 𝓕 Z N ω) ω := by
  have he : ∃ j ∈ Icc 0 N, snellEnvelope P 𝓕 Set.univ Z N j ω-Z (min j N) ω ∈ ({0} : Set ℝ) := by
    refine ⟨N,⟨Nat.zero_le _,le_rfl⟩,?_⟩
    simp [snellEnvelope_after_horizon le_rfl]
  have hh := hittingBtwn_mem_set
    (u := fun i ω => snellEnvelope P 𝓕 Set.univ Z N i ω-Z (min i N) ω) (ω := ω) he
  have hbound := snellContact_le (P := P) (𝓕 := 𝓕) (Z := Z) N ω
  change snellEnvelope P 𝓕 Set.univ Z N (snellContact P 𝓕 Z N ω) ω-
    Z (min (snellContact P 𝓕 Z N ω) N) ω = 0 at hh
  rw [min_eq_left hbound] at hh
  exact sub_eq_zero.mp hh

theorem snellContact_before (N i : ℕ) (ω : Ω)
    (ht : i < snellContact P 𝓕 Z N ω) :
    P[snellEnvelope P 𝓕 Set.univ Z N (i+1) | 𝓕 i] ω = snellEnvelope P 𝓕 Set.univ Z N i ω := by
  have hiN : i < N := ht.trans_le (snellContact_le N ω)
  have hn := notMem_of_lt_hittingBtwn
    (u := fun i ω => snellEnvelope P 𝓕 Set.univ Z N i ω-Z (min i N) ω)
    (s := ({0} : Set ℝ)) ht (Nat.zero_le i)
  have hne : snellEnvelope P 𝓕 Set.univ Z N i ω ≠ Z i ω := by
    simpa only [mem_singleton_iff,min_eq_left hiN.le,sub_eq_zero] using hn
  have hv : Z i ω < snellEnvelope P 𝓕 Set.univ Z N i ω := lt_of_le_of_ne
    (by simpa only [min_eq_left hiN.le] using
          snellEnvelope_dominates (P := P) (𝓕 := 𝓕) (Z := Z) (N := N) (Or.inl (mem_univ i)) ω)
    hne.symm
  have he := congrFun (snellEnvelope_succ_of_mem (P := P) (𝓕 := 𝓕) (Z := Z) hiN (mem_univ i)) ω
  rw [he] at hv
  have hc := (lt_max_iff.mp hv).resolve_left (lt_irrefl _)
  exact (he.trans (max_eq_right hc.le)).symm

variable [IsProbabilityMeasure P]

theorem snellContact_martingale (ha : Adapted 𝓕 Z)
    (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    Martingale (stoppedProcess (snellEnvelope P 𝓕 Set.univ Z N)
      (fun ω => (snellContact P 𝓕 Z N ω : WithTop ℕ))) 𝓕 P :=
  discrete_stopped_martingale_of_before (snellEnvelope_stronglyAdapted ha N)
    (snellEnvelope_integrable hi N) (snellContact_stopping ha N)
    (snellContact_before N)

theorem snellContact_expected_payoff (ha : Adapted 𝓕 Z)
    (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    (∫ ω, Z (snellContact P 𝓕 Z N ω) ω ∂P) =
      ∫ ω, snellEnvelope P 𝓕 Set.univ Z N 0 ω ∂P := by
  have hm := snellContact_martingale ha hi N
  have h0 : stoppedProcess (snellEnvelope P 𝓕 Set.univ Z N)
      (fun ω => (snellContact P 𝓕 Z N ω : WithTop ℕ)) 0 = snellEnvelope P 𝓕 Set.univ Z N 0 := by
    ext ω
    change snellEnvelope P 𝓕 Set.univ Z N (min 0 (snellContact P 𝓕 Z N ω)) ω = _
    simp
  have hN : stoppedProcess (snellEnvelope P 𝓕 Set.univ Z N)
      (fun ω => (snellContact P 𝓕 Z N ω : WithTop ℕ)) N =
        fun ω => Z (snellContact P 𝓕 Z N ω) ω := by
    ext ω
    change snellEnvelope P 𝓕 Set.univ Z N (min N (snellContact P 𝓕 Z N ω)) ω = _
    rw [min_eq_right (snellContact_le N ω)]
    exact snellContact_contact N ω
  have he := hm.setIntegral_eq (i := 0) (j := N) (Nat.zero_le _) (s := univ) MeasurableSet.univ
  rw [h0,hN] at he
  simpa only [Measure.restrict_univ] using he.symm

theorem expected_discrete_payoff_le_snellEnvelope (ha : Adapted 𝓕 Z)
    (hi : ∀ i, Integrable (Z i) P) {N : ℕ} {τ : Ω → ℕ}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ))) (hb : ∀ ω, τ ω ≤ N) :
    (∫ ω, Z (τ ω) ω ∂P) ≤ ∫ ω, snellEnvelope P 𝓕 Set.univ Z N 0 ω ∂P := by
  have hU := snellEnvelope_supermartingale (X := univ) ha hi N
  have hbound : ∀ ω, (τ ω : WithTop ℕ) ≤ (N : WithTop ℕ) := fun ω => by exact_mod_cast hb ω
  have hiZ : Integrable (fun ω => Z (τ ω) ω) P := by
    convert! integrable_stoppedValue ℕ hτ hi hbound using 1
  have hiU : Integrable (fun ω => snellEnvelope P 𝓕 Set.univ Z N (τ ω) ω) P := by
    convert! integrable_stoppedValue ℕ hτ (snellEnvelope_integrable hi N) hbound using 1
  have hle : (∫ ω, Z (τ ω) ω ∂P) ≤ ∫ ω, snellEnvelope P 𝓕 Set.univ Z N (τ ω) ω ∂P := by
    apply integral_mono hiZ hiU
    intro ω
    simpa only [min_eq_left (hb ω)] using snellEnvelope_dominates (P := P) (𝓕 := 𝓕)
        (Z := Z) (N := N) (Or.inl (mem_univ (τ ω))) ω
  have ho := hU.neg.expected_stoppedValue_mono (isStoppingTime_const 𝓕 0) hτ
    (fun ω => bot_le) hbound
  have ho' : (∫ ω, snellEnvelope P 𝓕 Set.univ Z N (τ ω) ω ∂P) ≤
      ∫ ω, snellEnvelope P 𝓕 Set.univ Z N 0 ω ∂P := by
    simp only [stoppedValue,Pi.neg_apply,integral_neg,neg_le_neg_iff] at ho
    convert! ho using 1
  exact hle.trans ho'

theorem snellContact_optimal (ha : Adapted 𝓕 Z)
    (hi : ∀ i, Integrable (Z i) P) {N : ℕ} {τ : Ω → ℕ}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ))) (hb : ∀ ω, τ ω ≤ N) :
    (∫ ω, Z (τ ω) ω ∂P) ≤ ∫ ω, Z (snellContact P 𝓕 Z N ω) ω ∂P := by
  rw [snellContact_expected_payoff ha hi N]
  exact expected_discrete_payoff_le_snellEnvelope ha hi hτ hb

end MathFin.BlackScholes.AmericanPut.Stopping
