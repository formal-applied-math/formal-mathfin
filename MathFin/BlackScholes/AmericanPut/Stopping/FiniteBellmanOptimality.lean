/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.DiscreteContactMartingale

/-! # First-contact attainment of the finite conditional-expectation Bellman value 
## Result

Public entry points include `finiteBellmanContact`, `finiteBellmanContact_le`,
`finiteBellmanContact_stopping`, `finiteBellmanContact_contact`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ}

/-- The first index in `[0,N]` at which the Bellman value meets the reward, that is at which
`finiteBellman P 𝓕 Z N i-Z (min i N)` vanishes. -/
noncomputable def finiteBellmanContact (P : Measure Ω) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›)
    (Z : ℕ → Ω → ℝ) (N : ℕ) : Ω → ℕ :=
  hittingBtwn (fun i ω => finiteBellman P 𝓕 Z N i ω-Z (min i N) ω) {0} 0 N

theorem finiteBellmanContact_le (N : ℕ) (ω : Ω) : finiteBellmanContact P 𝓕 Z N ω ≤ N :=
  hittingBtwn_le ω

theorem finiteBellmanContact_stopping (ha : Adapted 𝓕 Z) (N : ℕ) :
    IsStoppingTime 𝓕 (fun ω => (finiteBellmanContact P 𝓕 Z N ω : WithTop ℕ)) := by
  apply Adapted.isStoppingTime_hittingBtwn ?_ (measurableSet_singleton 0)
  intro i
  exact ((finiteBellman_stronglyAdapted ha N i).measurable).sub
    ((ha (min i N)).mono (𝓕.mono (min_le_left _ _)) le_rfl)

theorem finiteBellmanContact_contact (N : ℕ) (ω : Ω) :
    finiteBellman P 𝓕 Z N (finiteBellmanContact P 𝓕 Z N ω) ω =
      Z (finiteBellmanContact P 𝓕 Z N ω) ω := by
  have he : ∃ j ∈ Icc 0 N, finiteBellman P 𝓕 Z N j ω-Z (min j N) ω ∈ ({0} : Set ℝ) := by
    refine ⟨N,⟨Nat.zero_le _,le_rfl⟩,?_⟩
    simp [finiteBellman_after_horizon le_rfl]
  have hh := hittingBtwn_mem_set
    (u := fun i ω => finiteBellman P 𝓕 Z N i ω-Z (min i N) ω) (ω := ω) he
  have hbound := finiteBellmanContact_le (P := P) (𝓕 := 𝓕) (Z := Z) N ω
  change finiteBellman P 𝓕 Z N (finiteBellmanContact P 𝓕 Z N ω) ω-
    Z (min (finiteBellmanContact P 𝓕 Z N ω) N) ω = 0 at hh
  rw [min_eq_left hbound] at hh
  exact sub_eq_zero.mp hh

theorem finiteBellmanContact_before (N i : ℕ) (ω : Ω)
    (ht : i < finiteBellmanContact P 𝓕 Z N ω) :
    P[finiteBellman P 𝓕 Z N (i+1) | 𝓕 i] ω = finiteBellman P 𝓕 Z N i ω := by
  have hiN : i < N := ht.trans_le (finiteBellmanContact_le N ω)
  have hn := notMem_of_lt_hittingBtwn (u := fun i ω => finiteBellman P 𝓕 Z N i ω-Z (min i N) ω)
    (s := ({0} : Set ℝ)) ht (Nat.zero_le i)
  have hne : finiteBellman P 𝓕 Z N i ω ≠ Z i ω := by
    simpa only [mem_singleton_iff,min_eq_left hiN.le,sub_eq_zero] using hn
  have hv : Z i ω < finiteBellman P 𝓕 Z N i ω := lt_of_le_of_ne
    (by simpa only [min_eq_left hiN.le] using finiteBellman_dominates (P := P) (𝓕 := 𝓕)
        (Z := Z) N i ω)
    hne.symm
  have he := congrFun (finiteBellman_recursion (P := P) (𝓕 := 𝓕) (Z := Z) hiN) ω
  rw [he] at hv
  have hc := (lt_max_iff.mp hv).resolve_left (lt_irrefl _)
  exact (he.trans (max_eq_right hc.le)).symm

variable [IsProbabilityMeasure P]

theorem finiteBellmanContact_martingale (ha : Adapted 𝓕 Z)
    (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    Martingale (stoppedProcess (finiteBellman P 𝓕 Z N)
      (fun ω => (finiteBellmanContact P 𝓕 Z N ω : WithTop ℕ))) 𝓕 P :=
  discrete_stopped_martingale_of_before (finiteBellman_stronglyAdapted ha N)
    (finiteBellman_integrable hi N) (finiteBellmanContact_stopping ha N)
    (finiteBellmanContact_before N)

theorem finiteBellmanContact_expected_payoff (ha : Adapted 𝓕 Z)
    (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    (∫ ω, Z (finiteBellmanContact P 𝓕 Z N ω) ω ∂P) =
      ∫ ω, finiteBellman P 𝓕 Z N 0 ω ∂P := by
  have hm := finiteBellmanContact_martingale ha hi N
  have h0 : stoppedProcess (finiteBellman P 𝓕 Z N)
      (fun ω => (finiteBellmanContact P 𝓕 Z N ω : WithTop ℕ)) 0 = finiteBellman P 𝓕 Z N 0 := by
    ext ω
    change finiteBellman P 𝓕 Z N (min 0 (finiteBellmanContact P 𝓕 Z N ω)) ω = _
    simp
  have hN : stoppedProcess (finiteBellman P 𝓕 Z N)
      (fun ω => (finiteBellmanContact P 𝓕 Z N ω : WithTop ℕ)) N =
        fun ω => Z (finiteBellmanContact P 𝓕 Z N ω) ω := by
    ext ω
    change finiteBellman P 𝓕 Z N (min N (finiteBellmanContact P 𝓕 Z N ω)) ω = _
    rw [min_eq_right (finiteBellmanContact_le N ω)]
    exact finiteBellmanContact_contact N ω
  have he := hm.setIntegral_eq (i := 0) (j := N) (Nat.zero_le _) (s := univ) MeasurableSet.univ
  rw [h0,hN] at he
  simpa only [Measure.restrict_univ] using he.symm

theorem expected_discrete_payoff_le_bellman (ha : Adapted 𝓕 Z)
    (hi : ∀ i, Integrable (Z i) P) {N : ℕ} {τ : Ω → ℕ}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ))) (hb : ∀ ω, τ ω ≤ N) :
    (∫ ω, Z (τ ω) ω ∂P) ≤ ∫ ω, finiteBellman P 𝓕 Z N 0 ω ∂P := by
  have hU := finiteBellman_supermartingale ha hi N
  have hbound : ∀ ω, (τ ω : WithTop ℕ) ≤ (N : WithTop ℕ) := fun ω => by exact_mod_cast hb ω
  have hiZ : Integrable (fun ω => Z (τ ω) ω) P := by
    convert! integrable_stoppedValue ℕ hτ hi hbound using 1
  have hiU : Integrable (fun ω => finiteBellman P 𝓕 Z N (τ ω) ω) P := by
    convert! integrable_stoppedValue ℕ hτ (finiteBellman_integrable hi N) hbound using 1
  have hle : (∫ ω, Z (τ ω) ω ∂P) ≤ ∫ ω, finiteBellman P 𝓕 Z N (τ ω) ω ∂P := by
    apply integral_mono hiZ hiU
    intro ω
    simpa only [min_eq_left (hb ω)] using finiteBellman_dominates (P := P) (𝓕 := 𝓕)
        (Z := Z) N (τ ω) ω
  have ho := hU.neg.expected_stoppedValue_mono (isStoppingTime_const 𝓕 0) hτ
    (fun ω => bot_le) hbound
  have ho' : (∫ ω, finiteBellman P 𝓕 Z N (τ ω) ω ∂P) ≤
      ∫ ω, finiteBellman P 𝓕 Z N 0 ω ∂P := by
    simp only [stoppedValue,Pi.neg_apply,integral_neg,neg_le_neg_iff] at ho
    convert! ho using 1
  exact hle.trans ho'

theorem finiteBellmanContact_optimal (ha : Adapted 𝓕 Z)
    (hi : ∀ i, Integrable (Z i) P) {N : ℕ} {τ : Ω → ℕ}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ))) (hb : ∀ ω, τ ω ≤ N) :
    (∫ ω, Z (τ ω) ω ∂P) ≤ ∫ ω, Z (finiteBellmanContact P 𝓕 Z N ω) ω ∂P := by
  rw [finiteBellmanContact_expected_payoff ha hi N]
  exact expected_discrete_payoff_le_bellman ha hi hτ hb

end MathFin.BlackScholes.AmericanPut.Stopping
