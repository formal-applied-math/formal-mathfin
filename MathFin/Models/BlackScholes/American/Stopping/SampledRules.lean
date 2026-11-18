/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Models.BlackScholes.American.Stopping.GridSampling
public import MathFin.Pricing.ContinuousMarket
public import MathFin.Probability.Martingales.StoppingRule

/-!
# Discrete rules sampled at arbitrary deterministic increasing times

## Main definitions

* `StoppingRule.toSampledRule`: a discrete rule `η` for `ContinuousMarket.sampledFiltration 𝓕 hs`
  read back in continuous time as `ω ↦ s (η.time ω)`, with horizon `s N`.

## Tags

sampled stopping rule, discrete rules, deterministic times, increasing times, MSC 60G40, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A discrete rule `η` for `ContinuousMarket.sampledFiltration 𝓕 hs` read back in continuous
time as `ω ↦ s (η.time ω)`, with horizon `s N`. -/
def _root_.MathFin.StoppingRule.toSampledRule {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {s : ℕ → ℝ≥0} {hs : Monotone s} {N : ℕ}
    (η : StoppingRule (ContinuousMarket.sampledFiltration 𝓕 hs) N) : StoppingRule 𝓕 (s N) where
  time := fun ω => s (η.time ω)
  stopping := by
    intro t
    have he : {ω | (s (η.time ω) : WithTop ℝ≥0) ≤ t} =
        ⋃ i : ℕ, if s i ≤ t then {ω | (η.time ω : WithTop ℕ) ≤ i} else ∅ := by
      ext ω
      simp only [mem_ofPred_eq,WithTop.coe_le_coe,mem_iUnion]
      constructor
      · intro hω
        refine ⟨η.time ω,?_⟩
        simp [hω]
      · rintro ⟨i,hi⟩
        split_ifs at hi with hit
        · exact (hs (by simpa using hi)).trans hit
        · exact False.elim (notMem_empty ω hi)
    rw [he]
    apply MeasurableSet.iUnion
    intro i
    split_ifs with hit
    · exact 𝓕.mono hit _ (η.stopping i)
    · exact @MeasurableSet.empty Ω (𝓕 t)
  le_horizon := fun ω => hs (η.le_horizon ω)

end MathFin.BlackScholes.AmericanPut.Stopping

namespace MathFin

open MeasureTheory
open scoped NNReal

/-- Payoff-preserving bijection between physical and index stopping rules on finite schedules. -/
theorem exists_bijective_sampledRules {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0) (m : ℕ)
    (e : Fin (m + 1) → ℝ≥0) (he : StrictMono e) (heT : e (Fin.last m) = T)
    (s : ℕ → ℝ≥0) (hs : ∀ n, s n = e ⟨min n m, by omega⟩) :
    ∃ hsmono : Monotone s,
    ∃ (toIndex : {θ // θ ∈ StoppingRule.valuedIn 𝓕 T (Set.range e)} →
        StoppingRule (ContinuousMarket.sampledFiltration 𝓕 hsmono) m)
      (toPhysical : StoppingRule (ContinuousMarket.sampledFiltration 𝓕 hsmono) m →
        {θ // θ ∈ StoppingRule.valuedIn 𝓕 T (Set.range e)}),
      Function.LeftInverse toPhysical toIndex ∧ Function.RightInverse toPhysical toIndex
      ∧ (∀ (θ : {θ // θ ∈ StoppingRule.valuedIn 𝓕 T (Set.range e)}) (ω : Ω),
          s ((toIndex θ).time ω) = θ.val.time ω)
      ∧ (∀ (η : StoppingRule (ContinuousMarket.sampledFiltration 𝓕 hsmono) m) (ω : Ω),
          (toPhysical η).val.time ω = s (η.time ω)) := by
  have hsmono : Monotone s := by
    intro a b hab
    rw [hs a, hs b]
    apply he.monotone
    rw [Fin.le_def]
    change min a m ≤ min b m
    exact le_min (le_trans (min_le_left _ _) hab) (min_le_right _ _)
  have hsm : s m = T := by
    rw [hs m]
    refine Eq.trans (congrArg e ?_) heT
    apply Fin.ext
    change min m m = (Fin.last m).val
    rw [Fin.val_last]
    exact min_eq_left le_rfl
  subst hsm
  have hex (θ : {θ // θ ∈ StoppingRule.valuedIn 𝓕 (s m) (Set.range e)}) (ω : Ω) :
      ∃ k : Fin (m + 1), e k = θ.val.time ω :=
    θ.property ω
  choose invFn hinvFn using hex
  have key (θ : {θ // θ ∈ StoppingRule.valuedIn 𝓕 (s m) (Set.range e)}) (ω : Ω) (n : ℕ) :
      (invFn θ ω).val ≤ n ↔ θ.val.time ω ≤ s n := by
    rw [hs n, ← hinvFn θ ω, he.le_iff_le, Fin.le_def]
    change (invFn θ ω).val ≤ n ↔ (invFn θ ω).val ≤ min n m
    constructor
    · intro h
      exact le_min h (Nat.le_of_lt_succ (invFn θ ω).isLt)
    · intro h
      exact le_trans h (min_le_left _ _)
  have hscomp (θ : {θ // θ ∈ StoppingRule.valuedIn 𝓕 (s m) (Set.range e)}) (ω : Ω) :
      s ((invFn θ ω).val) = θ.val.time ω := by
    rw [hs ((invFn θ ω).val)]
    refine Eq.trans (congrArg e ?_) (hinvFn θ ω)
    apply Fin.ext
    change min (invFn θ ω).val m = (invFn θ ω).val
    exact min_eq_left (Nat.le_of_lt_succ (invFn θ ω).isLt)
  have hmem (η : StoppingRule (ContinuousMarket.sampledFiltration 𝓕 hsmono) m) :
      η.toSampledRule ∈ StoppingRule.valuedIn 𝓕 (s m) (Set.range e) := by
    change ∀ ω, (η.toSampledRule).time ω ∈ Set.range e
    intro ω
    change s (η.time ω) ∈ Set.range e
    rw [hs]
    exact Set.mem_range_self _
  have rule_ext {ι : Type} [LinearOrder ι] {F : Filtration ι ‹MeasurableSpace Ω›} {U : ι}
      {a b : StoppingRule F U} (h : ∀ ω, a.time ω = b.time ω) : a = b := by
    obtain ⟨t1, _, _⟩ := a
    obtain ⟨t2, _, _⟩ := b
    have ht : t1 = t2 := funext h
    subst ht
    rfl
  refine ⟨hsmono, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ
    refine { time := fun ω => (invFn θ ω).val, stopping := ?_, le_horizon := ?_ }
    · exact BlackScholes.AmericanPut.Stopping.isStoppingTime_sampledFiltration hsmono θ.val
        (i := fun ω => (invFn θ ω).val) (key θ)
    · intro ω
      exact Nat.le_of_lt_succ (invFn θ ω).isLt
  · intro η
    exact ⟨η.toSampledRule, hmem η⟩
  · intro θ
    apply Subtype.ext
    dsimp only
    apply rule_ext
    intro ω
    exact hscomp θ ω
  · intro η
    dsimp only
    apply rule_ext
    intro ω
    change (invFn ⟨η.toSampledRule, hmem η⟩ ω).val = η.time ω
    have hspec : e (invFn ⟨η.toSampledRule, hmem η⟩ ω) =
        s (η.time ω) := by
      have h1 := hinvFn ⟨η.toSampledRule, hmem η⟩ ω
      have h2 : (η.toSampledRule).time ω = s (η.time ω) := rfl
      rw [h1]
      exact h2
    have hinj : invFn ⟨η.toSampledRule, hmem η⟩ ω =
        (⟨min (η.time ω) m, by omega⟩ : Fin (m + 1)) := by
      apply he.injective
      rw [hspec, hs]
    have hval : (invFn ⟨η.toSampledRule, hmem η⟩ ω).val =
        η.time ω := by
      rw [hinj]
      change min (η.time ω) m = η.time ω
      exact min_eq_left (η.le_horizon ω)
    exact hval
  · intro θ ω
    change s ((invFn θ ω).val) = θ.val.time ω
    exact hscomp θ ω
  · intro η ω
    rfl

end MathFin
