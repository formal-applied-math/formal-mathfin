/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
import MathFin

/-!
# Finite sampled-rules tests

Tests for `MathFin.exists_bijective_sampledRules`: the single-date case and a
three-date nonuniform schedule with a skipped intermediate date.
-/

open MeasureTheory
open scoped NNReal

namespace MathFinTest.FiniteSampledRules

/-- Constant filtration on `Unit` used by the tests. -/
def constFiltration : Filtration ℝ≥0 (⊤ : MeasurableSpace Unit) where
  seq := fun _ => ⊤
  mono' := fun _ _ _ => le_rfl
  le' := fun _ => le_rfl

/-- Single-date exercise schedule. -/
def ex0 : Fin (0 + 1) → ℝ≥0 := fun _ => 5

/-- Constant extension of the single-date schedule. -/
def sched0 : ℕ → ℝ≥0 := fun n => ex0 ⟨min n 0, by omega⟩

/-- Three-date nonuniform exercise schedule. -/
def ex3 : Fin (2 + 1) → ℝ≥0 := fun k => ((k.val + min k.val 1 : ℕ) : ℝ≥0)

/-- Constant extension of the three-date schedule. -/
def sched3 : ℕ → ℝ≥0 := fun n => ex3 ⟨min n 2, by omega⟩

example : sched0 7 = 5 := rfl

example : ex3 ⟨0, by omega⟩ = 0 := by
  change ((((0 + min 0 1 : ℕ))) : ℝ≥0) = 0
  have h : min 0 1 = 0 := by decide
  rw [h]
  norm_num

example : ex3 ⟨1, by omega⟩ = 2 := by
  change ((((1 + min 1 1 : ℕ))) : ℝ≥0) = 2
  have h : min 1 1 = 1 := by decide
  rw [h]
  norm_num

example : ex3 ⟨2, by omega⟩ = 3 := by
  change ((((2 + min 2 1 : ℕ))) : ℝ≥0) = 3
  have h : min 2 1 = 1 := by decide
  rw [h]
  norm_num

example : sched3 1 = 2 := by
  change ((((min 1 2 + min (min 1 2) 1 : ℕ))) : ℝ≥0) = 2
  have h1 : min 1 2 = 1 := by decide
  have h2 : min 1 1 = 1 := by decide
  rw [h1, h2]
  norm_num

example : sched3 7 = 3 := by
  change ((((min 7 2 + min (min 7 2) 1 : ℕ))) : ℝ≥0) = 3
  have h1 : min 7 2 = 2 := by decide
  have h2 : min 2 1 = 1 := by decide
  rw [h1, h2]
  norm_num

example : True := by
  have he : StrictMono ex0 := by
    intro a b hab
    have ha : a.val = 0 := by
      have h := a.isLt
      omega
    have hb : b.val = 0 := by
      have h := b.isLt
      omega
    have hab_eq : a = b := Fin.ext (by rw [ha, hb])
    rw [hab_eq] at hab
    exact absurd hab (lt_irrefl b)
  have heT : ex0 (Fin.last 0) = 5 := rfl
  have hs : ∀ n, sched0 n = ex0 ⟨min n 0, by omega⟩ := fun n => rfl
  obtain ⟨hsmono, toIndex, toPhysical, _, _, hcorr₁, hcorr₂⟩ :=
    MathFin.exists_bijective_sampledRules constFiltration 5 0 ex0 he heT sched0 hs
  let θ : MathFin.StoppingRule constFiltration 5 :=
    { time := fun _ => 5, stopping := MeasureTheory.isStoppingTime_const _ _,
      le_horizon := fun _ => le_rfl }
  have hθ : θ ∈ MathFin.StoppingRule.valuedIn constFiltration 5 (Set.range ex0) := by
    change ∀ ω, θ.time ω ∈ Set.range ex0
    intro ω
    exact ⟨⟨0, by omega⟩, rfl⟩
  have htime₁ : sched0 ((toIndex ⟨θ, hθ⟩).time ()) = 5 := hcorr₁ ⟨θ, hθ⟩ ()
  let η : MathFin.StoppingRule
      (MathFin.ContinuousMarket.sampledFiltration constFiltration hsmono) 0 :=
    { time := fun _ => 0, stopping := MeasureTheory.isStoppingTime_const _ _,
      le_horizon := fun _ => le_rfl }
  have htime₂ : (toPhysical η).val.time () = sched0 0 := hcorr₂ η ()
  trivial

example : True := by
  have he : StrictMono ex3 := by
    intro a b hab
    have h' : a.val < b.val := Fin.lt_def.mp hab
    have hlt : a.val + min a.val 1 < b.val + min b.val 1 := by omega
    change ((((a.val + min a.val 1 : ℕ))) : ℝ≥0)
      < ((((b.val + min b.val 1 : ℕ))) : ℝ≥0)
    exact_mod_cast hlt
  have heT : ex3 (Fin.last 2) = 3 := by
    change ((((Fin.last 2).val + min (Fin.last 2).val 1 : ℕ)) : ℝ≥0) = 3
    rw [Fin.val_last]
    have hm : min 2 1 = 1 := by decide
    rw [hm]
    norm_num
  have hs : ∀ n, sched3 n = ex3 ⟨min n 2, by omega⟩ := fun n => rfl
  obtain ⟨hsmono, toIndex, toPhysical, _, _, hcorr₁, hcorr₂⟩ :=
    MathFin.exists_bijective_sampledRules constFiltration 3 2 ex3 he heT sched3 hs
  let θ : MathFin.StoppingRule constFiltration 3 :=
    { time := fun _ => ex3 ⟨1, by omega⟩,
      stopping := MeasureTheory.isStoppingTime_const _ _,
      le_horizon := fun _ => by
        change ((((1 + min 1 1 : ℕ))) : ℝ≥0) ≤ 3
        have hm : min 1 1 = 1 := by decide
        rw [hm]
        norm_num }
  have hθ : θ ∈ MathFin.StoppingRule.valuedIn constFiltration 3 (Set.range ex3) := by
    change ∀ ω, θ.time ω ∈ Set.range ex3
    intro ω
    exact ⟨⟨1, by omega⟩, rfl⟩
  have htime₁ : sched3 ((toIndex ⟨θ, hθ⟩).time ()) = ex3 ⟨1, by omega⟩ :=
    hcorr₁ ⟨θ, hθ⟩ ()
  let η : MathFin.StoppingRule
      (MathFin.ContinuousMarket.sampledFiltration constFiltration hsmono) 2 :=
    { time := fun _ => 2, stopping := MeasureTheory.isStoppingTime_const _ _,
      le_horizon := fun _ => le_rfl }
  have hskip : (toPhysical η).val.time () = 3 := by
    have h := hcorr₂ η ()
    rw [h]
    change sched3 2 = 3
    change ((((min 2 2 + min (min 2 2) 1 : ℕ))) : ℝ≥0) = 3
    have h1 : min 2 2 = 2 := by decide
    have h2 : min 2 1 = 1 := by decide
    rw [h1, h2]
    norm_num
  trivial

end MathFinTest.FiniteSampledRules
