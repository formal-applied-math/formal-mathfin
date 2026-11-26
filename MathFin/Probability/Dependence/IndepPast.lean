/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

/-!
# Independence from the past gives independent increments

A process adapted to a filtration whose increments are each independent of the past has
independent increments in Mathlib's sense. The step underneath is a statement about sequences:
if `Dₖ` is measurable for `𝒢ₖ₊₁` and independent of `𝒢ₖ`, along a monotone family `𝒢`, then
`(Dₖ)` is an independent family. On a finite subfamily, the largest index is independent of the
others, which are all measurable for its σ-algebra, so the product formula peels it off.

The Girsanov `Q`-Brownian motion (`Brownian/ExpMartingaleQBrownian.lean`) and the jump-diffusion
process (`Models/Jumps/JumpDiffusionProcess.lean`) both get `HasIndepIncrements` this way.

## Main results

* `MathFin.iIndepFun_of_indep_past`: sequential independence from a monotone family of
  σ-algebras gives joint independence.
* `MathFin.hasIndepIncrements_of_indep_past`: adapted, with each increment independent of the
  past, gives `HasIndepIncrements`.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  §2.1 (independent increments relative to a filtration)

## Tags

independent increments, independence of the past, filtration, MSC 60G51
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Sequential independence gives joint independence.** If `𝒢` is monotone, `D k` is
`𝒢 (k + 1)`-measurable and `D k` is independent of `𝒢 k`, then the `D k` are jointly independent:
on a finite index set, peel off the largest index, which is independent of the intersection of
the others (all `𝒢`-measurable at that index). -/
theorem iIndepFun_of_indep_past {β : Type*} [MeasurableSpace β] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : ℕ → Ω → β} {𝒢 : ℕ → MeasurableSpace Ω} (h𝒢 : Monotone 𝒢)
    (hD : ∀ k, Measurable[𝒢 (k + 1)] (D k))
    (hind : ∀ k, Indep (MeasurableSpace.comap (D k) inferInstance) (𝒢 k) μ) : iIndepFun D μ := by
  rw [iIndepFun_iff_iIndep, iIndep_iff]
  intro S
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hlt ih =>
    intro f hf
    have ha : a ∉ S := fun h ↦ lt_irrefl _ (hlt a h)
    have hS : MeasurableSet[𝒢 a] (⋂ i ∈ S, f i) := by
      letI : MeasurableSpace Ω := 𝒢 a
      exact Finset.measurableSet_biInter S fun i hi ↦
        h𝒢 (Nat.succ_le_of_lt (hlt i hi)) _
          ((hD i).comap_le _ (hf i (Finset.mem_insert_of_mem hi)))
    rw [Finset.set_biInter_insert, Finset.prod_insert ha,
      ← ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]
    exact (Indep_iff _ _ μ).1 (hind a) _ _ (hf a (Finset.mem_insert_self _ _)) hS

/-- **Adapted, with increments independent of the past, gives independent increments.** If `X` is
adapted to a monotone family `𝒢` of σ-algebras and each increment `X t − X s` (`s ≤ t`) is
independent of `𝒢 s`, then `X` has independent increments in Mathlib's sense
(`HasIndepIncrements`): along a monotone sequence of times, apply `iIndepFun_of_indep_past`. -/
theorem hasIndepIncrements_of_indep_past {ι E : Type*} [Preorder ι] [Sub E] [MeasurableSpace E]
    [MeasurableSub₂ E] {X : ι → Ω → E} {P : Measure Ω} [IsProbabilityMeasure P]
    (𝒢 : ι → MeasurableSpace Ω) (h𝒢 : Monotone 𝒢) (hX : ∀ t, Measurable[𝒢 t] (X t))
    (hind : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) (𝒢 s) P) :
    HasIndepIncrements X P :=
  HasIndepIncrements.of_nat fun τ hτ _ ↦
    iIndepFun_of_indep_past (𝒢 := fun k ↦ 𝒢 (τ k)) (fun _ _ hij ↦ h𝒢 (hτ hij))
      (fun k ↦ (hX (τ (k + 1))).sub ((hX (τ k)).mono (h𝒢 (hτ (Nat.le_succ k))) le_rfl))
      fun k ↦ hind _ _ (hτ (Nat.le_succ k))

end MathFin
