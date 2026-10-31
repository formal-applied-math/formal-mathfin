/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# A martingale from set-integral identities, over any index

Mathlib proves `martingale_of_setIntegral_eq_succ` for `ℕ`-indexed processes, where one-step
identities suffice. Over a general (e.g. continuous) index there is no successor, and the
identities are over every pair `i ≤ j`: `martingale_of_setIntegral_eq` is that statement. It is
the characterisation of conditional expectation by set integrals
(`ae_eq_condExp_of_forall_setIntegral_eq`) read off as the martingale property, and the way the
library's continuous-time martingales (the exponential martingales, the stopped price of an
equivalent martingale measure, promoted local martingales) are built.
-/

@[expose] public section

namespace MeasureTheory

variable {Ω ι E : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [Preorder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {𝒢 : Filtration ι m0}
  {f : ι → Ω → E}

/-- **A process is a martingale when it is adapted, integrable, and its set integrals over
`𝒢 i`-measurable sets are constant in time.** -/
theorem martingale_of_setIntegral_eq [IsFiniteMeasure μ] (hadp : StronglyAdapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ ⦃i j⦄, i ≤ j → ∀ s : Set Ω, MeasurableSet[𝒢 i] s →
      ∫ ω in s, f i ω ∂μ = ∫ ω in s, f j ω ∂μ) :
    Martingale f 𝒢 μ :=
  ⟨hadp, fun _ _ hij ↦
    (ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le _) (hint _)
      (fun _ _ _ ↦ (hint _).integrableOn) (fun s hs _ ↦ hf hij s hs)
      (hadp _).aestronglyMeasurable).symm⟩

end MeasureTheory
