/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.JumpDiffusionMixing
public import MathFin.Foundations.PoissonThinning

/-!
# Thinning the jumps of a Merton-type jump-diffusion

`JumpDiffusionHyp Q Λ Z N J` (`BlackScholes/JumpDiffusionMixing.lean`) is a Merton-type
jump-diffusion at a fixed horizon (any i.i.d. jump law; the Gaussian-jump `MertonHyp` is not an
instance as stated): a standard normal diffusion sample `Z`, a `Poisson(Λ)` jump count `N` and i.i.d.
log-jump sizes `J 0, J 1, …`, the count independent of the sizes. Sorting the jumps by a
measurable set `A` of sizes (for instance `A = (0, ∞)`, the up-jumps) is a thinning of the
Poisson count by i.i.d. marks, so `PoissonThinning.thinned_streams_of_iid_marks` applies: the
number of jumps with size in `A` and the number with size in `Aᶜ` are independent Poisson
counts with means `Λ·P(J₀ ∈ A)` and `Λ·P(J₀ ∉ A)`.

## Main results

* `JumpDiffusionHyp.jumpCounts_split`
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {Λ : ℝ≥0} {Z : Ω → ℝ}
  {N : Ω → ℕ} {J : ℕ → Ω → ℝ}

namespace JumpDiffusionHyp

/-- **The jumps of a Merton-type jump-diffusion split into independent Poisson streams.** In the model
`JumpDiffusionHyp Q Λ Z N J` and for a measurable set `A` of jump sizes, with
`p = Q(J₀ ∈ A)`, the number of the `N` jumps whose size lies in `A` is `Poisson(p·Λ)`, the number
whose size lies in `Aᶜ` is `Poisson((1 − p)·Λ)`, and the two counts are independent. -/
theorem jumpCounts_split (h : JumpDiffusionHyp Q Λ Z N J) {A : Set ℝ} (hA : MeasurableSet A) :
    Q.map (fun ω ↦ PoissonThinning.marksIn J A (N ω) ω)
        = poissonMeasure ((Q (J 0 ⁻¹' A)).toNNReal * Λ) ∧
      Q.map (fun ω ↦ PoissonThinning.marksIn J Aᶜ (N ω) ω)
        = poissonMeasure ((1 - (Q (J 0 ⁻¹' A)).toNNReal) * Λ) ∧
      IndepFun (fun ω ↦ PoissonThinning.marksIn J A (N ω) ω)
        (fun ω ↦ PoissonThinning.marksIn J Aᶜ (N ω) ω) Q :=
  have := h.J_indep.isProbabilityMeasure
  PoissonThinning.thinned_streams_of_iid_marks hA h.N_law h.J_meas h.J_indep h.J_ident
    h.N_indep_J

end JumpDiffusionHyp

end MathFin
