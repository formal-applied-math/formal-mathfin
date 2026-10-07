/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.IndepFreezing
public import MathFin.Foundations.PoissonPgf

/-!
# The compound-Poisson aggregate-loss MGF

For i.i.d. claim sizes `Xᵢ` with common moment generating function `M_X(t)`, integrating the MGF
of the `n`-claim sum `∑_{i<n} Xᵢ` against the Poisson(λ) law of `n` gives

  `∫ n, M_{∑_{i<n} Xᵢ}(t) dPoisson(λ) = exp(λ·(M_X(t) − 1))`,

the compound-Poisson aggregate-loss MGF in mixture form. For a claim count `N ∼ Poisson(λ)`
independent of the `Xᵢ` the left side is `𝔼[exp(tS)]` with `S = ∑_{i<N} Xᵢ`
(`compoundPoisson_mgf_of_indepFun`): freezing the count (`Foundations/IndepFreezing.lean`) turns
the expectation over the random count into the mixture.

This composes two genuine theorems rather than positing the algebraic shell
`e^{−λ}·e^{λM} = e^{λ(M−1)}` (`Actuarial/Mortality.compoundPoisson_mgf_identity`):

* the **`n`-claim aggregate MGF** `𝔼[exp(t·∑_{i<n} Xᵢ)] = M_X(t)ⁿ` — the MGF of a sum of
  i.i.d. summands is the `n`-th power of the common MGF (Mathlib's `iIndepFun.mgf_sum`
  factorisation + `IdentDistrib` collapse), and
* the **Poisson probability generating function** `𝔼[xᴺ] = e^{λ(x−1)}`
  (`Foundations/PoissonPgf.integral_pow_poissonMeasure`), evaluated at `x = M_X(t)`.


## Main results

* `compoundPoisson_mgf` — `∫ n, mgf (∑_{i<n} Xᵢ) t ∂Poisson(λ) = exp(λ·(mgf X₀ t − 1))`.
* `compoundPoisson_mgf_of_indepFun` — for a count `N ∼ Poisson(λ)` independent of the claims and
  `t` where the claim MGF is finite, `𝔼[exp(t·∑_{i<N} Xᵢ)] = exp(λ·(M_X(t) − 1))`.
* `integrable_exp_mul_sum_range_of_iid` — the `n`-claim aggregate has a finite MGF at `t`
  wherever the claims do.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The `n`-claim aggregate MGF is the `n`-th power of the common claim MGF.** For i.i.d.
claim sizes `X` (independent, identically distributed), the MGF of the `n`-claim aggregate
`∑_{i<n} Xᵢ` is `M_X(t)ⁿ`. -/
lemma mgf_range_sum_of_iid (t : ℝ) (X : ℕ → Ω → ℝ)
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    mgf (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) μ t = (mgf (X 0) μ t) ^ n := by
  have hu : Measurable (fun x : ℝ ↦ Real.exp (t * x)) := by fun_prop
  have hmgf : ∀ i, mgf (X i) μ t = mgf (X 0) μ t := fun i ↦
    ((hident i).comp hu).integral_eq
  have hsum : (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) = ∑ i ∈ Finset.range n, X i := by
    funext ω; rw [Finset.sum_apply]
  rw [hsum, hindep.mgf_sum hmeas (Finset.range n),
    Finset.prod_congr rfl (fun i _ ↦ hmgf i), Finset.prod_const, Finset.card_range]

/-- **The compound-Poisson aggregate-loss MGF, in mixture form.** For i.i.d. claim sizes `Xᵢ`,
the MGF of the `n`-claim sum integrated against the Poisson(λ) law of `n` is
`exp(λ·(M_X(t) − 1))`, the Poisson PGF evaluated at the common claim MGF. -/
theorem compoundPoisson_mgf (lam : ℝ≥0) (t : ℝ) (X : ℕ → Ω → ℝ)
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∫ n, mgf (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) μ t ∂(poissonMeasure lam)
      = Real.exp ((lam : ℝ) * (mgf (X 0) μ t - 1)) := by
  simp_rw [mgf_range_sum_of_iid t X hindep hmeas hident]
  exact PoissonPgf.integral_pow_poissonMeasure lam (mgf (X 0) μ t)

/-- The partial sums of i.i.d. claims have a finite MGF at `t` wherever the claims do. -/
lemma integrable_exp_mul_sum_range_of_iid (t : ℝ) (X : ℕ → Ω → ℝ) (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hint : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) μ) (n : ℕ) :
    Integrable (fun ω ↦ Real.exp (t * ∑ i ∈ Finset.range n, X i ω)) μ := by
  simpa only [Finset.sum_apply] using hindep.integrable_exp_mul_sum hmeas
    (s := Finset.range n) fun i _ ↦
      ((hident i).comp (measurable_const_mul t).exp).integrable_iff.mpr hint

/-- **The compound-Poisson aggregate-loss MGF.** For a claim count `N ∼ Poisson(λ)` independent of
i.i.d. claim sizes `Xᵢ` whose MGF is finite at `t`, the aggregate loss `S = ∑_{i<N} Xᵢ` has
`𝔼[exp(t·S)] = exp(λ·(M_X(t) − 1))`. Freezing the count
(`integral_comp_prodMk_of_indepFun_of_countable`) reduces it to the mixture form
`compoundPoisson_mgf`. -/
theorem compoundPoisson_mgf_of_indepFun (lam : ℝ≥0) (t : ℝ) {N : Ω → ℕ} (X : ℕ → Ω → ℝ)
    (hN : HasLaw N (poissonMeasure lam) μ) (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hNX : IndepFun N (fun ω i ↦ X i ω) μ)
    (hint : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) μ) :
    mgf (fun ω ↦ ∑ i ∈ Finset.range (N ω), X i ω) μ t
      = Real.exp ((lam : ℝ) * (mgf (X 0) μ t - 1)) := by
  have := hindep.isProbabilityMeasure
  have hgm (n : ℕ) : Measurable fun x : ℕ → ℝ ↦ Real.exp (t * ∑ i ∈ Finset.range n, x i) := by
    fun_prop
  have hint' : Integrable (fun n ↦ mgf (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) μ t) (μ.map N) := by
    simp_rw [hN.map_eq, mgf_range_sum_of_iid t X hindep hmeas hident]
    exact PoissonPgf.integrable_pow_poissonMeasure lam _
  calc mgf (fun ω ↦ ∑ i ∈ Finset.range (N ω), X i ω) μ t
      = ∫ n, mgf (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) μ t ∂(μ.map N) :=
        integral_comp_prodMk_of_indepFun_of_countable
          (g := fun p : ℕ × (ℕ → ℝ) ↦ Real.exp (t * ∑ i ∈ Finset.range p.1, p.2 i)) hNX
          hN.aemeasurable (measurable_pi_lambda _ hmeas).aemeasurable hgm
          (fun _ ↦ (Real.exp_pos _).le)
          (integrable_exp_mul_sum_range_of_iid t X hindep hmeas hident hint) hint'
    _ = Real.exp ((lam : ℝ) * (mgf (X 0) μ t - 1)) := by
        rw [hN.map_eq]
        exact compoundPoisson_mgf lam t X hindep hmeas hident

end MathFin
