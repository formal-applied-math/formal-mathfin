/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import MathFin.Insurance.Lundberg
public import MathFin.Probability.Laws.ExponentialMGF
public import Mathlib.Probability.Independence.Integration

/-!
# The Cramér–Lundberg adjustment equation and the embedded random walk

In the Cramér–Lundberg model an insurer collects premium at rate `c`, and claims of size `Xₖ`
arrive after waiting times `Tₖ ∼ Exp(λ)`. The surplus can only fall below zero at a claim, so
ruin is the ruin of the embedded random walk of the surplus just after each claim,
`Uₙ = u + ∑_{k<n} (c Tₖ − Xₖ)`. This file proves two things about that walk.

* `mgf_gap_sub_claim`: for a waiting time independent of the claim,
  `𝔼[e^{−R(cT − X)}] = 𝔼[e^{−R c T}] · 𝔼[e^{R X}]`.
* `isLundbergAdjustmentCoefficient_iff`: when `T ∼ Exp(λ)`, so that
  `𝔼[e^{−R c T}] = λ/(λ + R c)` (`HasLaw.mgf_neg_expMeasure`), the adjustment equation of the
  walk, `𝔼[e^{−R(cT − X)}] = 1`, is the classical Cramér–Lundberg equation
  `λ(𝔼[e^{R X}] − 1) − c R = 0` (`IsLundbergAdjustmentCoefficient`).

Composed with `lundberg_inequality` they give `cramerLundberg_embedded_ruin_le`: the embedded walk
is ruined with probability at most `e^{−R u}` at a root `R > 0` of the Cramér–Lundberg equation.

## Scope

Only the first waiting time `T₀` is assumed to have the law `Exp(λ)`; the `Tₖ` enter through the
i.i.d. hypothesis on the gaps `c Tₖ − Xₖ`. The Poisson process whose arrival times the `Tₖ` are
is not constructed: only the first interarrival time is known to be exponential
(`Probability/Jumps/PoissonInterarrival.lean`), the i.i.d. sequence needs the strong Markov
property. The statement is about the embedded walk, that is, ruin at claim
instants. The identification of the walk's ruin probability with that of the continuous-time
surplus process `u + c t − ∑_{i ≤ N(t)} Xᵢ`, which is a pathwise comparison of the two processes
at claim times, is not formalised.

## Main definitions

* `IsLundbergAdjustmentCoefficient`: the Cramér–Lundberg equation `λ(M(R) − 1) − c R = 0`.

## Main results

* `lundberg_zero_at_zero`: `R = 0` always solves it when `M 0 = 1`.
* `mgf_gap_sub_claim`: the exponential moment of the premium-minus-claim `c T − X`.
* `isLundbergAdjustmentCoefficient_iff`: adjustment coefficient of the walk, equivalent to the
  Cramér–Lundberg equation.
* `cramerLundberg_embedded_ruin_le`: `ℙ(∃ n, u + ∑_{k<n} (c Tₖ − Xₖ) < 0) ≤ e^{−R u}`.

## References

* [S. Asmussen and H. Albrecher, *Ruin Probabilities*][AsmussenAlbrecher2010], the
  Cramér–Lundberg model and the embedded random walk

## Tags

Cramér–Lundberg model, ruin probability, adjustment coefficient, embedded random walk,
exponential interarrival, collective risk theory, MSC 91G05, MSC 60G50, JEL G22
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

/-- **Lundberg adjustment-coefficient equation**: `λ · (M(R) − 1) − c · R = 0`, for the premium
rate `c`, the claim-arrival intensity `λ` and the moment generating function `M` of the claim
size. -/
def IsLundbergAdjustmentCoefficient (lam c R : ℝ) (M : ℝ → ℝ) : Prop :=
  lam * (M R - 1) - c * R = 0

/-- **Trivial root at zero**: `R = 0` always satisfies the adjustment equation
when `M 0 = 1` (which holds for any MGF). -/
theorem lundberg_zero_at_zero (lam c : ℝ) (M : ℝ → ℝ) (hM0 : M 0 = 1) :
    IsLundbergAdjustmentCoefficient lam c 0 M := by
  unfold IsLundbergAdjustmentCoefficient
  rw [hM0]
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The exponential moment of premium minus claim.** For a waiting time `T` independent of the
claim `X`, `𝔼[e^{−R(cT − X)}] = 𝔼[e^{−R c T}] · 𝔼[e^{R X}]`: the factor `e^{−R c T} · e^{R X}`
splits over independent variables. -/
theorem mgf_gap_sub_claim {T X : Ω → ℝ} (hT : Measurable T) (hX : Measurable X)
    (hind : IndepFun T X P) (c R : ℝ) :
    mgf (fun ω ↦ c * T ω - X ω) P (-R) = mgf T P (-(R * c)) * mgf X P R := by
  unfold mgf
  have hφ : Measurable fun t : ℝ ↦ Real.exp (-(R * c) * t) := (measurable_const_mul _).exp
  have hψ : Measurable fun x : ℝ ↦ Real.exp (R * x) := (measurable_const_mul _).exp
  have h := (hind.comp hφ hψ).integral_mul_eq_mul_integral (hφ.comp hT).aestronglyMeasurable
    (hψ.comp hX).aestronglyMeasurable
  refine Eq.trans ?_ h
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [← Real.exp_add]
  congr 1
  ring

/-- **The adjustment equation of the embedded walk is the Cramér–Lundberg equation.** If the
waiting time `T ∼ Exp(λ)` is independent of the claim `X`, then `𝔼[e^{−R(cT − X)}] = 1`
holds exactly when
`λ(𝔼[e^{R X}] − 1) − c R = 0`. -/
theorem isLundbergAdjustmentCoefficient_iff {T X : Ω → ℝ} {lam c R : ℝ} (hlam : 0 < lam)
    (hc : 0 < c) (hR : 0 < R) (hTm : Measurable T) (hXm : Measurable X) (hind : IndepFun T X P)
    (hT : HasLaw T (expMeasure lam) P) :
    mgf (fun ω ↦ c * T ω - X ω) P (-R) = 1 ↔
      IsLundbergAdjustmentCoefficient lam c R fun r ↦ mgf X P r := by
  have hpos : lam + R * c ≠ 0 := by positivity
  rw [mgf_gap_sub_claim hTm hXm hind, hT.mgf_neg_expMeasure hlam (by nlinarith [mul_pos hR hc]),
    div_mul_eq_mul_div, div_eq_one_iff_eq hpos]
  show _ ↔ lam * (mgf X P R - 1) - c * R = 0
  constructor <;> intro h <;> linarith

variable [IsProbabilityMeasure P]

/-- **Lundberg's inequality for the embedded Cramér–Lundberg walk.** Let `Tₖ` be waiting times and
`Xₖ` claims such that the gaps `c Tₖ − Xₖ` are i.i.d., `T₀ ∼ Exp(λ)` is independent
of `X₀`. If `R > 0` solves the Cramér–Lundberg equation
`λ(𝔼[e^{R X₀}] − 1) − c R = 0`, then the probability that the surplus after some claim,
`u + ∑_{k<n} (c Tₖ − Xₖ)`, is negative is at most `e^{−R u}`. -/
theorem cramerLundberg_embedded_ruin_le {T X : ℕ → Ω → ℝ} {lam c R : ℝ} (u : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hR : 0 < R) (hTm : ∀ k, Measurable (T k))
    (hXm : ∀ k, Measurable (X k)) (hindep : iIndepFun (fun k ω ↦ c * T k ω - X k ω) P)
    (hident : ∀ k, IdentDistrib (fun ω ↦ c * T k ω - X k ω) (fun ω ↦ c * T 0 ω - X 0 ω) P P)
    (hpair : IndepFun (T 0) (X 0) P) (hT : HasLaw (T 0) (expMeasure lam) P)
    (hadj : IsLundbergAdjustmentCoefficient lam c R fun r ↦ mgf (X 0) P r) :
    P {ω | ∃ n, surplus u (fun k ω ↦ c * T k ω - X k ω) n ω < 0}
      ≤ ENNReal.ofReal (Real.exp (-R * u)) :=
  lundberg_inequality u (fun k ↦ ((hTm k).const_mul c).sub (hXm k)) hindep hident hR
    ((isLundbergAdjustmentCoefficient_iff hlam hc hR (hTm 0) (hXm 0) hpair hT).2 hadj)

end MathFin
