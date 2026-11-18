/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import MathFin.Probability.Laws.FiniteWeights
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Finite-mixture credibility covariance identity

In a finite latent-iid mixture, the covariance of the conditional-mean
function with the sample mean equals the variance of the conditional mean.

## Main definitions

* `MathFin.mixtureLaw`: joint law on `Θ × (Fin n → Ξ)` with weight
  `p θ * ∏ i, w θ (x i)`; observations are conditionally iid given `θ`.
* `MathFin.condMean`: conditional mean `∑ ξ, w ξ * v ξ`.

## Main results

* `MathFin.covariance_condMean_sampleMean`: `Cov(m(Θ), X̄) = Var(m(Θ))`
  under the joint mixture law.

## References

* Bühlmann, H. and Gisler, A., *A Course in Credibility Theory and its
  Applications*, Springer, 2005.

## Tags

credibility, covariance, finite mixture, MSC 62P05, JEL G22
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathFin

noncomputable def mixtureLaw {Θ Ξ : Type*} [Fintype Θ] [Fintype Ξ]
    [MeasurableSpace Θ] [MeasurableSpace Ξ] (n : ℕ)
    (p : Θ → ℝ) (w : Θ → Ξ → ℝ) : Measure (Θ × (Fin n → Ξ)) :=
  Measure.ofWeights Finset.univ (fun ω => p ω.1 * ∏ i, w ω.1 (ω.2 i))

def condMean {Ξ : Type*} [Fintype Ξ] (w : Ξ → ℝ) (v : Ξ → ℝ) : ℝ :=
  ∑ ξ, w ξ * v ξ

/-- Integrals against `mixtureLaw` are weighted finite sums. -/
private theorem integral_mixture {Θ Ξ : Type*} [Fintype Θ] [Fintype Ξ]
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (n : ℕ) (p : Θ → ℝ) (w : Θ → Ξ → ℝ)
    (f : Θ × (Fin n → Ξ) → ℝ) (hp : ∀ θ, 0 ≤ p θ)
    (hw : ∀ θ ξ, 0 ≤ w θ ξ) :
    ∫ ω, f ω ∂(mixtureLaw n p w)
      = ∑ ω, (p ω.1 * ∏ i, w ω.1 (ω.2 i)) * f ω := by
  have hnonneg :
      ∀ a ∈ (Finset.univ : Finset (Θ × (Fin n → Ξ))),
        0 ≤ p a.1 * ∏ i, w a.1 (a.2 i) := by
    intro a _
    exact mul_nonneg (hp a.1)
      (Finset.prod_nonneg (fun i _ => hw a.1 (a.2 i)))
  change ∫ ω, f ω ∂(Measure.ofWeights Finset.univ
    (fun ω => p ω.1 * ∏ i, w ω.1 (ω.2 i))) = _
  exact MeasureTheory.Measure.integral_ofWeights _ hnonneg f

/-- The conditionally-iid product weights sum to one for each risk. -/
private theorem weight_sum_one {Θ Ξ : Type*} [Fintype Ξ]
    (n : ℕ) (θ : Θ) (w : Θ → Ξ → ℝ)
    (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1) :
    (∑ x : Fin n → Ξ, ∏ i, w θ (x i)) = 1 := by
  have h1 : (∏ _i : Fin n, ∑ ξ, w θ ξ) = (1 : ℝ) := by
    simp [hw1 θ]
  have hpi := Fintype.prod_sum (fun (_i : Fin n) (ξ : Ξ) => w θ ξ)
  rw [← hpi]
  exact h1

/-- Each coordinate has conditional mean `condMean`, given the risk. -/
private theorem coord_marginal {Θ Ξ : Type*} [Fintype Ξ]
    (n : ℕ) (θ : Θ) (j : Fin n) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ)
    (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1) :
    (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) * v (x j))
      = condMean (w θ) v := by
  have hx : ∀ x : Fin n → Ξ, (∏ i, w θ (x i)) * v (x j)
      = ∏ i, (w θ (x i) * (if i = j then v (x i) else (1 : ℝ))) := by
    intro x
    have hite : (∏ i, (if i = j then v (x i) else (1 : ℝ))) = v (x j) :=
      Fintype.prod_ite_eq' j (fun i => v (x i))
    rw [Finset.prod_mul_distrib, hite]
  have hi : ∀ i : Fin n, (∑ ξ, w θ ξ * (if i = j then v ξ else (1 : ℝ)))
      = (if i = j then condMean (w θ) v else 1) := by
    intro i
    by_cases h : i = j
    · simp [h, condMean]
    · simp [h, hw1 θ]
  calc (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) * v (x j))
      = ∑ x : Fin n → Ξ,
        ∏ i, (w θ (x i) * (if i = j then v (x i) else 1)) :=
        Finset.sum_congr rfl (fun x _ => hx x)
    _ = ∏ i : Fin n, ∑ ξ, w θ ξ * (if i = j then v ξ else 1) :=
        (Fintype.prod_sum
          (fun (i : Fin n) (ξ : Ξ) =>
            w θ ξ * (if i = j then v ξ else 1))).symm
    _ = ∏ i : Fin n, (if i = j then condMean (w θ) v else 1) :=
        Finset.prod_congr rfl (fun i _ => hi i)
    _ = condMean (w θ) v := Fintype.prod_ite_eq' j (fun _ => condMean (w θ) v)

/-- The sample mean has conditional mean `condMean`, given the risk. -/
private theorem mean_sampleMean_cond {Θ Ξ : Type*} [Fintype Ξ]
    (n : ℕ) (θ : Θ) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ)
    (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1) (hn : 0 < n) :
    (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i)))
      = condMean (w θ) v := by
  have hx : ∀ x : Fin n → Ξ, (∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i))
      = ∑ i : Fin n, (n : ℝ)⁻¹ * ((∏ j, w θ (x j)) * v (x i)) := by
    intro x
    rw [← Finset.mul_sum]
    have hP : (∑ i : Fin n, (∏ j, w θ (x j)) * v (x i))
        = (∏ j, w θ (x j)) * ∑ i : Fin n, v (x i) :=
      (Finset.mul_sum _ _ _).symm
    rw [hP]
    ring
  have hi : ∀ i : Fin n,
      (∑ x : Fin n → Ξ, (n : ℝ)⁻¹ * ((∏ j, w θ (x j)) * v (x i)))
        = (n : ℝ)⁻¹ * condMean (w θ) v := by
    intro i
    calc (∑ x : Fin n → Ξ, (n : ℝ)⁻¹ * ((∏ j, w θ (x j)) * v (x i)))
        = (n : ℝ)⁻¹ * ∑ x : Fin n → Ξ, (∏ j, w θ (x j)) * v (x i) :=
          (Finset.mul_sum _ _ _).symm
      _ = (n : ℝ)⁻¹ * condMean (w θ) v := by
          rw [coord_marginal n θ i w v hw1]
  have hcard : (∑ _i : Fin n, (n : ℝ)⁻¹ * condMean (w θ) v)
      = (n : ℝ) * ((n : ℝ)⁻¹ * condMean (w θ) v) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfield : (n : ℝ) * ((n : ℝ)⁻¹ * condMean (w θ) v)
      = condMean (w θ) v := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hinv : (n : ℝ)⁻¹ * (n : ℝ) = 1 := inv_mul_cancel₀ hn0
    calc (n : ℝ) * ((n : ℝ)⁻¹ * condMean (w θ) v)
        = ((n : ℝ)⁻¹ * (n : ℝ)) * condMean (w θ) v := by ring
      _ = condMean (w θ) v := by rw [hinv, one_mul]
  calc (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i)))
      = ∑ x : Fin n → Ξ, ∑ i : Fin n,
        (n : ℝ)⁻¹ * ((∏ j, w θ (x j)) * v (x i)) :=
        Finset.sum_congr rfl (fun x _ => hx x)
    _ = ∑ i : Fin n, ∑ x : Fin n → Ξ,
        (n : ℝ)⁻¹ * ((∏ j, w θ (x j)) * v (x i)) :=
        Finset.sum_comm
    _ = ∑ _i : Fin n, (n : ℝ)⁻¹ * condMean (w θ) v :=
        Finset.sum_congr rfl (fun i _ => hi i)
    _ = (n : ℝ) * ((n : ℝ)⁻¹ * condMean (w θ) v) := hcard
    _ = condMean (w θ) v := hfield

/-- Expectation of the conditional-mean function under the mixture. -/
private theorem mean_fst {Θ Ξ : Type*} [Fintype Θ] [Fintype Ξ]
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (n : ℕ) (p : Θ → ℝ) (w : Θ → Ξ → ℝ)
    (v : Ξ → ℝ) (hp : ∀ θ, 0 ≤ p θ) (hw : ∀ θ ξ, 0 ≤ w θ ξ)
    (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1) :
    (∫ ω, condMean (w ω.1) v ∂(mixtureLaw n p w))
      = ∑ θ, p θ * condMean (w θ) v := by
  rw [integral_mixture n p w _ hp hw]
  simp only [Fintype.sum_prod_type]
  have hθ : ∀ θ : Θ,
      (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) * condMean (w θ) v)
        = p θ * condMean (w θ) v := by
    intro θ
    have hterm : ∀ x : Fin n → Ξ,
        (p θ * ∏ i, w θ (x i)) * condMean (w θ) v
          = (p θ * condMean (w θ) v) * ∏ i, w θ (x i) :=
      fun x => by ring
    calc (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) * condMean (w θ) v)
        = ∑ x : Fin n → Ξ, (p θ * condMean (w θ) v) * ∏ i, w θ (x i) :=
          Finset.sum_congr rfl (fun x _ => hterm x)
      _ = (p θ * condMean (w θ) v) * ∑ x : Fin n → Ξ, ∏ i, w θ (x i) :=
          (Finset.mul_sum _ _ _).symm
      _ = p θ * condMean (w θ) v := by
          rw [weight_sum_one n θ w hw1, mul_one]
  exact Finset.sum_congr rfl (fun θ _ => hθ θ)

/-- Expectation of the sample mean under the mixture. -/
private theorem mean_snd {Θ Ξ : Type*} [Fintype Θ] [Fintype Ξ]
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (n : ℕ) (hn : 0 < n) (p : Θ → ℝ)
    (w : Θ → Ξ → ℝ) (v : Ξ → ℝ) (hp : ∀ θ, 0 ≤ p θ)
    (hw : ∀ θ ξ, 0 ≤ w θ ξ) (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1) :
    (∫ ω, (n : ℝ)⁻¹ * ∑ i, v (ω.2 i) ∂(mixtureLaw n p w))
      = ∑ θ, p θ * condMean (w θ) v := by
  rw [integral_mixture n p w _ hp hw]
  simp only [Fintype.sum_prod_type]
  have hθ : ∀ θ : Θ,
      (∑ x : Fin n → Ξ,
        (p θ * ∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i)))
        = p θ * condMean (w θ) v := by
    intro θ
    have hterm : ∀ x : Fin n → Ξ,
        (p θ * ∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i))
          = p θ * ((∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i))) :=
      fun x => by ring
    calc (∑ x : Fin n → Ξ,
            (p θ * ∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i)))
        = ∑ x : Fin n → Ξ,
            p θ * ((∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i))) :=
          Finset.sum_congr rfl (fun x _ => hterm x)
      _ = p θ * ∑ x : Fin n → Ξ,
            (∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i)) :=
          (Finset.mul_sum _ _ _).symm
      _ = p θ * condMean (w θ) v := by
          rw [mean_sampleMean_cond n θ w v hw1 hn]
  exact Finset.sum_congr rfl (fun θ _ => hθ θ)

/-- The conditional-mean function is a.e. measurable for the mixture. -/
private theorem aemeasurable_fst {Θ Ξ : Type*} [Fintype Θ] [Fintype Ξ]
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace Ξ]
    (n : ℕ) (p : Θ → ℝ) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ) :
    AEMeasurable (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
      (mixtureLaw n p w) :=
  ((measurable_of_finite (fun θ : Θ => condMean (w θ) v)).comp
    measurable_fst).aemeasurable

theorem covariance_condMean_sampleMean {Θ Ξ : Type*} [Fintype Θ] [Fintype Ξ]
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (n : ℕ) (hn : 0 < n) (p : Θ → ℝ) (w : Θ → Ξ → ℝ)
    (v : Ξ → ℝ) (hp : ∀ θ, 0 ≤ p θ) (_hp1 : ∑ θ, p θ = 1)
    (hw : ∀ θ ξ, 0 ≤ w θ ξ) (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1) :
    covariance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
      (fun ω : Θ × (Fin n → Ξ) => (n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) (mixtureLaw n p w)
      = variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w) := by
  have hX : AEMeasurable (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
      (mixtureLaw n p w) := aemeasurable_fst n p w v
  have hmeanX : (∫ ω, condMean (w ω.1) v ∂(mixtureLaw n p w))
      = ∑ φ, p φ * condMean (w φ) v :=
    mean_fst n p w v hp hw hw1
  have hmeanY : (∫ ω, (n : ℝ)⁻¹ * ∑ i, v (ω.2 i) ∂(mixtureLaw n p w))
      = ∑ φ, p φ * condMean (w φ) v :=
    mean_snd n hn p w v hp hw hw1
  simp only [covariance, variance_eq_integral hX]
  rw [hmeanX, hmeanY, integral_mixture n p w _ hp hw,
    integral_mixture n p w _ hp hw]
  simp only [Fintype.sum_prod_type]
  have hθ : ∀ θ : Θ,
      (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
        ((condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) *
          (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v)))
      = ∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
        (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2 := by
    intro θ
    have hJ : (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v))
          = condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v := by
      have hterm : ∀ x : Fin n → Ξ, (∏ i, w θ (x i)) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v)
            = (∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i))
              - (∏ i, w θ (x i)) * (∑ φ, p φ * condMean (w φ) v) :=
        fun x => mul_sub _ _ _
      have hS : (∑ x : Fin n → Ξ,
              (∏ i, w θ (x i)) * (∑ φ, p φ * condMean (w φ) v))
            = ∑ φ, p φ * condMean (w φ) v := by
        have hSc : ∀ x : Fin n → Ξ, (∏ i, w θ (x i)) *
                (∑ φ, p φ * condMean (w φ) v)
              = (∑ φ, p φ * condMean (w φ) v) * ∏ i, w θ (x i) :=
          fun x => mul_comm _ _
        calc (∑ x : Fin n → Ξ,
                (∏ i, w θ (x i)) * (∑ φ, p φ * condMean (w φ) v))
            = ∑ x : Fin n → Ξ, (∑ φ, p φ * condMean (w φ) v) *
                ∏ i, w θ (x i) :=
              Finset.sum_congr rfl (fun x _ => hSc x)
          _ = (∑ φ, p φ * condMean (w φ) v) *
                ∑ x : Fin n → Ξ, ∏ i, w θ (x i) :=
              (Finset.mul_sum _ _ _).symm
          _ = ∑ φ, p φ * condMean (w φ) v := by
              rw [weight_sum_one n θ w hw1, mul_one]
      calc (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v))
          = ∑ x : Fin n → Ξ, ((∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i))
            - (∏ i, w θ (x i)) * (∑ φ, p φ * condMean (w φ) v)) :=
            Finset.sum_congr rfl (fun x _ => hterm x)
        _ = (∑ x : Fin n → Ξ,
              (∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i)))
            - ∑ x : Fin n → Ξ,
              (∏ i, w θ (x i)) * (∑ φ, p φ * condMean (w φ) v) := by
            rw [Finset.sum_sub_distrib]
        _ = condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v := by
            rw [mean_sampleMean_cond n θ w v hw1 hn, hS]
    have hP : (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
            (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v))
          = condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v := by
      have hPc : ∀ x : Fin n → Ξ, (∏ i, w θ (x i)) *
              (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)
            = (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) *
              ∏ i, w θ (x i) :=
        fun x => mul_comm _ _
      calc (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
              (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v))
          = ∑ x : Fin n → Ξ,
              (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) *
              ∏ i, w θ (x i) :=
            Finset.sum_congr rfl (fun x _ => hPc x)
        _ = (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) *
              ∑ x : Fin n → Ξ, ∏ i, w θ (x i) :=
            (Finset.mul_sum _ _ _).symm
        _ = condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v := by
            rw [weight_sum_one n θ w hw1, mul_one]
    have hL : (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
            ((condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v)))
          = (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)) *
            (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) := by
      have hterm : ∀ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
              ((condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) *
                (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v))
            = (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)) *
              ((∏ i, w θ (x i)) *
                (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v)) :=
        fun x => by ring
      calc (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
              ((condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) *
                (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v)))
          = ∑ x : Fin n → Ξ,
              (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)) *
              ((∏ i, w θ (x i)) *
                (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v)) :=
            Finset.sum_congr rfl (fun x _ => hterm x)
        _ = (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)) *
              ∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
                (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v) :=
            (Finset.mul_sum _ _ _).symm
        _ = (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)) *
              (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) := by
            rw [hJ]
    have hR : (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
            (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2)
          = (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)) *
            (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) := by
      have hterm : ∀ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
              (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2
            = (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)) *
              ((∏ i, w θ (x i)) *
                (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)) :=
        fun x => by ring
      calc (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
              (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2)
          = ∑ x : Fin n → Ξ,
              (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)) *
              ((∏ i, w θ (x i)) *
                (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)) :=
            Finset.sum_congr rfl (fun x _ => hterm x)
        _ = (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)) *
              ∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
                (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) :=
            (Finset.mul_sum _ _ _).symm
        _ = (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v)) *
              (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) := by
            rw [hP]
    exact hL.trans hR.symm
  exact Finset.sum_congr rfl (fun θ _ => hθ θ)

end MathFin
