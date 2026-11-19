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
* `MathFin.condVar`: conditional variance `∑ ξ, w ξ * (v ξ - m) ^ 2`
  around the conditional mean `m`.

## Main results

* `MathFin.covariance_condMean_sampleMean`: `Cov(m(Θ), X̄) = Var(m(Θ))`
  under the joint mixture law.
* `MathFin.variance_sampleMean`: `Var(X̄) = Var(m(Θ)) + E[v(Θ)] / n`
  under the joint mixture law.
* `MathFin.buhlmann_mse_le`: the Bühlmann affine predictor
  `μ + (a / (a + v / n)) (X̄ - μ)` minimizes the MSE over affine
  functions of `X̄`.
* `MathFin.buhlmann_coefficient_bounds`: the credibility factor
  `a / (a + v / n)` lies in `[0, 1]`.

## References

* [H. Bühlmann and A. Gisler, *A Course in Credibility Theory and its
  Applications*][BuhlmannGisler2005]

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
    have h_weight_sum_one : (∑ x : Fin n → Ξ, ∏ i, w θ (x i)) = 1 := by
      have h1 : (∏ _i : Fin n, ∑ ξ, w θ ξ) = (1 : ℝ) := by
        simp [hw1 θ]
      have hpi := Fintype.prod_sum (fun (_i : Fin n) (ξ : Ξ) => w θ ξ)
      rw [← hpi]
      exact h1
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
          rw [h_weight_sum_one, mul_one]
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
    have h_weight_sum_one : (∑ x : Fin n → Ξ, ∏ i, w θ (x i)) = 1 := by
      have h1 : (∏ _i : Fin n, ∑ ξ, w θ ξ) = (1 : ℝ) := by
        simp [hw1 θ]
      have hpi := Fintype.prod_sum (fun (_i : Fin n) (ξ : Ξ) => w θ ξ)
      rw [← hpi]
      exact h1
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
              rw [h_weight_sum_one, mul_one]
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
            rw [h_weight_sum_one, mul_one]
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

def condVar {Ξ : Type*} [Fintype Ξ] (w : Ξ → ℝ) (v : Ξ → ℝ) : ℝ :=
  ∑ ξ, w ξ * (v ξ - condMean w v) ^ 2

/-- Each coordinate has second moment `condVar` around the mean. -/
private theorem diag_moment_cond {Θ Ξ : Type*} [Fintype Ξ]
    (n : ℕ) (θ : Θ) (j : Fin n) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ)
    (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1) :
    (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
      (v (x j) - condMean (w θ) v) ^ 2)
      = condVar (w θ) v := by
  have hx : ∀ x : Fin n → Ξ, (∏ i, w θ (x i)) *
      (v (x j) - condMean (w θ) v) ^ 2
      = ∏ i, (w θ (x i) *
        (if i = j then (v (x i) - condMean (w θ) v) ^ 2 else (1 : ℝ))) := by
    intro x
    have hite : (∏ i, (if i = j then (v (x i) - condMean (w θ) v) ^ 2
        else (1 : ℝ))) = (v (x j) - condMean (w θ) v) ^ 2 :=
      Fintype.prod_ite_eq' j
        (fun i => (v (x i) - condMean (w θ) v) ^ 2)
    rw [Finset.prod_mul_distrib, hite]
  have hi : ∀ i : Fin n, (∑ ξ, w θ ξ *
      (if i = j then (v ξ - condMean (w θ) v) ^ 2 else (1 : ℝ)))
      = (if i = j then condVar (w θ) v else 1) := by
    intro i
    by_cases h : i = j
    · simp [h, condVar]
    · simp [h, hw1 θ]
  calc (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
        (v (x j) - condMean (w θ) v) ^ 2)
      = ∑ x : Fin n → Ξ,
        ∏ i, (w θ (x i) *
          (if i = j then (v (x i) - condMean (w θ) v) ^ 2 else 1)) :=
        Finset.sum_congr rfl (fun x _ => hx x)
    _ = ∏ i : Fin n, ∑ ξ, w θ ξ *
        (if i = j then (v ξ - condMean (w θ) v) ^ 2 else 1) :=
        (Fintype.prod_sum
          (fun (i : Fin n) (ξ : Ξ) =>
            w θ ξ * (if i = j then (v ξ - condMean (w θ) v) ^ 2 else 1))).symm
    _ = ∏ i : Fin n, (if i = j then condVar (w θ) v else 1) :=
        Finset.prod_congr rfl (fun i _ => hi i)
    _ = condVar (w θ) v :=
        Fintype.prod_ite_eq' j (fun _ => condVar (w θ) v)

/-- Distinct coordinates are uncorrelated around the mean, given the risk. -/
private theorem offdiag_moment_cond {Θ Ξ : Type*} [Fintype Ξ]
    (n : ℕ) (θ : Θ) (i j : Fin n) (hji : j ≠ i) (w : Θ → Ξ → ℝ)
    (v : Ξ → ℝ) (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1) :
    (∑ x : Fin n → Ξ, (∏ k, w θ (x k)) *
      ((v (x i) - condMean (w θ) v) * (v (x j) - condMean (w θ) v)))
      = 0 := by
  have hij : i ≠ j := Ne.symm hji
  have hx : ∀ x : Fin n → Ξ, (∏ k, w θ (x k)) *
      ((v (x i) - condMean (w θ) v) * (v (x j) - condMean (w θ) v))
      = ∏ k, (w θ (x k) *
        ((if k = i then (v (x k) - condMean (w θ) v) else 1) *
          (if k = j then (v (x k) - condMean (w θ) v) else 1))) := by
    intro x
    have h1 : (∏ k, (if k = i then (v (x k) - condMean (w θ) v)
        else (1 : ℝ))) = (v (x i) - condMean (w θ) v) :=
      Fintype.prod_ite_eq' i (fun k => (v (x k) - condMean (w θ) v))
    have h2 : (∏ k, (if k = j then (v (x k) - condMean (w θ) v)
        else (1 : ℝ))) = (v (x j) - condMean (w θ) v) :=
      Fintype.prod_ite_eq' j (fun k => (v (x k) - condMean (w θ) v))
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, h1, h2]
  have hSi : (∑ ξ, w θ ξ * ((v ξ - condMean (w θ) v) * 1)) = 0 := by
    have hterm : ∀ ξ : Ξ, w θ ξ * ((v ξ - condMean (w θ) v) * 1)
        = w θ ξ * v ξ - condMean (w θ) v * w θ ξ := fun ξ => by ring
    have hsub : (∑ ξ, w θ ξ * ((v ξ - condMean (w θ) v) * 1))
        = (∑ ξ, w θ ξ * v ξ) - ∑ ξ, condMean (w θ) v * w θ ξ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun ξ _ => hterm ξ)
    have hmul : (∑ ξ, condMean (w θ) v * w θ ξ)
        = condMean (w θ) v := by
      rw [(Finset.mul_sum _ _ _).symm, hw1 θ, mul_one]
    rw [hsub, hmul]
    simp [condMean]
  have hSi' : (∑ ξ, w θ ξ *
      ((if i = i then (v ξ - condMean (w θ) v) else 1) *
        (if i = j then (v ξ - condMean (w θ) v) else 1))) = 0 := by
    calc (∑ ξ, w θ ξ *
            ((if i = i then (v ξ - condMean (w θ) v) else 1) *
              (if i = j then (v ξ - condMean (w θ) v) else 1)))
        = (∑ ξ, w θ ξ * ((v ξ - condMean (w θ) v) * 1)) :=
          Finset.sum_congr rfl (fun ξ _ => by simp [hij])
      _ = 0 := hSi
  calc (∑ x : Fin n → Ξ, (∏ k, w θ (x k)) *
          ((v (x i) - condMean (w θ) v) *
            (v (x j) - condMean (w θ) v)))
      = ∑ x : Fin n → Ξ, ∏ k, (w θ (x k) *
          ((if k = i then (v (x k) - condMean (w θ) v) else 1) *
            (if k = j then (v (x k) - condMean (w θ) v) else 1))) :=
        Finset.sum_congr rfl (fun x _ => hx x)
    _ = ∏ k : Fin n, ∑ ξ, w θ ξ *
        ((if k = i then (v ξ - condMean (w θ) v) else 1) *
          (if k = j then (v ξ - condMean (w θ) v) else 1)) :=
        (Fintype.prod_sum
          (fun (k : Fin n) (ξ : Ξ) =>
            w θ ξ * ((if k = i then (v ξ - condMean (w θ) v) else 1) *
              (if k = j then (v ξ - condMean (w θ) v) else 1)))).symm
    _ = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hSi'

/-- Fixed-risk squared-deviation identity for the sample mean. -/
private theorem sqDev_sampleMean_cond {Θ Ξ : Type*} [Fintype Ξ]
    (n : ℕ) (θ : Θ) (w : Θ → Ξ → ℝ) (v : Ξ → ℝ) (c : ℝ)
    (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1) (hn : 0 < n) :
    (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
      (((n : ℝ)⁻¹ * ∑ i, v (x i)) - c) ^ 2)
      = condVar (w θ) v * (n : ℝ)⁻¹
        + (condMean (w θ) v - c) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hinv : (n : ℝ)⁻¹ * (n : ℝ) = 1 := inv_mul_cancel₀ hn0
  have h_weight_sum_one : (∑ x : Fin n → Ξ, ∏ i, w θ (x i)) = 1 := by
    have h1 : (∏ _i : Fin n, ∑ ξ, w θ ξ) = (1 : ℝ) := by
      simp [hw1 θ]
    have hpi := Fintype.prod_sum (fun (_i : Fin n) (ξ : Ξ) => w θ ξ)
    rw [← hpi]
    exact h1
  have hpair : ∀ i j : Fin n,
      (∑ x : Fin n → Ξ, (∏ k, w θ (x k)) *
        ((v (x i) - condMean (w θ) v) * (v (x j) - condMean (w θ) v)))
      = (if j = i then condVar (w θ) v else 0) := by
    intro i j
    by_cases h : j = i
    · subst j
      rw [ite_eq_left rfl]
      calc (∑ x : Fin n → Ξ, (∏ k, w θ (x k)) *
              ((v (x i) - condMean (w θ) v) *
                (v (x i) - condMean (w θ) v)))
          = ∑ x : Fin n → Ξ, (∏ k, w θ (x k)) *
              (v (x i) - condMean (w θ) v) ^ 2 :=
            Finset.sum_congr rfl (fun x _ => by ring)
        _ = condVar (w θ) v := diag_moment_cond n θ i w v hw1
    · rw [ite_eq_right h]
      exact offdiag_moment_cond n θ i j h w v hw1
  have hinner : ∀ i : Fin n,
      (∑ j : Fin n, ∑ x : Fin n → Ξ, (∏ k, w θ (x k)) *
        ((v (x i) - condMean (w θ) v) * (v (x j) - condMean (w θ) v)))
      = condVar (w θ) v := by
    intro i
    calc (∑ j : Fin n, ∑ x : Fin n → Ξ, (∏ k, w θ (x k)) *
            ((v (x i) - condMean (w θ) v) *
              (v (x j) - condMean (w θ) v)))
        = ∑ j : Fin n, (if j = i then condVar (w θ) v else 0) :=
          Finset.sum_congr rfl (fun j _ => hpair i j)
      _ = condVar (w θ) v := Fintype.sum_ite_eq' i (fun _ => condVar (w θ) v)
  have hx : ∀ x : Fin n → Ξ, ((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v
      = (n : ℝ)⁻¹ * ∑ i, (v (x i) - condMean (w θ) v) := by
    intro x
    have hcard : (∑ _i : Fin n, condMean (w θ) v)
        = (n : ℝ) * condMean (w θ) v := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsum : (∑ i, (v (x i) - condMean (w θ) v))
        = (∑ i, v (x i)) - (n : ℝ) * condMean (w θ) v := by
      rw [Finset.sum_sub_distrib, hcard]
    have hkey : (n : ℝ)⁻¹ * ((n : ℝ) * condMean (w θ) v)
        = condMean (w θ) v := by
      calc (n : ℝ)⁻¹ * ((n : ℝ) * condMean (w θ) v)
          = ((n : ℝ)⁻¹ * (n : ℝ)) * condMean (w θ) v := by ring
        _ = condMean (w θ) v := by rw [hinv, one_mul]
    rw [hsum, mul_sub, hkey]
  have hsq : ∀ x : Fin n → Ξ,
      (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2
      = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j : Fin n,
        (v (x i) - condMean (w θ) v) * (v (x j) - condMean (w θ) v) := by
    intro x
    have hmul : (∑ i : Fin n, (v (x i) - condMean (w θ) v)) *
        (∑ i : Fin n, (v (x i) - condMean (w θ) v))
        = ∑ i : Fin n, ∑ j : Fin n,
          (v (x i) - condMean (w θ) v) * (v (x j) - condMean (w θ) v) :=
      Finset.sum_mul_sum _ _ _ _
    calc (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2
        = ((n : ℝ)⁻¹ * ∑ i, (v (x i) - condMean (w θ) v)) ^ 2 := by rw [hx x]
      _ = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ *
          ((∑ i : Fin n, (v (x i) - condMean (w θ) v)) *
            (∑ i : Fin n, (v (x i) - condMean (w θ) v))) := by ring
      _ = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j : Fin n,
          (v (x i) - condMean (w θ) v) * (v (x j) - condMean (w θ) v) := by
          rw [hmul]
  have hpush : ∀ x : Fin n → Ξ, (∏ i, w θ (x i)) *
      (∑ i : Fin n, ∑ j : Fin n,
        (v (x i) - condMean (w θ) v) * (v (x j) - condMean (w θ) v))
      = ∑ i : Fin n, ∑ j : Fin n, (∏ k, w θ (x k)) *
        ((v (x i) - condMean (w θ) v) * (v (x j) - condMean (w θ) v)) := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact Finset.mul_sum _ _ _
  have hC : (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
      (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2)
      = condVar (w θ) v * (n : ℝ)⁻¹ := by
    have hterm : ∀ x : Fin n → Ξ, (∏ i, w θ (x i)) *
        (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2
        = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j : Fin n,
          (∏ k, w θ (x k)) *
            ((v (x i) - condMean (w θ) v) *
              (v (x j) - condMean (w θ) v)) := by
      intro x
      calc (∏ i, w θ (x i)) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2
          = (∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * (n : ℝ)⁻¹ *
              ∑ i : Fin n, ∑ j : Fin n,
                (v (x i) - condMean (w θ) v) *
                  (v (x j) - condMean (w θ) v)) := by rw [hsq x]
        _ = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ((∏ i, w θ (x i)) *
            (∑ i : Fin n, ∑ j : Fin n,
              (v (x i) - condMean (w θ) v) *
                (v (x j) - condMean (w θ) v))) := by
            ring
        _ = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j : Fin n,
            (∏ k, w θ (x k)) *
              ((v (x i) - condMean (w θ) v) *
                (v (x j) - condMean (w θ) v)) := by rw [hpush x]
    calc (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2)
        = ∑ x : Fin n → Ξ, (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j : Fin n,
          (∏ k, w θ (x k)) *
            ((v (x i) - condMean (w θ) v) *
              (v (x j) - condMean (w θ) v)) :=
          Finset.sum_congr rfl (fun x _ => hterm x)
      _ = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ x : Fin n → Ξ, ∑ i : Fin n, ∑ j : Fin n,
          (∏ k, w θ (x k)) *
            ((v (x i) - condMean (w θ) v) *
              (v (x j) - condMean (w θ) v)) :=
          (Finset.mul_sum _ _ _).symm
      _ = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ j : Fin n, ∑ x : Fin n → Ξ,
          (∏ k, w θ (x k)) *
            ((v (x i) - condMean (w θ) v) *
              (v (x j) - condMean (w θ) v)) := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact Finset.sum_comm
      _ = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ * ∑ _i : Fin n, condVar (w θ) v := by
          congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact hinner i
      _ = condVar (w θ) v * (n : ℝ)⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          calc ((n : ℝ)⁻¹ * (n : ℝ)⁻¹) * ((n : ℝ) * condVar (w θ) v)
              = ((n : ℝ)⁻¹ * (n : ℝ)) * ((n : ℝ)⁻¹ * condVar (w θ) v) := by
                ring
            _ = condVar (w θ) v * (n : ℝ)⁻¹ := by
                rw [hinv, one_mul]
                exact mul_comm _ _
  have hE0 : (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
      (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v)) = 0 := by
    have hterm : ∀ x : Fin n → Ξ, (∏ i, w θ (x i)) *
        (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v)
        = (∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i))
          - (∏ i, w θ (x i)) * condMean (w θ) v :=
      fun x => mul_sub _ _ _
    have hS1 : (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) * condMean (w θ) v)
        = condMean (w θ) v := by
      have hSc : ∀ x : Fin n → Ξ, (∏ i, w θ (x i)) * condMean (w θ) v
          = condMean (w θ) v * ∏ i, w θ (x i) := fun x => mul_comm _ _
      calc (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) * condMean (w θ) v)
          = ∑ x : Fin n → Ξ, condMean (w θ) v * ∏ i, w θ (x i) :=
            Finset.sum_congr rfl (fun x _ => hSc x)
        _ = condMean (w θ) v * ∑ x : Fin n → Ξ, ∏ i, w θ (x i) :=
            (Finset.mul_sum _ _ _).symm
        _ = condMean (w θ) v := by rw [h_weight_sum_one, mul_one]
    calc (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v))
        = (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) * ((n : ℝ)⁻¹ * ∑ i, v (x i)))
          - ∑ x : Fin n → Ξ, (∏ i, w θ (x i)) * condMean (w θ) v := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun x _ => hterm x)
      _ = condMean (w θ) v - condMean (w θ) v := by
          rw [mean_sampleMean_cond n θ w v hw1 hn, hS1]
      _ = 0 := sub_self _
  have hS2 : (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
      (condMean (w θ) v - c) ^ 2) = (condMean (w θ) v - c) ^ 2 := by
    have hSc : ∀ x : Fin n → Ξ, (∏ i, w θ (x i)) * (condMean (w θ) v - c) ^ 2
        = (condMean (w θ) v - c) ^ 2 * ∏ i, w θ (x i) :=
      fun x => mul_comm _ _
    calc (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) * (condMean (w θ) v - c) ^ 2)
        = ∑ x : Fin n → Ξ, (condMean (w θ) v - c) ^ 2 * ∏ i, w θ (x i) :=
          Finset.sum_congr rfl (fun x _ => hSc x)
      _ = (condMean (w θ) v - c) ^ 2 * ∑ x : Fin n → Ξ, ∏ i, w θ (x i) :=
          (Finset.mul_sum _ _ _).symm
      _ = (condMean (w θ) v - c) ^ 2 := by
          rw [h_weight_sum_one, mul_one]
  have hEq : (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
      (((n : ℝ)⁻¹ * ∑ i, v (x i)) - c) ^ 2)
      = (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
          (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2)
        + ((2 * (condMean (w θ) v - c)) *
          (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v))
          + ∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
            (condMean (w θ) v - c) ^ 2) := by
    have h1 : ∀ x : Fin n → Ξ, (∏ i, w θ (x i)) *
        (((n : ℝ)⁻¹ * ∑ i, v (x i)) - c) ^ 2
        = ((∏ i, w θ (x i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2
          + (2 * (condMean (w θ) v - c)) * ((∏ i, w θ (x i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v)))
          + (∏ i, w θ (x i)) * (condMean (w θ) v - c) ^ 2 := by
      intro x
      have hsplit : ((n : ℝ)⁻¹ * ∑ i, v (x i)) - c
          = (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v)
            + (condMean (w θ) v - c) := by ring
      rw [hsplit]
      ring
    calc (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (x i)) - c) ^ 2)
        = ∑ x : Fin n → Ξ, (((∏ i, w θ (x i)) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2
            + (2 * (condMean (w θ) v - c)) * ((∏ i, w θ (x i)) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v)))
            + (∏ i, w θ (x i)) * (condMean (w θ) v - c) ^ 2) :=
          Finset.sum_congr rfl (fun x _ => h1 x)
      _ = (∑ x : Fin n → Ξ, ((∏ i, w θ (x i)) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2
            + (2 * (condMean (w θ) v - c)) * ((∏ i, w θ (x i)) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v))))
          + ∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
            (condMean (w θ) v - c) ^ 2 := by
          rw [Finset.sum_add_distrib]
      _ = ((∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2)
            + ∑ x : Fin n → Ξ, (2 * (condMean (w θ) v - c)) *
              ((∏ i, w θ (x i)) *
                (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v)))
          + ∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
            (condMean (w θ) v - c) ^ 2 := by
          congr 1
          rw [Finset.sum_add_distrib]
      _ = (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2)
          + ((2 * (condMean (w θ) v - c)) *
            (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v))
            + ∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
              (condMean (w θ) v - c) ^ 2) := by
          rw [(Finset.mul_sum _ _ _).symm]
          ring
  calc (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
          (((n : ℝ)⁻¹ * ∑ i, v (x i)) - c) ^ 2)
      = (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
          (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v) ^ 2)
        + ((2 * (condMean (w θ) v - c)) *
          (∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (x i)) - condMean (w θ) v))
          + ∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
            (condMean (w θ) v - c) ^ 2) := hEq
    _ = condVar (w θ) v * (n : ℝ)⁻¹ + (condMean (w θ) v - c) ^ 2 := by
        rw [hC, hE0, hS2]
        ring

theorem variance_sampleMean {Θ Ξ : Type*} [Fintype Θ] [Fintype Ξ]
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (n : ℕ) (hn : 0 < n) (p : Θ → ℝ) (w : Θ → Ξ → ℝ)
    (v : Ξ → ℝ) (hp : ∀ θ, 0 ≤ p θ) (_hp1 : ∑ θ, p θ = 1)
    (hw : ∀ θ ξ, 0 ≤ w θ ξ) (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1) :
    variance (fun ω : Θ × (Fin n → Ξ) => (n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) (mixtureLaw n p w)
      = variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
        + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v := by
  have hX : AEMeasurable (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
      (mixtureLaw n p w) := aemeasurable_fst n p w v
  have hY : AEMeasurable
      (fun ω : Θ × (Fin n → Ξ) => (n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
      (mixtureLaw n p w) :=
    (measurable_of_finite _).aemeasurable
  have hmeanX : (∫ ω, condMean (w ω.1) v ∂(mixtureLaw n p w))
      = ∑ φ, p φ * condMean (w φ) v :=
    mean_fst n p w v hp hw hw1
  have hmeanY : (∫ ω, (n : ℝ)⁻¹ * ∑ i, v (ω.2 i) ∂(mixtureLaw n p w))
      = ∑ φ, p φ * condMean (w φ) v :=
    mean_snd n hn p w v hp hw hw1
  simp only [variance_eq_integral hY, variance_eq_integral hX]
  rw [hmeanX, hmeanY, integral_mixture n p w _ hp hw,
    integral_mixture n p w _ hp hw]
  simp only [Fintype.sum_prod_type]
  have hθ : ∀ θ : Θ,
      (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
        (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v) ^ 2)
      = (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
          (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2)
        + (n : ℝ)⁻¹ * (p θ * condVar (w θ) v) := by
    intro θ
    have h_weight_sum_one : (∑ x : Fin n → Ξ, ∏ i, w θ (x i)) = 1 := by
      have h1 : (∏ _i : Fin n, ∑ ξ, w θ ξ) = (1 : ℝ) := by
        simp [hw1 θ]
      have hpi := Fintype.prod_sum (fun (_i : Fin n) (ξ : Ξ) => w θ ξ)
      rw [← hpi]
      exact h1
    have hL : (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
        (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v) ^ 2)
        = p θ * (condVar (w θ) v * (n : ℝ)⁻¹
          + (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2) := by
      have hterm : ∀ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
          (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v) ^ 2
          = p θ * ((∏ i, w θ (x i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (x i))
              - ∑ φ, p φ * condMean (w φ) v) ^ 2) := fun x => by ring
      calc (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i))
                - ∑ φ, p φ * condMean (w φ) v) ^ 2)
          = ∑ x : Fin n → Ξ, p θ * ((∏ i, w θ (x i)) *
              (((n : ℝ)⁻¹ * ∑ i, v (x i))
                - ∑ φ, p φ * condMean (w φ) v) ^ 2) :=
            Finset.sum_congr rfl (fun x _ => hterm x)
        _ = p θ * ∑ x : Fin n → Ξ, (∏ i, w θ (x i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (x i))
              - ∑ φ, p φ * condMean (w φ) v) ^ 2 :=
            (Finset.mul_sum _ _ _).symm
        _ = p θ * (condVar (w θ) v * (n : ℝ)⁻¹
            + (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2) := by
            rw [sqDev_sampleMean_cond n θ w v _ hw1 hn]
    have hR : (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
        (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2)
        = p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2 := by
      have hterm : ∀ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
          (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2
          = (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2) *
            ∏ i, w θ (x i) := fun x => by ring
      calc (∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
              (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2)
          = ∑ x : Fin n → Ξ,
              (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2) *
              ∏ i, w θ (x i) :=
            Finset.sum_congr rfl (fun x _ => hterm x)
        _ = (p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2) *
            ∑ x : Fin n → Ξ, ∏ i, w θ (x i) :=
            (Finset.mul_sum _ _ _).symm
        _ = p θ * (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2 := by
            rw [h_weight_sum_one, mul_one]
    rw [hL, hR]
    ring
  calc (∑ θ : Θ, ∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
          (((n : ℝ)⁻¹ * ∑ i, v (x i)) - ∑ φ, p φ * condMean (w φ) v) ^ 2)
      = ∑ θ : Θ, ((∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
            (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2)
          + (n : ℝ)⁻¹ * (p θ * condVar (w θ) v)) :=
        Finset.sum_congr rfl (fun θ _ => hθ θ)
    _ = (∑ θ : Θ, ∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
          (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2)
        + ∑ θ : Θ, (n : ℝ)⁻¹ * (p θ * condVar (w θ) v) := by
        rw [Finset.sum_add_distrib]
    _ = (∑ θ : Θ, ∑ x : Fin n → Ξ, (p θ * ∏ i, w θ (x i)) *
          (condMean (w θ) v - ∑ φ, p φ * condMean (w φ) v) ^ 2)
        + (n : ℝ)⁻¹ * ∑ θ : Θ, p θ * condVar (w θ) v := by
        congr 1
        exact (Finset.mul_sum _ _ _).symm

/-- The mixture law is a probability measure: the mixture weights sum to one. -/
theorem isProbabilityMeasure_mixtureLaw {Θ Ξ : Type*} [Fintype Θ] [Fintype Ξ]
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (n : ℕ) (p : Θ → ℝ) (w : Θ → Ξ → ℝ)
    (hp : ∀ θ, 0 ≤ p θ) (hp1 : ∑ θ, p θ = 1)
    (hw : ∀ θ ξ, 0 ≤ w θ ξ) (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1) :
    IsProbabilityMeasure (mixtureLaw n p w) := by
  have hθ : ∀ θ : Θ, (∑ x : Fin n → Ξ, p θ * ∏ i, w θ (x i)) = p θ := by
    intro θ
    calc (∑ x : Fin n → Ξ, p θ * ∏ i, w θ (x i))
        = p θ * ∑ x : Fin n → Ξ, ∏ i, w θ (x i) := (Finset.mul_sum _ _ _).symm
      _ = p θ := by
        have hW : (∑ x : Fin n → Ξ, ∏ i, w θ (x i)) = 1 := by
          have h1 : (∏ _i : Fin n, ∑ xi, w θ xi) = (1 : ℝ) := by simp [hw1 θ]
          have hpi := Fintype.prod_sum (fun (_i : Fin n) (xi : Ξ) => w θ xi)
          rw [← hpi]
          exact h1
        rw [hW, mul_one]
  have hsum : (∑ ω : Θ × (Fin n → Ξ), p ω.1 * ∏ i, w ω.1 (ω.2 i)) = 1 := by
    calc (∑ ω : Θ × (Fin n → Ξ), p ω.1 * ∏ i, w ω.1 (ω.2 i))
        = ∑ θ, p θ := by
          simp only [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl (fun θ _ => hθ θ)
      _ = 1 := hp1
  have hInt : (∫ _, (1 : ℝ) ∂(mixtureLaw n p w))
      = ∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) * 1 :=
    integral_mixture n p w _ hp hw
  have hC : (∫ _, (1 : ℝ) ∂(mixtureLaw n p w))
      = (mixtureLaw n p w).real Set.univ := by
    rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
  rw [MeasureTheory.isProbabilityMeasure_iff_real]
  rw [hC] at hInt
  simp only [mul_one] at hInt
  rw [hsum] at hInt
  exact hInt

/-- Each conditional variance is nonnegative. -/
private theorem condVar_nonneg {Ξ : Type*} [Fintype Ξ] (w : Ξ → ℝ) (v : Ξ → ℝ)
    (hw : ∀ ξ, 0 ≤ w ξ) : 0 ≤ condVar w v := by
  unfold condVar
  exact Finset.sum_nonneg (fun ξ _ => mul_nonneg (hw ξ) (sq_nonneg _))

/-- Affine mean-squared-error expansion around the mixture mean. -/
private theorem mse_sum_eq {Θ Ξ : Type*} [Fintype Θ] [Fintype Ξ]
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (n : ℕ) (hn : 0 < n) (p : Θ → ℝ) (w : Θ → Ξ → ℝ)
    (v : Ξ → ℝ) (hp : ∀ θ, 0 ≤ p θ) (hp1 : ∑ θ, p θ = 1)
    (hw : ∀ θ ξ, 0 ≤ w θ ξ) (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1) (b0 b1 : ℝ) :
    (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
      (condMean (w ω.1) v - (b0 + b1 * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)))) ^ 2)
      = variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w)
        - 2 * b1 * variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w)
        + b1 ^ 2 * (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w) + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)
        + (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
          - ∑ θ, p θ * condMean (w θ) v) ^ 2 := by
  have hmeanM : (∫ ω, condMean (w ω.1) v ∂(mixtureLaw n p w))
      = ∑ θ, p θ * condMean (w θ) v :=
    mean_fst n p w v hp hw hw1
  have hmeanX : (∫ ω, (n : ℝ)⁻¹ * ∑ i, v (ω.2 i) ∂(mixtureLaw n p w))
      = ∑ θ, p θ * condMean (w θ) v :=
    mean_snd n hn p w v hp hw hw1
  have hX : AEMeasurable (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
      (mixtureLaw n p w) := aemeasurable_fst n p w v
  have hXbar : AEMeasurable
      (fun ω : Θ × (Fin n → Ξ) => (n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
      (mixtureLaw n p w) :=
    (measurable_of_finite _).aemeasurable
  have hW1 : (∑ ω : Θ × (Fin n → Ξ), p ω.1 * ∏ i, w ω.1 (ω.2 i)) = 1 := by
    have hθ : ∀ θ : Θ, (∑ x : Fin n → Ξ, p θ * ∏ i, w θ (x i)) = p θ := by
      intro θ
      calc (∑ x : Fin n → Ξ, p θ * ∏ i, w θ (x i))
          = p θ * ∑ x : Fin n → Ξ, ∏ i, w θ (x i) := (Finset.mul_sum _ _ _).symm
        _ = p θ := by
          have hW : (∑ x : Fin n → Ξ, ∏ i, w θ (x i)) = 1 := by
            have h1 : (∏ _i : Fin n, ∑ xi, w θ xi) = (1 : ℝ) := by simp [hw1 θ]
            have hpi := Fintype.prod_sum (fun (_i : Fin n) (xi : Ξ) => w θ xi)
            rw [← hpi]
            exact h1
          rw [hW, mul_one]
    calc (∑ ω : Θ × (Fin n → Ξ), p ω.1 * ∏ i, w ω.1 (ω.2 i))
        = ∑ θ, p θ := by
          simp only [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl (fun θ _ => hθ θ)
      _ = 1 := hp1
  have hVar : variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
      (mixtureLaw n p w)
      = ∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
        (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) ^ 2 := by
    rw [variance_eq_integral hX, hmeanM, integral_mixture n p w _ hp hw]
  have hCov : covariance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
      (fun ω : Θ × (Fin n → Ξ) => (n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
      (mixtureLaw n p w)
      = ∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
        ((condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) *
          (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v)) := by
    simp only [covariance]
    rw [hmeanM, hmeanX, integral_mixture n p w _ hp hw]
  have hVarX : variance
      (fun ω : Θ × (Fin n → Ξ) => (n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
      (mixtureLaw n p w)
      = ∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
        (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v) ^ 2 := by
    rw [variance_eq_integral hXbar, hmeanX, integral_mixture n p w _ hp hw]
  have hSumM : (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) * condMean (w ω.1) v)
      = ∑ θ, p θ * condMean (w θ) v :=
    (integral_mixture n p w _ hp hw).symm.trans hmeanM
  have hSumX : (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
      ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)))
      = ∑ θ, p θ * condMean (w θ) v :=
    (integral_mixture n p w _ hp hw).symm.trans hmeanX
  have hZ1 : (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
      (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v)) = 0 := by
    have e1 : ∀ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
        (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v)
        = (p ω.1 * ∏ i, w ω.1 (ω.2 i)) * condMean (w ω.1) v
          - (∑ θ, p θ * condMean (w θ) v) * (p ω.1 * ∏ i, w ω.1 (ω.2 i)) :=
      fun ω => by ring
    calc (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
            (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v))
        = ∑ ω : Θ × (Fin n → Ξ), ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) * condMean (w ω.1) v
          - (∑ θ, p θ * condMean (w θ) v) * (p ω.1 * ∏ i, w ω.1 (ω.2 i))) :=
          Finset.sum_congr rfl (fun ω _ => e1 ω)
      _ = (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) * condMean (w ω.1) v)
          - ∑ ω : Θ × (Fin n → Ξ), (∑ θ, p θ * condMean (w θ) v) *
            (p ω.1 * ∏ i, w ω.1 (ω.2 i)) :=
          Finset.sum_sub_distrib _ _
      _ = (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) * condMean (w ω.1) v)
          - (∑ θ, p θ * condMean (w θ) v) *
            ∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) := by
          congr 1
          exact (Finset.mul_sum _ _ _).symm
      _ = (∑ θ, p θ * condMean (w θ) v)
          - (∑ θ, p θ * condMean (w θ) v) * 1 := by
          rw [hSumM, hW1]
      _ = 0 := by ring
  have hZ2 : (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
      (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v)) = 0 := by
    have e2 : ∀ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
        (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v)
        = (p ω.1 * ∏ i, w ω.1 (ω.2 i)) * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
          - (∑ θ, p θ * condMean (w θ) v) * (p ω.1 * ∏ i, w ω.1 (ω.2 i)) :=
      fun ω => by ring
    calc (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v))
        = ∑ ω : Θ × (Fin n → Ξ), ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
          - (∑ θ, p θ * condMean (w θ) v) * (p ω.1 * ∏ i, w ω.1 (ω.2 i))) :=
          Finset.sum_congr rfl (fun ω _ => e2 ω)
      _ = (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)))
          - ∑ ω : Θ × (Fin n → Ξ), (∑ θ, p θ * condMean (w θ) v) *
            (p ω.1 * ∏ i, w ω.1 (ω.2 i)) :=
          Finset.sum_sub_distrib _ _
      _ = (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)))
          - (∑ θ, p θ * condMean (w θ) v) *
            ∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) := by
          congr 1
          exact (Finset.mul_sum _ _ _).symm
      _ = (∑ θ, p θ * condMean (w θ) v)
          - (∑ θ, p θ * condMean (w θ) v) * 1 := by
          rw [hSumX, hW1]
      _ = 0 := by ring
  have hexpand : ∀ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
      (condMean (w ω.1) v - (b0 + b1 * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)))) ^ 2
      = (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) ^ 2
        - 2 * b1 * ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          ((condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) *
            (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v)))
        + b1 ^ 2 * ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
            - ∑ θ, p θ * condMean (w θ) v) ^ 2)
        + 2 * (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) * b1 *
          ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v))
        - 2 * (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) *
          ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
            (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v))
        + (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) ^ 2 *
          (p ω.1 * ∏ i, w ω.1 (ω.2 i)) := by
    intro ω
    ring
  have hsplit : (∑ ω : Θ × (Fin n → Ξ), ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) ^ 2
        - 2 * b1 * ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          ((condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) *
            (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v)))
        + b1 ^ 2 * ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v) ^ 2)
        + 2 * (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) * b1 *
          ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v))
        - 2 * (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) *
          ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
            (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v))
        + (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) ^ 2 *
          (p ω.1 * ∏ i, w ω.1 (ω.2 i))))
      = (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) ^ 2)
        - (∑ ω : Θ × (Fin n → Ξ), 2 * b1 * ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          ((condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) *
            (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v))))
        + (∑ ω : Θ × (Fin n → Ξ), b1 ^ 2 * ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v) ^ 2))
        + (∑ ω : Θ × (Fin n → Ξ), 2 * (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) * b1 *
          ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v)))
        - (∑ ω : Θ × (Fin n → Ξ), 2 * (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) *
          ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
            (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v)))
        + (∑ ω : Θ × (Fin n → Ξ), (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) ^ 2 *
          (p ω.1 * ∏ i, w ω.1 (ω.2 i))) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have s1 : (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
      (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) ^ 2)
      = variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
        (mixtureLaw n p w) :=
    hVar.symm
  have s2 : (∑ ω : Θ × (Fin n → Ξ), 2 * b1 * ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
      ((condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) *
        (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v))))
      = 2 * b1 * covariance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
        (fun ω : Θ × (Fin n → Ξ) => (n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
        (mixtureLaw n p w) := by
    rw [← Finset.mul_sum, hCov.symm]
  have s3 : (∑ ω : Θ × (Fin n → Ξ), b1 ^ 2 * ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
      (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v) ^ 2))
      = b1 ^ 2 * variance
        (fun ω : Θ × (Fin n → Ξ) => (n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
        (mixtureLaw n p w) := by
    rw [← Finset.mul_sum, hVarX.symm]
  have s4 : (∑ ω : Θ × (Fin n → Ξ), 2 * (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
      - ∑ θ, p θ * condMean (w θ) v) * b1 *
        ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v))) = 0 := by
    rw [← Finset.mul_sum, hZ2, mul_zero]
  have s5 : (∑ ω : Θ × (Fin n → Ξ), 2 * (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
      - ∑ θ, p θ * condMean (w θ) v) *
        ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v))) = 0 := by
    rw [← Finset.mul_sum, hZ1, mul_zero]
  have s6 : (∑ ω : Θ × (Fin n → Ξ), (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
      - ∑ θ, p θ * condMean (w θ) v) ^ 2 * (p ω.1 * ∏ i, w ω.1 (ω.2 i)))
      = (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
        - ∑ θ, p θ * condMean (w θ) v) ^ 2 * 1 := by
    rw [← Finset.mul_sum, hW1]
  have hCovEq : covariance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
      (fun ω : Θ × (Fin n → Ξ) => (n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
      (mixtureLaw n p w)
      = variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
        (mixtureLaw n p w) :=
    covariance_condMean_sampleMean n hn p w v hp hp1 hw hw1
  have hVarXEq : variance (fun ω : Θ × (Fin n → Ξ) => (n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
      (mixtureLaw n p w)
      = variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
        (mixtureLaw n p w)
        + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v :=
    variance_sampleMean n hn p w v hp hp1 hw hw1
  calc (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (condMean (w ω.1) v - (b0 + b1 * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)))) ^ 2)
      = ∑ ω : Θ × (Fin n → Ξ), ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) ^ 2
        - 2 * b1 * ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          ((condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) *
            (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v)))
        + b1 ^ 2 * ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v) ^ 2)
        + 2 * (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) * b1 *
          ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v))
        - 2 * (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) *
          ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
            (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v))
        + (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) ^ 2 *
          (p ω.1 * ∏ i, w ω.1 (ω.2 i))) :=
        Finset.sum_congr rfl (fun ω _ => hexpand ω)
    _ = (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) ^ 2)
        - (∑ ω : Θ × (Fin n → Ξ), 2 * b1 * ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          ((condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v) *
            (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v))))
        + (∑ ω : Θ × (Fin n → Ξ), b1 ^ 2 * ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
          (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v) ^ 2))
        + (∑ ω : Θ × (Fin n → Ξ), 2 * (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) * b1 *
          ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
            (((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)) - ∑ θ, p θ * condMean (w θ) v)))
        - (∑ ω : Θ × (Fin n → Ξ), 2 * (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) *
          ((p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
            (condMean (w ω.1) v - ∑ θ, p θ * condMean (w θ) v)))
        + (∑ ω : Θ × (Fin n → Ξ), (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
            - ∑ θ, p θ * condMean (w θ) v) ^ 2 *
          (p ω.1 * ∏ i, w ω.1 (ω.2 i))) :=
        hsplit
    _ = variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w)
        - 2 * b1 * covariance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (fun ω : Θ × (Fin n → Ξ) => (n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
          (mixtureLaw n p w)
        + b1 ^ 2 * variance
          (fun ω : Θ × (Fin n → Ξ) => (n : ℝ)⁻¹ * ∑ i, v (ω.2 i))
          (mixtureLaw n p w)
        + 0 - 0
        + (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
          - ∑ θ, p θ * condMean (w θ) v) ^ 2 * 1 := by
        rw [s1, s2, s3, s4, s5, s6]
    _ = variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w)
        - 2 * b1 * variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w)
        + b1 ^ 2 * (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w) + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)
        + (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
          - ∑ θ, p θ * condMean (w θ) v) ^ 2 := by
        rw [hCovEq, hVarXEq]
        ring

/-- Bühlmann's affine predictor minimizes the mean squared error of
predicting the conditional mean by an affine function of the sample mean. -/
theorem buhlmann_mse_le {Θ Ξ : Type*} [Fintype Θ] [Fintype Ξ]
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (n : ℕ) (hn : 0 < n) (p : Θ → ℝ) (w : Θ → Ξ → ℝ)
    (v : Ξ → ℝ) (hp : ∀ θ, 0 ≤ p θ) (_hp1 : ∑ θ, p θ = 1)
    (hw : ∀ θ ξ, 0 ≤ w θ ξ) (hw1 : ∀ θ, ∑ ξ, w θ ξ = 1)
    (hd : 0 < variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
      + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v) (b0 b1 : ℝ) :
    ∫ ω, (condMean (w ω.1) v
        - ((∑ θ, p θ * condMean (w θ) v)
          + (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
            / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
              + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v))
          * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i) - ∑ θ, p θ * condMean (w θ) v))) ^ 2
        ∂(mixtureLaw n p w)
      ≤ ∫ ω, (condMean (w ω.1) v - (b0 + b1 * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)))) ^ 2
          ∂(mixtureLaw n p w) := by
  rw [integral_mixture n p w _ hp hw, integral_mixture n p w _ hp hw]
  have hnormTerm : ∀ ω : Θ × (Fin n → Ξ), ∀ Z : ℝ,
      (p ω.1 * ∏ i, w ω.1 (ω.2 i)) * (condMean (w ω.1) v
        - ((∑ θ, p θ * condMean (w θ) v)
          + Z * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i) - ∑ θ, p θ * condMean (w θ) v))) ^ 2
      = (p ω.1 * ∏ i, w ω.1 (ω.2 i)) * (condMean (w ω.1) v
        - (((∑ θ, p θ * condMean (w θ) v)
          - Z * (∑ θ, p θ * condMean (w θ) v))
          + Z * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)))) ^ 2 := fun ω Z => by ring
  have hnorm : (∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
      (condMean (w ω.1) v
        - ((∑ θ, p θ * condMean (w θ) v)
          + (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
            (mixtureLaw n p w)
            / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
              (mixtureLaw n p w)
              + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v))
          * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i) - ∑ θ, p θ * condMean (w θ) v))) ^ 2)
      = ∑ ω : Θ × (Fin n → Ξ), (p ω.1 * ∏ i, w ω.1 (ω.2 i)) *
        (condMean (w ω.1) v - (((∑ θ, p θ * condMean (w θ) v)
          - (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
            (mixtureLaw n p w)
            / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
              (mixtureLaw n p w)
              + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v))
            * (∑ θ, p θ * condMean (w θ) v))
          + (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
            (mixtureLaw n p w)
            / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
              (mixtureLaw n p w)
              + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v))
            * ((n : ℝ)⁻¹ * ∑ i, v (ω.2 i)))) ^ 2 :=
    Finset.sum_congr rfl (fun ω _ => hnormTerm ω _)
  rw [hnorm, mse_sum_eq n hn p w v hp _hp1 hw hw1
    ((∑ θ, p θ * condMean (w θ) v)
      - (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
        / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
          + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v))
        * (∑ θ, p θ * condMean (w θ) v))
    (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
      / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
        + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)),
    mse_sum_eq n hn p w v hp _hp1 hw hw1 b0 b1]
  have hA : 0 < variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
      (mixtureLaw n p w)
      + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v := hd
  have hAne : variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
      (mixtureLaw n p w)
      + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v ≠ 0 :=
    ne_of_gt hA
  have hexcessGen : ∀ Z : ℝ, Z * (variance
        (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
        + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)
      = variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
        (mixtureLaw n p w) →
      (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
        - 2 * b1 * variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w)
        + b1 ^ 2 * (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w) + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)
        + (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
          - ∑ θ, p θ * condMean (w θ) v) ^ 2)
      = (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
        - 2 * Z * variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w)
        + Z ^ 2 * (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w) + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)
        + (((∑ θ, p θ * condMean (w θ) v) - Z * (∑ θ, p θ * condMean (w θ) v))
          + Z * (∑ θ, p θ * condMean (w θ) v) - ∑ θ, p θ * condMean (w θ) v) ^ 2)
      + ((variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
          + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v) * (b1 - Z) ^ 2
        + (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
          - ∑ θ, p θ * condMean (w θ) v) ^ 2) := by
    intro Z hZA
    linear_combination 2 * (b1 - Z) * hZA
  have hZA : (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
      / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
        + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v))
      * (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
        + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)
      = variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w) :=
    div_mul_cancel₀ _ hAne
  have hkey : (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
        (mixtureLaw n p w)
        - 2 * b1 * variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w)
        + b1 ^ 2 * (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w) + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)
        + (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
          - ∑ θ, p θ * condMean (w θ) v) ^ 2)
      = (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w)
        - 2 * (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
            (mixtureLaw n p w)
          / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
            (mixtureLaw n p w)
            + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v))
          * variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w)
        + (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
            (mixtureLaw n p w)
          / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
            (mixtureLaw n p w)
            + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)) ^ 2
          * (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
            (mixtureLaw n p w) + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)
        + (((∑ θ, p θ * condMean (w θ) v)
            - (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
              (mixtureLaw n p w)
              / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
                (mixtureLaw n p w)
                + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v))
              * (∑ θ, p θ * condMean (w θ) v))
            + (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
              (mixtureLaw n p w)
              / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
                (mixtureLaw n p w)
                + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v))
              * (∑ θ, p θ * condMean (w θ) v)
          - ∑ θ, p θ * condMean (w θ) v) ^ 2)
      + ((variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
            (mixtureLaw n p w) + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)
          * (b1 - variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
            (mixtureLaw n p w)
            / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
              (mixtureLaw n p w)
              + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)) ^ 2
        + (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
          - ∑ θ, p θ * condMean (w θ) v) ^ 2) :=
    hexcessGen _ hZA
  have hnonneg : 0 ≤ (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
        (mixtureLaw n p w) + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)
        * (b1 - variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
          (mixtureLaw n p w)
          / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
            (mixtureLaw n p w)
            + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)) ^ 2
      + (b0 + b1 * (∑ θ, p θ * condMean (w θ) v)
        - ∑ θ, p θ * condMean (w θ) v) ^ 2 :=
    add_nonneg (mul_nonneg (le_of_lt hA) (sq_nonneg _)) (sq_nonneg _)
  rw [hkey]
  exact le_add_of_nonneg_right hnonneg

/-- The Bühlmann coefficient lies between zero and one. -/
theorem buhlmann_coefficient_bounds {Θ Ξ : Type*} [Fintype Θ] [Fintype Ξ]
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (n : ℕ) (hn : 0 < n) (p : Θ → ℝ) (w : Θ → Ξ → ℝ)
    (v : Ξ → ℝ) (hp : ∀ θ, 0 ≤ p θ) (_hp1 : ∑ θ, p θ = 1)
    (hw : ∀ θ ξ, 0 ≤ w θ ξ) (_hw1 : ∀ θ, ∑ ξ, w θ ξ = 1)
    (hd : 0 < variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
      + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v) :
    0 ≤ variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
        / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
          + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v)
      ∧ variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
          / (variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v) (mixtureLaw n p w)
            + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v) ≤ 1 := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hninv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hnpos)
  have hV : 0 ≤ variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
      (mixtureLaw n p w) :=
    variance_nonneg _ _
  have hVsum : 0 ≤ ∑ θ, p θ * condVar (w θ) v :=
    Finset.sum_nonneg (fun θ _ => mul_nonneg (hp θ) (condVar_nonneg _ _ (hw θ)))
  have hnv : 0 ≤ (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v :=
    mul_nonneg hninv hVsum
  have hA : 0 < variance (fun ω : Θ × (Fin n → Ξ) => condMean (w ω.1) v)
      (mixtureLaw n p w) + (n : ℝ)⁻¹ * ∑ θ, p θ * condVar (w θ) v := hd
  refine ⟨div_nonneg hV (le_of_lt hA), ?_⟩
  rw [div_le_one hA]
  exact le_add_of_nonneg_right hnv

end MathFin
