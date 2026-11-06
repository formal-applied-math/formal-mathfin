/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# The willow tree lattice: moment and marginal constraints

The willow tree of Curran is a recombining lattice that prices against a Brownian motion
by a discrete-time Markov chain on a **fixed** node set `z j` with a **fixed** discrete
marginal `q`: the number of nodes per time step is constant, and the lattice widens like
`√t` only through the scaling, not through new nodes. What replaces the recombination
familiar from binomial trees is a time-inhomogeneous family of transition matrices `P k`,
each row of which is chosen (in the original construction, by linear programming) to
satisfy, with `β k = √(t k / t (k+1))`,

    ∑ j, P k i j = 1                       (row stochasticity)
    ∑ j, P k i j * z j = β k * z i         (conditional first moment)
    ∑ j, P k i j * z j ^ 2
      = β k ^ 2 * z i ^ 2 + (1 - β k ^ 2)  (conditional second moment)

together with the marginal constraint `∑ i, q i * P k i j = q j`. The conditional
constraints are exactly those of a Brownian motion read at two grid times: for
`t' = (1 + α) t` the de-correlation coefficient `1 / √(1 + α)` equals `√(t / t')`, the
correlation of a Brownian motion at times `t` and `t'`, and the Brownian bridge relations
`E[W_{t'} | W_t = w] = (t / t') w` and `E[W_{t'}^2 | W_t = w] = w^2 + t' - t` become, in
the standardized variables `z`, precisely the two moment rows above (Curran 2001, *Willow
Power: Optimizing Derivative Pricing Trees*, ALGO Research Quarterly 4(4); the constraint
system as stated follows Ho 2000, *Willow Tree*, MSc thesis, University of British
Columbia).

This file proves the formalizable core of the construction:

1. the `β` identity `1 / √(1 + α) = √(t / t')` when `t' = (1 + α) t` (`willowBeta`,
   `willowBeta_eq_sqrt_div`, and its grid instantiation `willowBeta_eq_sqrt_div'`);
2. **moment propagation**: a chain started at a marginal `q` of mass `1`, mean `0` and
   second moment `1` keeps mass `1`, mean `0` and second moment `1` at every step, for
   *any* family of transition matrices satisfying the row constraints — an induction on
   the step that needs neither the marginal constraint nor non-negativity of the entries
   (`willowMarginal_mass`, `willowMarginal_mean`, `willowMarginal_secondMoment`);
3. **marginal preservation**: with the marginal constraint added, the marginal at *every*
   step is the same discrete law `q` (`willowMarginal_eq`);
4. the **cross moment** of the chain at two consecutive steps: `E[Z_k Z_{k+1}] = β k`,
   and in the unstandardized variables `X k = √(t k) * Z k` the cross moment across
   `[t k, t (k+1)]` is `t k` — the Brownian value, and the de-correlation the
   construction is named for (`willowMarginal_crossMoment`, `willowScaled_secondMoment`,
   `willowScaled_crossMoment`).

Nothing here touches the linear program that *finds* such a matrix (feasibility, the
objective, entry non-negativity): the statements are unconditional in the matrix `P`,
which is what makes them usable against any solver output. No claim is made about prices
computed on the lattice.
-/

@[expose] public section

namespace MathFin

/-- **Curran's de-correlation coefficient**: for a grid step widening time by the factor
`1 + α`, the willow tree pairs times `t` and `t' = (1 + α) t` through `β = 1 / √(1 + α)`,
which is `√(t / t')` (`willowBeta_eq_sqrt_div`) — the correlation of a Brownian motion
read at `t` and `t'`. -/
noncomputable def willowBeta (α : ℝ) : ℝ := 1 / √(1 + α)

/-- **The `β` identity of the willow tree**: if `t' = (1 + α) * t` with `t > 0`, then
`1 / √(1 + α) = √(t / t')`. -/
theorem willowBeta_eq_sqrt_div {t t' α : ℝ} (hα : 0 < 1 + α) (ht : 0 < t)
    (ht' : t' = (1 + α) * t) : willowBeta α = √(t / t') := by
  rw [willowBeta, ht']
  have hdiv : t / ((1 + α) * t) = (1 + α)⁻¹ := by field_simp
  rw [hdiv, Real.sqrt_inv, one_div]

/-- **The `β` identity on a time grid**: with `α` computed from consecutive grid times as
in the willow tree construction, `α k = (t (k+1) - t k) / t k`, the de-correlation
coefficient is `√(t k / t (k+1))`. -/
theorem willowBeta_eq_sqrt_div' {t : ℕ → ℝ} (ht0 : ∀ k, 0 < t k) (k : ℕ) :
    willowBeta ((t (k + 1) - t k) / t k) = √(t k / t (k + 1)) := by
  have htne : t k ≠ 0 := ne_of_gt (ht0 k)
  refine willowBeta_eq_sqrt_div ?_ (ht0 k) ?_
  · have h1 : 1 + (t (k + 1) - t k) / t k = t (k + 1) / t k := by
      rw [add_div_eq_mul_add_div 1 _ htne, one_mul]
      congr 1
      ring
    rw [h1]
    exact div_pos (ht0 (k + 1)) (ht0 k)
  · rw [add_mul, one_mul, div_mul_cancel₀ _ htne]
    ring

variable {n : ℕ}

/-- **The willow tree moment constraints** on a family of transition matrices `P k` over
a fixed node set `z`: each matrix is row stochastic, and its rows match the first two
conditional moments of the standardized Brownian pair with correlation `β k`. No
non-negativity is required of the entries — the moment statements below are insensitive
to it (it is the linear program's business, not the induction's). -/
structure WillowMomentConstraints (z : Fin n → ℝ) (β : ℕ → ℝ)
    (P : ℕ → Fin n → Fin n → ℝ) : Prop where
  /-- Every transition matrix is row stochastic. -/
  rowStochastic : ∀ k i, ∑ j, P k i j = 1
  /-- Conditional first moment: `E[Z_{k+1} | Z_k = z i] = β k * z i`. -/
  mean : ∀ k i, ∑ j, P k i j * z j = β k * z i
  /-- Conditional second moment: `E[Z_{k+1}^2 | Z_k = z i] = β k^2 * z i^2 + (1 - β k^2)`. -/
  secondMoment : ∀ k i, ∑ j, P k i j * z j ^ 2 = β k ^ 2 * z i ^ 2 + (1 - β k ^ 2)

variable {z : Fin n → ℝ} {β : ℕ → ℝ} {P : ℕ → Fin n → Fin n → ℝ} {q : Fin n → ℝ}

/-- The marginal of the willow chain at step `k`: the initial law `q` rolled forward
through the transition matrices `P 0, P 1, …, P (k-1)`. -/
noncomputable def willowMarginal (P : ℕ → Fin n → Fin n → ℝ) (q : Fin n → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => q
  | k + 1 => fun j => ∑ i, willowMarginal P q k i * P k i j

@[simp] theorem willowMarginal_zero : willowMarginal P q 0 = q := rfl

@[simp] theorem willowMarginal_succ (k : ℕ) :
    willowMarginal P q (k + 1) = fun j => ∑ i, willowMarginal P q k i * P k i j := rfl

/-- A weighted double sum rolls up into the weighted row pairings. -/
private theorem sum_weighted_rows (w : Fin n → ℝ) (g : Fin n → Fin n → ℝ) (h : Fin n → ℝ) :
    ∑ j, (∑ i, w i * g i j) * h j = ∑ i, w i * ∑ j, g i j * h j := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum Finset.univ (fun j => g i j * h j) (w i)]
  exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _

/-- A scalar factor pulls out of a weighted finite sum. -/
private theorem sum_pull_scalar (w : Fin n → ℝ) (a : ℝ) (f : Fin n → ℝ) :
    ∑ i, w i * (a * f i) = a * ∑ i, w i * f i := by
  have h : ∑ i, w i * (a * f i) = ∑ i, a * (w i * f i) :=
    Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  rw [h, Finset.mul_sum]

/-- An affine per-row identity transfers to the marginals. -/
private theorem sum_affine (w : Fin n → ℝ) (a b : ℝ) (f : Fin n → ℝ) :
    ∑ i, w i * (a * f i + b) = a * ∑ i, w i * f i + b * ∑ i, w i := by
  have hsplit : ∑ i, w i * (a * f i + b) = ∑ i, (w i * (a * f i) + w i * b) :=
    Finset.sum_congr rfl fun i _ => by ring
  have hconst : ∑ i, w i * b = b * ∑ i, w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, Finset.sum_add_distrib, sum_pull_scalar, hconst]

/-- The next marginal has total mass `1` as soon as the current one does. -/
theorem willowMarginal_mass_succ (hP : WillowMomentConstraints z β P) (k : ℕ)
    (h : ∑ i, willowMarginal P q k i = 1) :
    ∑ j, willowMarginal P q (k + 1) j = 1 := by
  have h2 : ∑ j, ∑ i, willowMarginal P q k i * P k i j
      = ∑ i, willowMarginal P q k i * ∑ j, P k i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  simp only [willowMarginal_succ]
  rw [h2, Finset.sum_congr rfl fun i _ => by rw [hP.rowStochastic k i]]
  simp only [mul_one, h]

/-- **Mass preservation**: the willow marginal has total mass `1` at every step, for any
family of transition matrices satisfying the row-stochasticity constraint. -/
theorem willowMarginal_mass (hP : WillowMomentConstraints z β P) (hq : ∑ i, q i = 1) (k : ℕ) :
    ∑ j, willowMarginal P q k j = 1 := by
  induction k with
  | zero => exact hq
  | succ k ih => exact willowMarginal_mass_succ hP k ih

/-- The next marginal's first moment is `β k` times the current one. -/
theorem willowMarginal_mean_succ (hP : WillowMomentConstraints z β P) (k : ℕ) :
    ∑ j, willowMarginal P q (k + 1) j * z j = β k * ∑ i, willowMarginal P q k i * z i := by
  simp only [willowMarginal_succ]
  rw [sum_weighted_rows]
  exact (Finset.sum_congr rfl fun i _ => by rw [hP.mean k i]).trans (sum_pull_scalar _ _ _)

/-- The next marginal's second moment is `β k ^ 2` times the current one, plus the
standardized Brownian increment variance `(1 - β k ^ 2)` times the current mass. -/
theorem willowMarginal_secondMoment_succ (hP : WillowMomentConstraints z β P) (k : ℕ) :
    ∑ j, willowMarginal P q (k + 1) j * z j ^ 2
      = β k ^ 2 * ∑ i, willowMarginal P q k i * z i ^ 2
        + (1 - β k ^ 2) * ∑ i, willowMarginal P q k i := by
  simp only [willowMarginal_succ]
  rw [sum_weighted_rows]
  exact (Finset.sum_congr rfl fun i _ => by rw [hP.secondMoment k i]).trans
    (sum_affine _ _ _ _)

/-- **Mean propagation**: a willow chain started at a mean-zero marginal keeps mean zero
at every step, for any family of transition matrices satisfying the conditional first
moment constraint. No marginal constraint and no non-negativity are needed. -/
theorem willowMarginal_mean (hP : WillowMomentConstraints z β P)
    (hq0 : ∑ i, q i * z i = 0) (k : ℕ) :
    ∑ j, willowMarginal P q k j * z j = 0 := by
  induction k with
  | zero => exact hq0
  | succ k ih => rw [willowMarginal_mean_succ hP k, ih, mul_zero]

/-- **Second-moment propagation**: a willow chain started at a marginal of unit second
moment keeps unit second moment at every step, for any family of transition matrices
satisfying the conditional second moment constraint. This is the variance-on-track
induction: combined with the scaling `√(t k)` it keeps the chain's marginal variance at
`t k` (`willowScaled_secondMoment`). -/
theorem willowMarginal_secondMoment (hP : WillowMomentConstraints z β P)
    (hq : ∑ i, q i = 1) (hq2 : ∑ i, q i * z i ^ 2 = 1) (k : ℕ) :
    ∑ j, willowMarginal P q k j * z j ^ 2 = 1 := by
  induction k with
  | zero => exact hq2
  | succ k ih =>
    rw [willowMarginal_secondMoment_succ hP k, ih, willowMarginal_mass hP hq k]
    ring

/-- **Marginal preservation**: if every transition matrix also satisfies the marginal
constraint `∑ i, q i * P k i j = q j`, then the willow marginal is the *same* discrete
law `q` at every step — the constant node set and constant marginal that distinguish the
willow tree from growing recombining trees. The moment constraints are not needed. -/
theorem willowMarginal_eq (hmarg : ∀ k j, ∑ i, q i * P k i j = q j) (k : ℕ) :
    willowMarginal P q k = q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext j
    simp only [willowMarginal_succ]
    rw [ih]
    exact hmarg k j

/-- **Cross moment**: the willow chain's standardized cross moment across one step is
its de-correlation coefficient, `E[Z_k Z_{k+1}] = β k` — under any family of transition
matrices satisfying the conditional first moment constraint. -/
theorem willowMarginal_crossMoment (hP : WillowMomentConstraints z β P)
    (hq : ∑ i, q i = 1) (hq2 : ∑ i, q i * z i ^ 2 = 1) (k : ℕ) :
    ∑ i, willowMarginal P q k i * z i * ∑ j, P k i j * z j = β k := by
  calc ∑ i, willowMarginal P q k i * z i * ∑ j, P k i j * z j
      = ∑ i, willowMarginal P q k i * z i * (β k * z i) :=
        Finset.sum_congr rfl fun i _ => by rw [hP.mean k i]
    _ = β k * ∑ i, willowMarginal P q k i * z i ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = β k := by rw [willowMarginal_secondMoment hP hq hq2, mul_one]

/-- **The scaled chain's second moment**: in the unstandardized variables
`X k = √(t k) * Z k` on an initially unit-variance willow chain, the marginal second
moment (equal to the variance, the mean being zero) at step `k` is `t k` — the Brownian
marginal variance at the grid time. -/
theorem willowScaled_secondMoment (hP : WillowMomentConstraints z β P)
    (hq : ∑ i, q i = 1) (hq2 : ∑ i, q i * z i ^ 2 = 1)
    (t : ℕ → ℝ) (ht : ∀ k, 0 ≤ t k) (k : ℕ) :
    ∑ j, willowMarginal P q k j * (√(t k) * z j) ^ 2 = t k := by
  have hpow : ∀ j, (√(t k) * z j) ^ 2 = t k * z j ^ 2 := fun j => by
    rw [mul_pow, Real.sq_sqrt (ht k)]
  calc ∑ j, willowMarginal P q k j * (√(t k) * z j) ^ 2
      = ∑ j, willowMarginal P q k j * (t k * z j ^ 2) :=
        Finset.sum_congr rfl fun j _ => by rw [hpow j]
    _ = t k * ∑ j, willowMarginal P q k j * z j ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _
    _ = t k := by rw [willowMarginal_secondMoment hP hq hq2, mul_one]

/-- `√a * √(a / b) * √b = a` for `0 ≤ a` and `0 < b`. -/
private theorem sqrt_mul_sqrt_div' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    √a * √(a / b) * √b = a := by
  rw [Real.sqrt_div' a (le_of_lt hb), mul_div_assoc', Real.mul_self_sqrt ha,
    div_mul_cancel₀ _ (Real.sqrt_ne_zero'.mpr hb)]

/-- **The scaled chain's cross moment**: in the unstandardized variables
`X k = √(t k) * Z k`, the cross moment across the step `[t k, t (k+1)]` is
`E[X_k X_{k+1}] = t k` — exactly the Brownian covariance at two grid times, which is the
de-correlation property Curran's constraint system encodes. -/
theorem willowScaled_crossMoment (hP : WillowMomentConstraints z β P)
    (hq : ∑ i, q i = 1) (hq2 : ∑ i, q i * z i ^ 2 = 1)
    (t : ℕ → ℝ) (ht : ∀ k, 0 ≤ t k) (ht1 : ∀ k, 0 < t (k + 1))
    (hβ : ∀ k, β k = √(t k / t (k + 1))) (k : ℕ) :
    ∑ i, willowMarginal P q k i * (√(t k) * z i) * ∑ j, P k i j * (√(t (k + 1)) * z j)
      = t k := by
  have hinner : ∀ i : Fin n, ∑ j, P k i j * (√(t (k + 1)) * z j)
      = √(t (k + 1)) * (β k * z i) := by
    intro i
    have hterm : ∀ j : Fin n, P k i j * (√(t (k + 1)) * z j)
        = √(t (k + 1)) * (P k i j * z j) := fun j => by ring
    simp only [hterm]
    rw [← Finset.mul_sum, hP.mean k i]
  calc ∑ i, willowMarginal P q k i * (√(t k) * z i) * ∑ j, P k i j * (√(t (k + 1)) * z j)
      = ∑ i, willowMarginal P q k i * (√(t k) * z i) * (√(t (k + 1)) * (β k * z i)) :=
        Finset.sum_congr rfl fun i _ => by rw [hinner i]
    _ = ∑ i, (√(t k) * β k * √(t (k + 1))) * (willowMarginal P q k i * z i ^ 2) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = √(t k) * β k * √(t (k + 1)) * ∑ i, willowMarginal P q k i * z i ^ 2 := by
        rw [Finset.mul_sum]
    _ = t k := by
        rw [hβ k, willowMarginal_secondMoment hP hq hq2, mul_one,
          sqrt_mul_sqrt_div' (ht k) (ht1 k)]

end MathFin
