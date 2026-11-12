/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.Wiener.WienerIntegralL2
public import MathFin.Probability.Gaussian.BivariateNormalCDF
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp

/-!
# The willow tree lattice: moment and marginal constraints

The willow tree of Curran prices against a Brownian motion with a discrete-time
Markov chain on a **fixed** node set `z j` with a **fixed** discrete marginal `q` —
paths recombine trivially because the nodes never grow. The number of nodes per time
step is constant, and the lattice widens like `√t` only through the scaling, not
through new nodes. What replaces the recombination
familiar from binomial trees is a time-inhomogeneous family of transition matrices `P k`,
each matrix of which is chosen (in the original construction, by a linear program over
the whole matrix) to satisfy, with `β k = √(t k / t (k+1))`,

    ∑ j, P k i j = 1                       (row stochasticity)
    ∑ j, P k i j * z j = β k * z i         (conditional first moment)
    ∑ j, P k i j * z j ^ 2
      = β k ^ 2 * z i ^ 2 + (1 - β k ^ 2)  (conditional second moment)

together with the marginal constraint `∑ i, q i * P k i j = q j`. The conditional
constraints are exactly those of a Brownian motion read at two grid times: for
`t' = (1 + α) t` the de-correlation coefficient `1 / √(1 + α)` equals `√(t / t')`, the
correlation of a Brownian motion at times `t` and `t'`, and the Markov relations
`E[W_{t'} | W_t = w] = w` and `E[W_{t'}^2 | W_t = w] = w^2 + (t' - t)` become, in the
standardized variables `Z = W_t / √t`, `Z' = W_{t'} / √t'`, precisely the two moment
rows above.

## Main definitions

* `willowBeta` — Curran's de-correlation coefficient `1 / √(1 + α)`.
* `WillowMomentConstraints` — the three row constraints above, bundled as a predicate on
  a family of transition matrices. No non-negativity is required of the entries: the
  moment statements below are insensitive to it (it is the linear program's business,
  not the induction's).
* `willowMarginal P q k` — the chain's marginal at step `k`, the initial law `q` rolled
  forward through `P 0, …, P (k-1)`.

## Main results

* `willowBeta_eq_sqrt_div`, `willowBeta_eq_sqrt_div'` — the `β` identity
  `1 / √(1 + α) = √(t / t')` when `t' = (1 + α) t`, and its grid instantiation.
* `willowMarginal_mass`, `willowMarginal_mean`, `willowMarginal_secondMoment` —
  **moment propagation**: a chain started at a marginal of mass `1`, mean `0` and unit
  second moment keeps mass `1`, mean `0` and unit second moment at every step, for *any*
  family of transition matrices satisfying the row constraints — an induction needing
  neither the marginal constraint nor non-negativity of the entries.
* `willowMarginal_eq` — **marginal preservation**: with the marginal constraint added,
  the marginal at every step is the same discrete law `q`.
* `willowMarginal_crossMoment`, `willowScaled_secondMoment`, `willowScaled_crossMoment` —
  the scaled moments and cross moments: `E[Z_k Z_{k+1}] = β k`, and — with the chain's
  own coefficient tied to the grid by `β k = √(t k / t (k+1))` — in the unstandardized
  variables `X k = √(t k) * Z k` the second moment is `t k` and the cross moment across
  `[t k, t (k+1)]` is `t k` — the Brownian values, which is the de-correlation
  property Curran's constraint system encodes.
* `willowMarginal_crossMoment_eq_willowBeta` — the join: the chain's standardized
  cross moment is the construction's own `willowBeta` coefficient once `β k` is tied
  to the grid.
* `willowScaled_secondMoment_eq_integral_sq`, `willowScaled_crossMoment_eq_integral_mul` — **the
  Brownian join**: against a pre-Brownian motion `W` on the grid `t k`, the scaled chain's second
  moment is `E[W_{t k}²]` and its cross moment is `E[W_{t k} W_{t (k+1)}]`.
* `WillowMomentConstraints.sq_le_one`,
  `WillowMomentConstraints.bivariateNormal_moments` — **feasibility**: an
  honest (non-negative, summing-to-one) transition row forces `β k ^ 2 ≤ 1`, the
  lattice-side analogue of `sq_le_one_of_covariance_unit` for a correlated Gaussian
  pair; and for such a coefficient the standard bivariate normal law
  `bivariateNormalLaw (β k)` has unit variances and covariance `β k`.

Nothing here touches the linear program that *finds* such a matrix (feasibility of the
full system, the objective, sparsity): the statements are unconditional in the matrix
`P`, which is what makes them usable against any solver output. No claim is made about
prices computed on the lattice.

The chain is stated entrywise — finite sums over the node set, matching the entrywise
form of Curran's constraint rows. Over Mathlib's matrix API the recursion is `vecMul`
and the roll-up lemma below is the entrywise form of `Matrix.dotProduct_mulVec`; the
entrywise form was kept because every hypothesis here is itself an entrywise statement
about rows.

## References

* [M. Curran, *Willow Power: Optimizing Derivative Pricing Trees*][Curran2001],
  ALGO Research Quarterly 4(4), 2001.
* [A. C. T. Ho, *Willow Tree*][Ho2000], MSc thesis in Mathematics, University of British
  Columbia (2000) — the constraint system as stated.
* [F. M. Massari, *willowtree*][willowtreePkg] — the open-source implementation whose
  `lp.py` states the constraint set as used here.

## Tags

willow tree, lattice, transition matrix, moment matching,
de-correlation, Markov chain, Brownian motion, MSC 60J10, MSC 91G60, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- **Curran's de-correlation coefficient**: for a grid step widening time by the factor
`1 + α > 0`, the willow tree pairs times `t` and `t' = (1 + α) t` through
`β = 1 / √(1 + α)`, which is `√(t / t')` (`willowBeta_eq_sqrt_div`) — the correlation of
a Brownian motion read at `t` and `t'`. (Without `1 + α > 0` the definition takes the
junk value `0`.) -/
noncomputable def willowBeta (α : ℝ) : ℝ := 1 / √(1 + α)

/-- **The `β` identity of the willow tree**: if `0 < 1 + α` and `t' = (1 + α) * t`
with `t > 0`, then `1 / √(1 + α) = √(t / t')`. The hypotheses keep both sides in the
meaningful range (`willowBeta` takes the junk value `0` outside it); the identity's
algebra survives without them. -/
theorem willowBeta_eq_sqrt_div {t t' α : ℝ} (hα : 0 < 1 + α) (ht : 0 < t)
    (ht' : t' = (1 + α) * t) : willowBeta α = √(t / t') := by
  rw [willowBeta, ht']
  have hdiv : t / ((1 + α) * t) = (1 + α)⁻¹ := by field_simp
  rw [hdiv, Real.sqrt_inv, one_div]

/-- **The `β` identity on a time grid**: with `α` computed from consecutive grid times as
in the willow tree construction, `α k = (t (k+1) - t k) / t k`, the de-correlation
coefficient is `√(t k / t (k+1))`. Only the two times it pairs are required to be
positive — a willow grid may start at `t 0 = 0` — and `htk1` earns its place in the
proof (the positivity it feeds `div_pos`). -/
theorem willowBeta_eq_sqrt_div' {t : ℕ → ℝ} (k : ℕ) (htk : 0 < t k)
    (htk1 : 0 < t (k + 1)) :
    willowBeta ((t (k + 1) - t k) / t k) = √(t k / t (k + 1)) := by
  have htne : t k ≠ 0 := htk.ne'
  refine willowBeta_eq_sqrt_div ?_ htk ?_
  · have h1 : 1 + (t (k + 1) - t k) / t k = t (k + 1) / t k := by
      rw [add_div_eq_mul_add_div 1 _ htne, one_mul]
      congr 1
      ring
    rw [h1]
    exact div_pos htk1 htk
  · rw [add_mul, one_mul, div_mul_cancel₀ _ htne]
    ring

variable {n : ℕ}

/-- **The willow tree moment constraints** on a family of transition matrices `P k` over
a fixed node set `z`: each matrix is row stochastic, and its rows have the form of the
first two conditional moments of the standardized Brownian pair with correlation `β k`.
No non-negativity is required of the entries — the moment statements below are
insensitive to it (it is the linear program's business, not the induction's) — so with
sign-free entries the rows are satisfiable at `|β k| > 1` too; that `β k` is a genuine
correlation for a given step needs a non-negative row (`WillowMomentConstraints.sq_le_one`). -/
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
  | k + 1 => fun j ↦ ∑ i, willowMarginal P q k i * P k i j

@[simp] theorem willowMarginal_zero : willowMarginal P q 0 = q := rfl

@[simp] theorem willowMarginal_succ (k : ℕ) :
    willowMarginal P q (k + 1) = fun j ↦ ∑ i, willowMarginal P q k i * P k i j := rfl

/-- Rolling the weighted rows of one willow transition matrix up against a test
vector: the marginal-weighted column sums equal the weighted row pairings. -/
private theorem willowMarginal_roll (P : ℕ → Fin n → Fin n → ℝ) (q : Fin n → ℝ) (k : ℕ)
    (h : Fin n → ℝ) :
    ∑ j, (∑ i, willowMarginal P q k i * P k i j) * h j
      = ∑ i, willowMarginal P q k i * ∑ j, P k i j * h j := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum Finset.univ (fun j ↦ P k i j * h j) (willowMarginal P q k i)]
  exact Finset.sum_congr rfl fun j _ ↦ mul_assoc _ _ _

/-- The next marginal has total mass `1` as soon as the current one does. -/
theorem willowMarginal_mass_succ (hP : WillowMomentConstraints z β P) (k : ℕ)
    (h : ∑ i, willowMarginal P q k i = 1) :
    ∑ j, willowMarginal P q (k + 1) j = 1 := by
  have h1 : ∑ j, (∑ i, willowMarginal P q k i * P k i j)
      = ∑ j, (∑ i, willowMarginal P q k i * P k i j) * 1 :=
    Finset.sum_congr rfl fun j _ ↦ (mul_one _).symm
  have h2 (i : Fin n) : ∑ j, P k i j * 1 = 1 := by
    rw [Finset.sum_congr rfl fun j _ ↦ mul_one (P k i j)]
    exact hP.rowStochastic k i
  simp only [willowMarginal_succ]
  rw [h1, willowMarginal_roll P q k (fun _ ↦ (1 : ℝ))]
  rw [Finset.sum_congr rfl fun i _ ↦ by rw [h2 i, mul_one]]
  simp only [h]

/-- **Mass preservation**: a chain started at a unit-mass marginal `q` (`hq`) keeps
total mass `1` at every step, for any family of transition matrices satisfying the row
constraints (bundled as `WillowMomentConstraints`; the proof uses only row
stochasticity). -/
theorem willowMarginal_mass (hP : WillowMomentConstraints z β P) (hq : ∑ i, q i = 1) (k : ℕ) :
    ∑ j, willowMarginal P q k j = 1 := by
  induction k with
  | zero => exact hq
  | succ k ih => exact willowMarginal_mass_succ hP k ih

/-- The next marginal's first moment is `β k` times the current one. -/
theorem willowMarginal_mean_succ (hP : WillowMomentConstraints z β P) (k : ℕ) :
    ∑ j, willowMarginal P q (k + 1) j * z j = β k * ∑ i, willowMarginal P q k i * z i := by
  simp only [willowMarginal_succ]
  rw [willowMarginal_roll P q k z]
  refine (Finset.sum_congr rfl fun i _ ↦ by rw [hP.mean k i]).trans ?_
  have h2 : ∑ i, willowMarginal P q k i * (β k * z i)
      = ∑ i, β k * (willowMarginal P q k i * z i) :=
    Finset.sum_congr rfl fun i _ ↦ mul_left_comm _ _ _
  rw [h2, Finset.mul_sum]

/-- The next marginal's second moment is `β k ^ 2` times the current one, plus the
standardized Brownian increment variance `(1 - β k ^ 2)` times the current mass. -/
theorem willowMarginal_secondMoment_succ (hP : WillowMomentConstraints z β P) (k : ℕ) :
    ∑ j, willowMarginal P q (k + 1) j * z j ^ 2
      = β k ^ 2 * ∑ i, willowMarginal P q k i * z i ^ 2
        + (1 - β k ^ 2) * ∑ i, willowMarginal P q k i := by
  simp only [willowMarginal_succ]
  rw [willowMarginal_roll P q k (fun j ↦ z j ^ 2)]
  have h2 : ∑ i, willowMarginal P q k i * ∑ j, P k i j * z j ^ 2
      = ∑ i, willowMarginal P q k i * (β k ^ 2 * z i ^ 2 + (1 - β k ^ 2)) :=
    Finset.sum_congr rfl fun i _ ↦ by rw [hP.secondMoment k i]
  have hsplit : ∑ i, willowMarginal P q k i * (β k ^ 2 * z i ^ 2 + (1 - β k ^ 2))
      = ∑ i, (willowMarginal P q k i * (β k ^ 2 * z i ^ 2)
        + willowMarginal P q k i * (1 - β k ^ 2)) :=
    Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h2, hsplit, Finset.sum_add_distrib]
  have hpull1 : ∑ i, willowMarginal P q k i * (β k ^ 2 * z i ^ 2)
      = β k ^ 2 * ∑ i, willowMarginal P q k i * z i ^ 2 := by
    have h3 : ∑ i, willowMarginal P q k i * (β k ^ 2 * z i ^ 2)
        = ∑ i, β k ^ 2 * (willowMarginal P q k i * z i ^ 2) :=
      Finset.sum_congr rfl fun i _ ↦ mul_left_comm _ _ _
    rw [h3, Finset.mul_sum]
  have hpull2 : ∑ i, willowMarginal P q k i * (1 - β k ^ 2)
      = (1 - β k ^ 2) * ∑ i, willowMarginal P q k i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hpull1, hpull2]

/-- **Mean propagation**: a willow chain started at a mean-zero marginal keeps mean zero
at every step, for any family of transition matrices satisfying the row constraints
(the proof uses only the conditional first moment constraint). No marginal constraint
and no non-negativity are needed. -/
theorem willowMarginal_mean (hP : WillowMomentConstraints z β P)
    (hq0 : ∑ i, q i * z i = 0) (k : ℕ) :
    ∑ j, willowMarginal P q k j * z j = 0 := by
  induction k with
  | zero => exact hq0
  | succ k ih => rw [willowMarginal_mean_succ hP k, ih, mul_zero]

/-- **Second-moment propagation**: a willow chain started at a marginal of unit mass
and unit second moment (`hq`, `hq2`) keeps unit second moment at every step, for any
family of transition matrices satisfying the row constraints (the proof uses the
conditional second moment constraint for the recursion and row stochasticity — via
`willowMarginal_mass` — for the unit mass its constant term is weighted by). This is
the variance-on-track induction: combined with the scaling `√(t k)` it
keeps the chain's marginal second moment at `t k` (`willowScaled_secondMoment`) — its
variance too, under `willowMarginal_mean`'s mean-zero start. -/
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
its de-correlation coefficient, `E[Z_k Z_{k+1}] = β k`. The proof uses all three row
constraints: the first-moment row collapses the inner sum to `β k * z i`, and the
propagated unit second moment (`willowMarginal_secondMoment`) closes it. -/
theorem willowMarginal_crossMoment (hP : WillowMomentConstraints z β P)
    (hq : ∑ i, q i = 1) (hq2 : ∑ i, q i * z i ^ 2 = 1) (k : ℕ) :
    ∑ i, willowMarginal P q k i * z i * ∑ j, P k i j * z j = β k := by
  calc ∑ i, willowMarginal P q k i * z i * ∑ j, P k i j * z j
      = ∑ i, willowMarginal P q k i * z i * (β k * z i) :=
        Finset.sum_congr rfl fun i _ ↦ by rw [hP.mean k i]
    _ = β k * ∑ i, willowMarginal P q k i * z i ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = β k := by rw [willowMarginal_secondMoment hP hq hq2, mul_one]

/-- **The scaled chain's second moment**: in the unstandardized variables
`X k = √(t k) * Z k` on a willow chain started at a marginal of unit mass and unit
second moment (`hq`, `hq2` — the recursion weights the increment variance by the mass),
the marginal second moment at step `k` is `t k` — the Brownian marginal variance at the
grid time.
(It is the variance as well whenever the marginal mean is zero, which
`willowMarginal_mean` gives under its own hypotheses.) -/
theorem willowScaled_secondMoment (hP : WillowMomentConstraints z β P)
    (hq : ∑ i, q i = 1) (hq2 : ∑ i, q i * z i ^ 2 = 1)
    (t : ℕ → ℝ) (k : ℕ) (ht : 0 ≤ t k) :
    ∑ j, willowMarginal P q k j * (√(t k) * z j) ^ 2 = t k := by
  have hpow (j : Fin n) : (√(t k) * z j) ^ 2 = t k * z j ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ht]
  calc ∑ j, willowMarginal P q k j * (√(t k) * z j) ^ 2
      = ∑ j, willowMarginal P q k j * (t k * z j ^ 2) :=
        Finset.sum_congr rfl fun j _ ↦ by rw [hpow j]
    _ = t k * ∑ j, willowMarginal P q k j * z j ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ mul_left_comm _ _ _
    _ = t k := by rw [willowMarginal_secondMoment hP hq hq2, mul_one]

/-- **The scaled chain's cross moment**: on a willow chain started at a marginal of
unit mass and unit second moment (`hq`, `hq2`), in the unstandardized variables
`X k = √(t k) * Z k` with the chain's own
coefficient tied to the grid by `hβ : β k = √(t k / t (k+1))`, the cross moment across
the step `[t k, t (k+1)]` is `E[X_k X_{k+1}] = t k` — exactly the Brownian covariance
at two grid times, which is the de-correlation property Curran's constraint system
encodes. -/
theorem willowScaled_crossMoment (hP : WillowMomentConstraints z β P)
    (hq : ∑ i, q i = 1) (hq2 : ∑ i, q i * z i ^ 2 = 1)
    (t : ℕ → ℝ) (k : ℕ) (ht : 0 ≤ t k) (ht1 : 0 < t (k + 1))
    (hβ : β k = √(t k / t (k + 1))) :
    ∑ i, willowMarginal P q k i * (√(t k) * z i) * ∑ j, P k i j * (√(t (k + 1)) * z j)
      = t k := by
  have hinner (i : Fin n) : ∑ j, P k i j * (√(t (k + 1)) * z j)
      = √(t (k + 1)) * (β k * z i) := by
    have hterm (j : Fin n) : P k i j * (√(t (k + 1)) * z j)
        = √(t (k + 1)) * (P k i j * z j) := by ring
    simp only [hterm]
    rw [← Finset.mul_sum, hP.mean k i]
  calc ∑ i, willowMarginal P q k i * (√(t k) * z i) * ∑ j, P k i j * (√(t (k + 1)) * z j)
      = ∑ i, willowMarginal P q k i * (√(t k) * z i) * (√(t (k + 1)) * (β k * z i)) :=
        Finset.sum_congr rfl fun i _ ↦ by rw [hinner i]
    _ = ∑ i, (√(t k) * β k * √(t (k + 1))) * (willowMarginal P q k i * z i ^ 2) :=
        Finset.sum_congr rfl fun i _ ↦ by ring
    _ = √(t k) * β k * √(t (k + 1)) * ∑ i, willowMarginal P q k i * z i ^ 2 := by
        rw [Finset.mul_sum]
    _ = t k := by
        rw [hβ, willowMarginal_secondMoment hP hq hq2, mul_one,
          Real.sqrt_div' _ ht1.le, mul_div_assoc', Real.mul_self_sqrt ht,
          div_mul_cancel₀ _ (Real.sqrt_ne_zero'.mpr ht1)]

/-- **The chain's cross moment is the construction's own coefficient**: the
standardized cross moment across one step is `willowBeta ((t (k+1) - t k) / t k)` — the
two halves of the file (the `willowBeta` identity and the moment-constrained chain)
join here. The chain's own coefficient `β k` is tied to the grid by the hypothesis
`hβ : β k = √(t k / t (k+1))`; with it, the identity lemma re-expresses the grid side
and the cross-moment theorem the chain side. -/
theorem willowMarginal_crossMoment_eq_willowBeta (hP : WillowMomentConstraints z β P)
    (hq : ∑ i, q i = 1) (hq2 : ∑ i, q i * z i ^ 2 = 1)
    (t : ℕ → ℝ) (k : ℕ) (ht0 : 0 < t k) (ht1 : 0 < t (k + 1))
    (hβ : β k = √(t k / t (k + 1))) :
    ∑ i, willowMarginal P q k i * z i * ∑ j, P k i j * z j
      = willowBeta ((t (k + 1) - t k) / t k) := by
  rw [willowBeta_eq_sqrt_div' k ht0 ht1, ← hβ]
  exact willowMarginal_crossMoment hP hq hq2 k

/-- **Feasibility of the de-correlation coefficient**: if a willow transition row is an
honest probability row (non-negative entries summing to one), then `β k ^ 2 ≤ 1` — the
coefficient is a bona fide correlation. By Cauchy–Schwarz on the row the conditional
second moment dominates the squared conditional mean; substituting the two moment rows
then gives `1 - β k ^ 2 ≥ 0`. This is the lattice-side analogue of
`sq_le_one_of_covariance_unit` for a correlated Gaussian pair. -/
theorem WillowMomentConstraints.sq_le_one (hP : WillowMomentConstraints z β P) (k : ℕ) (i : Fin n)
    (hrow : ∀ j, 0 ≤ P k i j) :
    β k ^ 2 ≤ 1 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin n ↦ √(P k i j) * z j) (fun j : Fin n ↦ √(P k i j))
  have hL : ∑ j : Fin n, (√(P k i j) * z j) * √(P k i j)
      = ∑ j : Fin n, P k i j * z j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_assoc, mul_comm (z j) (√(P k i j)), ← mul_assoc, Real.mul_self_sqrt (hrow j)]
  have hR1 : ∑ j : Fin n, (√(P k i j) * z j) ^ 2 = ∑ j : Fin n, P k i j * z j ^ 2 :=
    Finset.sum_congr rfl fun j _ ↦ by rw [mul_pow, Real.sq_sqrt (hrow j)]
  have hR2 : ∑ j : Fin n, (√(P k i j)) ^ 2 = ∑ j : Fin n, P k i j :=
    Finset.sum_congr rfl fun j _ ↦ Real.sq_sqrt (hrow j)
  rw [hL, hR1, hR2, hP.mean k i] at hcs
  have hsq : (β k * z i) ^ 2 = β k ^ 2 * z i ^ 2 := by ring
  rw [hsq, hP.secondMoment k i, hP.rowStochastic k i, mul_one] at hcs
  linarith

/-- **The willow coefficient is a valid correlation, and the bivariate normal law at
it is standard**: an honest transition row forces `β k ^ 2 ≤ 1`, and for a coefficient
in that range the standard bivariate normal law `bivariateNormalLaw (β k)` has unit
variances and covariance `β k`. (The chain's own moments matching that law's is proved
separately, entrywise: `willowMarginal_crossMoment` gives the cross moment `β k`.) -/
theorem WillowMomentConstraints.bivariateNormal_moments (hP : WillowMomentConstraints z β P) (k : ℕ)
    (i : Fin n) (hrow : ∀ j, 0 ≤ P k i j) :
    β k ^ 2 ≤ 1
      ∧ Var[(Prod.fst : ℝ × ℝ → ℝ); bivariateNormalLaw (β k)] = 1
      ∧ Var[(Prod.snd : ℝ × ℝ → ℝ); bivariateNormalLaw (β k)] = 1
      ∧ cov[Prod.fst, Prod.snd; bivariateNormalLaw (β k)] = β k :=
  have h := hP.sq_le_one k i hrow
  ⟨h, variance_fst_bivariateNormalLaw h, variance_snd_bivariateNormalLaw _,
    covariance_fst_snd_bivariateNormalLaw _⟩

/-! ### The chain against a Brownian motion

The moments the scaled chain reproduces are those of a pre-Brownian motion `W` read at the grid
times: `E[W_s W_t] = min s t` (`WienerIntegralL2.integral_mul_eval`). -/

variable {Ω : Type*} [MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω}

/-- **The scaled chain's second moment is the Brownian one**: for a pre-Brownian motion `W`
and a willow chain started at a marginal of unit mass and unit second moment, the second moment of
`X k = √(t k) Z k` is `E[W_{t k}²]`. -/
theorem willowScaled_secondMoment_eq_integral_sq [IsProbabilityMeasure μ]
    (hP : WillowMomentConstraints z β P) (hq : ∑ i, q i = 1) (hq2 : ∑ i, q i * z i ^ 2 = 1)
    (hW : IsPreBrownianReal W μ) (t : ℕ → ℝ≥0) (k : ℕ) :
    ∑ j, willowMarginal P q k j * (√(t k : ℝ) * z j) ^ 2 = ∫ ω, W (t k) ω ^ 2 ∂μ := by
  rw [willowScaled_secondMoment hP hq hq2 (fun k ↦ (t k : ℝ)) k (t k).2]
  simpa [sq] using (WienerIntegralL2.integral_mul_eval hW (t k) (t k)).symm

/-- **The scaled chain's cross moment is the Brownian one**: on an increasing grid with
`t (k+1) > 0` and the chain's coefficient tied to it by `β k = √(t k / t (k+1))`, the cross moment
of `X k`, `X (k+1)` is `E[W_{t k} W_{t (k+1)}]`. -/
theorem willowScaled_crossMoment_eq_integral_mul [IsProbabilityMeasure μ]
    (hP : WillowMomentConstraints z β P) (hq : ∑ i, q i = 1) (hq2 : ∑ i, q i * z i ^ 2 = 1)
    (hW : IsPreBrownianReal W μ) (t : ℕ → ℝ≥0) (k : ℕ) (hk : t k ≤ t (k + 1))
    (ht1 : 0 < (t (k + 1) : ℝ)) (hβ : β k = √((t k : ℝ) / t (k + 1))) :
    ∑ i, willowMarginal P q k i * (√(t k : ℝ) * z i)
        * ∑ j, P k i j * (√(t (k + 1) : ℝ) * z j)
      = ∫ ω, W (t k) ω * W (t (k + 1)) ω ∂μ := by
  rw [willowScaled_crossMoment hP hq hq2 (fun k ↦ (t k : ℝ)) k (t k).2 ht1 hβ,
    WienerIntegralL2.integral_mul_eval hW, min_eq_left hk]

end MathFin
