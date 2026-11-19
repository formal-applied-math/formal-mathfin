/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Adam Kiezun
-/

/-
The definitions and proofs here are our own, following this library's conventions: Mathlib's
`MeasureTheory`/`ProbabilityTheory`, a concrete complementary-CDF survival function, and the
conditional measure `cond`. Yosuke Ito's Isabelle/HOL AFP entry "Actuarial Mathematics"
(https://isa-afp.org/entries/Actuarial_Mathematics.html, BSD License) — in particular its
`Survival_Model` theory — was consulted as a source for the classical result set, and is cited
here with thanks and with the author's kind permission.
-/
module

public import MathFin.Init
public import MathFin.Probability.Laws.FiniteWeights
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.ConditionalProbability

/-!
# The survival model: age-at-death random variable and conditional survival

The probabilistic foundation of life-contingent actuarial mathematics. A life is described by a
random variable `X : Ω → ℝ`, its **age at death**, on a probability space `(Ω, P)`, with `X > 0`
almost surely. Everything else is derived from the **survival function** (complementary CDF)
`S_X(t) = P(X > t)`.

The design is ours (see the file header); the classical statements were cross-checked against
Yosuke Ito's AFP `Survival_Model`, cited as a source.

The future lifetime of a life aged `x` is `T(x) = X − x`, defined on the event `alive x = {X > x}`
that the life reaches age `x`. Its survival function is the conditional probability
`tpₓ = P(X > x + t ∣ X > x)`, which for `t ≥ 0` collapses to the survival ratio
`tpₓ = S_X(x + t) / S_X(x)` — the keystone of the theory.

## Correspondence with the AFP source (cross-reference only)

For readers coming from the AFP entry, our declarations line up with its `Survival_Model` names:
`alive`↔`alive`, `futureLifetime`↔`futr_life`, `survivalFunction`↔`ccdf (distr 𝔐 borel X)`,
`survive`↔`survive` (`$p_{t&x}`), `die`↔`die` (`$q_{t&x}`), `survivalFunction_zero`↔`ccdfX_0_1`,
`survive_zero`↔`ccdfTx_0_1`, `survive_eq_survivalFunction_ratio`↔`ccdfTx_ccdfX`.

## Main definitions

* `alive`: the event `{X > x}` that a life with age at death `X` reaches age `x`.
* `futureLifetime`: the future lifetime `T(x) = X − x` of a life aged `x`.
* `survivalFunction`: the survival function `S_X(t) = P(X > t)`.
* `survive`: the probability `tpₓ = P(X > x + t ∣ X > x)` that a life aged `x` survives `t` more
  years.
* `die`: the probability `tqₓ = 1 − tpₓ` that a life aged `x` dies within `t` years.
* `lifeTableWeights`: the death-cell and residual weights of a finite life table.
* `lifeTableMeasure`: the finite probability law of a life table.
* `lifeTableLifetime`: the representative lifetime of a life-table outcome (cell `i` at
  `i + 1`, residual at `n + 1`).

## Main results

* `survivalFunction_zero` — `S_X(0) = 1` (`X > 0` a.e.).
* `survivalFunction_antitone`, `survivalFunction_le_one` — the survival function decreases in
  `[0, 1]`.
* `survive_zero` — `₀pₓ = 1` for a life alive at `x`.
* `survive_eq_survivalFunction_ratio` — `tpₓ = S_X(x+t) / S_X(x)` for `t ≥ 0`, the survival-ratio
  keystone: the conditional-probability definition of `survive` collapses to the ratio.
* `real_le_eq_one_sub_survivalFunction` — `P(X ≤ t) = 1 - S_X(t)`.
* `survivalFunction_lifeTable` — under the life-table law, `S(m) = l m / l 0` at the observed dates
  `m ≤ n`.
* `survive_lifeTable` — a finite life table induces the conditional survival ratios
  `l_{x+k} / l_x` under its finite-weights probability law.

## References

* [Y. Ito, *AFP Actuarial Mathematics*][ItoAFPActuarial]
* [D. C. M. Dickson, M. R. Hardy and H. R. Waters, *Actuarial Mathematics for Life
  Contingent Risks*][DicksonHardyWaters2013], Chapter 3 (life tables)

## Tags

age at death, future lifetime, survival function, life table, conditional survival, life-contingent,
MSC 91G05, MSC 62P05, JEL G22
-/

@[expose] public section

namespace MathFin.SurvivalModel

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- `alive x` — the event that a life reaches age `x`, i.e. `{ω | x < X ω}`. AFP: `alive`. -/
def alive (X : Ω → ℝ) (x : ℝ) : Set Ω := {ω | x < X ω}

/-- The future lifetime `T(x) = X − x` of a life aged `x`. AFP: `futr_life` (`T`). -/
def futureLifetime (X : Ω → ℝ) (x : ℝ) : Ω → ℝ := fun ω ↦ X ω - x

/-- The **survival function** `S_X(t) = P(X > t)` — the complementary CDF of the age at death.
AFP: `ccdf (distr 𝔐 borel X)`. -/
noncomputable def survivalFunction (P : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  (P (alive X t)).toReal

/-- `tpₓ` — the probability `P(X > x + t ∣ X > x)` that a life aged `x` survives a further `t`
years. AFP: `survive` — the ccdf of the future lifetime `T(x)` under the measure conditioned on
`alive x`. -/
noncomputable def survive (P : Measure Ω) (X : Ω → ℝ) (t x : ℝ) : ℝ :=
  ((P[|alive X x]) (alive X (x + t))).toReal

/-- `tqₓ = 1 − tpₓ` — the probability that a life aged `x` dies within `t` years. AFP: `die`. -/
noncomputable def die (P : Measure Ω) (X : Ω → ℝ) (t x : ℝ) : ℝ :=
  1 - survive P X t x

lemma measurableSet_alive (hX : Measurable X) (x : ℝ) : MeasurableSet (alive X x) :=
  measurableSet_lt measurable_const hX

omit [MeasurableSpace Ω] in
/-- `alive x` shrinks as `x` grows: reaching a later age is a sub-event. -/
lemma alive_subset_alive {x y : ℝ} (hxy : x ≤ y) : alive X y ⊆ alive X x :=
  fun _ hω ↦ lt_of_le_of_lt hxy hω

/-- `S_X(0) = 1`: everyone is alive at age `0`, since `X > 0` almost surely. AFP: `ccdfX_0_1`. -/
lemma survivalFunction_zero [IsProbabilityMeasure P] (hpos : ∀ᵐ ω ∂P, 0 < X ω) :
    survivalFunction P X 0 = 1 := by
  have hcompl : P (alive X 0)ᶜ = 0 := measure_mono_null (fun _ hω ↦ hω) (ae_iff.mp hpos)
  have h1 : P (alive X 0) = 1 := by
    rw [← measure_univ (μ := P)]
    exact measure_congr (ae_eq_univ.mpr hcompl)
  rw [survivalFunction, h1, ENNReal.toReal_one]

/-- `P(X ≤ t) = 1 - S_X(t)`: the survival function is the complement of the distribution function
of the age at death. -/
lemma real_le_eq_one_sub_survivalFunction [IsProbabilityMeasure P] (hX : Measurable X) (t : ℝ) :
    P.real {ω | X ω ≤ t} = 1 - survivalFunction P X t := by
  have h : alive X t = {ω | X ω ≤ t}ᶜ := by
    ext ω
    simp [alive]
  rw [survivalFunction, h, ← measureReal_def,
    probReal_compl_eq_one_sub (measurableSet_le hX measurable_const)]
  ring

/-- The survival function is bounded by `1`. -/
lemma survivalFunction_le_one [IsProbabilityMeasure P] (t : ℝ) :
    survivalFunction P X t ≤ 1 := by
  rw [survivalFunction, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

/-- The survival function is nonnegative. -/
lemma survivalFunction_nonneg (t : ℝ) : 0 ≤ survivalFunction P X t :=
  ENNReal.toReal_nonneg

/-- The survival function is nonincreasing in age. -/
lemma survivalFunction_antitone [IsProbabilityMeasure P] : Antitone (survivalFunction P X) := by
  intro x y hxy
  exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (alive_subset_alive hxy))

/-- `₀pₓ = 1`: a life alive at age `x` survives `0` further years with certainty. AFP: `ccdfTx_0_1`.
-/
lemma survive_zero [IsProbabilityMeasure P] (hX : Measurable X) (x : ℝ)
    (hx : P (alive X x) ≠ 0) : survive P X 0 x = 1 := by
  rw [survive, add_zero, cond_apply (measurableSet_alive hX x), Set.inter_self,
    ENNReal.inv_mul_cancel hx (measure_ne_top P _), ENNReal.toReal_one]

/-- **The survival ratio** `tpₓ = S_X(x+t) / S_X(x)` for `t ≥ 0` — the survival-ratio keystone (AFP:
`ccdfTx_ccdfX`). Conditioning on survival to age `x`, a further `t` years of survival has
probability the ratio of the two unconditional survival probabilities. -/
lemma survive_eq_survivalFunction_ratio (hX : Measurable X) (x : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    survive P X t x = survivalFunction P X (x + t) / survivalFunction P X x := by
  have hsub : alive X (x + t) ⊆ alive X x := alive_subset_alive (le_add_of_nonneg_right ht)
  rw [survive, survivalFunction, survivalFunction, cond_apply (measurableSet_alive hX x),
    Set.inter_eq_self_of_subset_right hsub, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

/-- `tpₓ + tqₓ = 1` — the survival/death dichotomy. -/
lemma survive_add_die (t x : ℝ) : survive P X t x + die P X t x = 1 := by
  rw [die]; ring

/-! ### Finite life tables

A finite nonincreasing life table `l` with `l 0 > 0` induces a probability
law on the outcomes `Fin (n + 1)`: death cells `(i, i+1]` with mass
`(l i - l (i+1)) / l 0` and one residual survivor outcome with mass
`l n / l 0`, represented at lifetime `i + 1` (the residual at `n + 1`).
Under this law the conditional survival at observed dates is the table
ratio `l (x + k) / l x` (`survive_lifeTable`).
-/


/-- Death-cell and residual weights of a finite life table: index `i < n`
is the death cell `(i, i+1]` with mass `(l i - l (i+1)) / l 0`; index `n`
is the residual survivor outcome with mass `l n / l 0`. -/
noncomputable def lifeTableWeights (n : ℕ) (l : ℕ → ℝ) (i : Fin (n + 1)) : ℝ :=
  if i.val < n then (l i.val - l (i.val + 1)) / l 0 else l n / l 0

/-- The weights of a life table are nonnegative when `l` is nonnegative and nonincreasing. -/
theorem lifeTableWeights_nonneg (n : ℕ) (l : ℕ → ℝ) (hl0 : 0 < l 0)
    (hmono : ∀ k < n, l (k + 1) ≤ l k) (hnonneg : ∀ k ≤ n, 0 ≤ l k)
    (i : Fin (n + 1)) : 0 ≤ lifeTableWeights n l i := by
  unfold lifeTableWeights
  by_cases h : i.val < n
  · rw [ite_eq_left h]
    exact div_nonneg (sub_nonneg.mpr (hmono i.val h)) (le_of_lt hl0)
  · rw [ite_eq_right h]
    exact div_nonneg (hnonneg n le_rfl) (le_of_lt hl0)

/-- The weights of a life table sum to one: the death cells telescope to `(l 0 - l n) / l 0`
and the residual outcome carries `l n / l 0`. -/
theorem lifeTableWeights_sum (n : ℕ) (l : ℕ → ℝ) (hl0 : 0 < l 0) :
    ∑ i : Fin (n + 1), lifeTableWeights n l i = 1 := by
  simp only [lifeTableWeights]
  rw [Fin.sum_univ_eq_sum_range
    (fun k ↦ if k < n then (l k - l (k + 1)) / l 0 else l n / l 0), Finset.sum_range_succ,
    Finset.sum_congr rfl fun k hk ↦ ite_eq_left (Finset.mem_range.1 hk), ite_eq_right n.lt_irrefl,
    ← Finset.sum_div, Finset.sum_range_sub', ← add_div, sub_add_cancel, div_self hl0.ne']

/-- The finite probability law of a life table, by the existing
finite-weights constructor on all outcomes. -/
noncomputable def lifeTableMeasure (n : ℕ) (l : ℕ → ℝ) : Measure (Fin (n + 1)) :=
  MeasureTheory.Measure.ofWeights Finset.univ (lifeTableWeights n l)

/-- Representative lifetime of a life-table outcome: death cell `i` at
`i + 1`, residual survivor outcome at `n + 1`. -/
def lifeTableLifetime (n : ℕ) (i : Fin (n + 1)) : ℝ := i.val + 1

/-- **The survival function of the life-table law** at an observed date `m ≤ n` is the table
ratio `l m / l 0`: the mass of the outcomes outliving `m` telescopes. -/
theorem survivalFunction_lifeTable (n : ℕ) (l : ℕ → ℝ) (hl0 : 0 < l 0)
    (hmono : ∀ k < n, l (k + 1) ≤ l k) (hnonneg : ∀ k ≤ n, 0 ≤ l k) {m : ℕ} (hm : m ≤ n) :
    survivalFunction (lifeTableMeasure n l) (lifeTableLifetime n) m = l m / l 0 := by
  rw [survivalFunction, ← measureReal_def,
    ← integral_indicator_one (measurableSet_alive (measurable_of_finite _) _), lifeTableMeasure,
    Measure.integral_ofWeights _ fun i _ ↦ lifeTableWeights_nonneg n l hl0 hmono hnonneg i]
  have hind (i : Fin (n + 1)) :
      (alive (lifeTableLifetime n) m).indicator (1 : Fin (n + 1) → ℝ) i
        = if m ≤ i.val then 1 else 0 := by
    have h : ((m : ℝ) < (i.val : ℝ) + 1) ↔ m ≤ i.val := by exact_mod_cast Nat.lt_succ_iff
    simp [Set.indicator_apply, alive, lifeTableLifetime, h]
  simp only [hind, mul_ite, mul_one, mul_zero, lifeTableWeights]
  rw [Fin.sum_univ_eq_sum_range
    (fun k ↦ if m ≤ k then (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0) else 0),
    Finset.sum_range_succ, ite_eq_left hm, ite_eq_right n.lt_irrefl,
    Finset.sum_congr rfl fun k hk ↦
      show _ = if m ≤ k then (l k - l (k + 1)) / l 0 else 0 by simp [Finset.mem_range.1 hk],
    ← Finset.sum_filter,
    show (Finset.range n).filter (m ≤ ·) = Finset.Ico m n by ext; simp [and_comm],
    ← Finset.sum_div, Finset.sum_Ico_eq_sub _ hm, Finset.sum_range_sub', Finset.sum_range_sub',
    ← add_div]
  ring

/-- **Conditional survival in a life table**: a life aged `x` in the finite life table `l` survives
`k` more years with probability `l (x + k) / l x` under the life-table law. -/
theorem survive_lifeTable (n : ℕ) (l : ℕ → ℝ) (hl0 : 0 < l 0)
    (hmono : ∀ k < n, l (k + 1) ≤ l k) (hnonneg : ∀ k ≤ n, 0 ≤ l k)
    (x k : ℕ) (hxk : x + k ≤ n) :
    survive (lifeTableMeasure n l) (lifeTableLifetime n) k x = l (x + k) / l x := by
  rw [survive_eq_survivalFunction_ratio (measurable_of_finite _) _ k.cast_nonneg, ← Nat.cast_add,
    survivalFunction_lifeTable n l hl0 hmono hnonneg hxk,
    survivalFunction_lifeTable n l hl0 hmono hnonneg ((x.le_add_right k).trans hxk),
    div_div_div_cancel_right₀ hl0.ne']

end MathFin.SurvivalModel
