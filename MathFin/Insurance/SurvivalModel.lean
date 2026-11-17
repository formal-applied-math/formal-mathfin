/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
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
* `survive_lifeTable` — a finite life table induces the conditional survival ratios
  `l_{x+k} / l_x` under its finite-weights probability law.

## References

* [Y. Ito, *AFP Actuarial Mathematics*][ItoAFPActuarial]

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

theorem lifeTableWeights_nonneg (n : ℕ) (l : ℕ → ℝ) (hl0 : 0 < l 0)
    (hmono : ∀ k < n, l (k + 1) ≤ l k) (hnonneg : ∀ k ≤ n, 0 ≤ l k)
    (i : Fin (n + 1)) : 0 ≤ lifeTableWeights n l i := by
  unfold lifeTableWeights
  by_cases h : i.val < n
  · rw [ite_eq_left h]
    exact div_nonneg (sub_nonneg.mpr (hmono i.val h)) (le_of_lt hl0)
  · rw [ite_eq_right h]
    exact div_nonneg (hnonneg n le_rfl) (le_of_lt hl0)

theorem lifeTableWeights_sum (n : ℕ) (l : ℕ → ℝ) (hl0 : 0 < l 0) :
    ∑ i : Fin (n + 1), lifeTableWeights n l i = 1 := by
  have hl0' : l 0 ≠ 0 := ne_of_gt hl0
  have hrange : (∑ i : Fin (n + 1), lifeTableWeights n l i)
      = ∑ k ∈ Finset.range (n + 1),
        (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0) :=
    Fin.sum_univ_eq_sum_range
      (fun k => if k < n then (l k - l (k + 1)) / l 0 else l n / l 0) (n + 1)
  have hsplit : (∑ k ∈ Finset.range (n + 1),
        (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0))
      = (∑ k ∈ Finset.range n, (l k - l (k + 1)) / l 0) + l n / l 0 := by
    have h1 : (∑ k ∈ Finset.range (n + 1),
          (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0))
        = (∑ k ∈ Finset.range n,
            (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0))
          + (if n < n then (l n - l (n + 1)) / l 0 else l n / l 0) :=
      Finset.sum_range_succ
        (fun k => if k < n then (l k - l (k + 1)) / l 0 else l n / l 0) n
    have h2 : (∑ k ∈ Finset.range n,
          (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0))
        = ∑ k ∈ Finset.range n, (l k - l (k + 1)) / l 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ite_eq_left (Finset.mem_range.mp hk)]
    have h3 : (if n < n then (l n - l (n + 1)) / l 0 else l n / l 0)
        = l n / l 0 :=
      ite_eq_right (by omega : ¬n < n)
    rw [h1, h2, h3]
  have htele : (∑ k ∈ Finset.range n, (l k - l (k + 1)) / l 0)
      = (l 0 - l n) / l 0 := by
    have hdiv : (∑ k ∈ Finset.range n, (l k - l (k + 1)) / l 0)
        = (∑ k ∈ Finset.range n, (l k - l (k + 1))) / l 0 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
    have hts : (∑ k ∈ Finset.range n, (l k - l (k + 1))) = l 0 - l n :=
      Finset.sum_range_sub' l n
    rw [hdiv, hts]
  rw [hrange, hsplit, htele, ← add_div, sub_add_cancel, div_self hl0']

/-- The finite probability law of a life table, by the existing
finite-weights constructor on all outcomes. -/
noncomputable def lifeTableMeasure (n : ℕ) (l : ℕ → ℝ) : Measure (Fin (n + 1)) :=
  MeasureTheory.Measure.ofWeights Finset.univ (lifeTableWeights n l)

/-- Representative lifetime of a life-table outcome: death cell `i` at
`i + 1`, residual survivor outcome at `n + 1`. -/
def lifeTableLifetime (n : ℕ) (i : Fin (n + 1)) : ℝ := i.val + 1

/-- Survival function of the life-table law at an observed date: the mass of
outcomes outliving `m` telescopes to `l m / l 0`. -/
private theorem lifeTable_survivalFunction_eq (n : ℕ) (l : ℕ → ℝ) (hl0 : 0 < l 0)
    (hmono : ∀ k < n, l (k + 1) ≤ l k) (hnonneg : ∀ k ≤ n, 0 ≤ l k)
    (m : ℕ) (hm : m ≤ n) :
    survivalFunction (lifeTableMeasure n l) (lifeTableLifetime n) (m : ℝ)
      = l m / l 0 := by
  classical
  have hmeas : Measurable (lifeTableLifetime n) := by
    apply measurable_of_finite
  have hμ : (lifeTableMeasure n l) (alive (lifeTableLifetime n) (m : ℝ))
      = ∑ a ∈ Finset.univ.filter (· ∈ alive (lifeTableLifetime n) (m : ℝ)),
        ENNReal.ofReal (lifeTableWeights n l a) := by
    have hA : MeasurableSet (alive (lifeTableLifetime n) (m : ℝ)) :=
      measurableSet_alive hmeas _
    simp only [lifeTableMeasure, MeasureTheory.Measure.ofWeights,
      MeasureTheory.Measure.finsetSum_apply]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ alive (lifeTableLifetime n) (m : ℝ)
    · rw [MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.dirac_apply_of_mem hi, smul_eq_mul, mul_one,
        ite_eq_left hi]
    · rw [MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.dirac_apply' i hA, Set.indicator_of_notMem hi,
        smul_eq_mul, mul_zero, ite_eq_right hi]
  have hF : Finset.univ.filter (· ∈ alive (lifeTableLifetime n) (m : ℝ))
      = Finset.univ.filter (fun a : Fin (n + 1) => m ≤ a.val) := by
    rw [Finset.ext_iff]
    intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [alive, lifeTableLifetime, Set.mem_ofPred]
    constructor
    · intro h
      have h' : m < a.val + 1 := by exact_mod_cast h
      omega
    · intro h
      have h' : m < a.val + 1 := by omega
      exact_mod_cast h'
  have hnn : ∀ a ∈ Finset.univ.filter (· ∈ alive (lifeTableLifetime n) (m : ℝ)),
      0 ≤ lifeTableWeights n l a := by
    intro a _
    exact lifeTableWeights_nonneg n l hl0 hmono hnonneg a
  have hbridge : ENNReal.ofReal
        (∑ a ∈ Finset.univ.filter (· ∈ alive (lifeTableLifetime n) (m : ℝ)),
          lifeTableWeights n l a)
      = ∑ a ∈ Finset.univ.filter (· ∈ alive (lifeTableLifetime n) (m : ℝ)),
        ENNReal.ofReal (lifeTableWeights n l a) := by
    apply ENNReal.ofReal_sum_of_nonneg
    intro a ha
    exact hnn a ha
  have htr : (ENNReal.ofReal
        (∑ a ∈ Finset.univ.filter (· ∈ alive (lifeTableLifetime n) (m : ℝ)),
          lifeTableWeights n l a)).toReal
      = ∑ a ∈ Finset.univ.filter (· ∈ alive (lifeTableLifetime n) (m : ℝ)),
        lifeTableWeights n l a := by
    apply ENNReal.toReal_ofReal
    exact Finset.sum_nonneg (fun a ha => hnn a ha)
  have hfilt : (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) => m ≤ a.val),
        lifeTableWeights n l a)
      = ∑ a ∈ Finset.univ,
        (if m ≤ a.val then lifeTableWeights n l a else 0) :=
    Finset.sum_filter (fun a : Fin (n + 1) => m ≤ a.val) (lifeTableWeights n l)
  have hrange : (∑ a ∈ Finset.univ,
        (if m ≤ a.val then lifeTableWeights n l a else 0))
      = ∑ k ∈ Finset.range (n + 1),
        (if m ≤ k then (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0)
          else 0) :=
    Fin.sum_univ_eq_sum_range
      (fun k => if m ≤ k then (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0)
        else 0) (n + 1)
  have hIco : (Finset.range (n + 1)).filter (fun k : ℕ => m ≤ k)
      = Finset.Ico m (n + 1) := by
    rw [Finset.ext_iff]
    intro k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact and_comm
  have hfilt2 : (∑ k ∈ Finset.range (n + 1),
        (if m ≤ k then (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0)
          else 0))
      = ∑ k ∈ Finset.Ico m (n + 1),
        (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0) := by
    rw [← hIco, Finset.sum_filter]
  have hsplit : (∑ k ∈ Finset.Ico m (n + 1),
        (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0))
      = (∑ k ∈ Finset.Ico m n, (l k - l (k + 1)) / l 0) + l n / l 0 := by
    have h1 : (∑ k ∈ Finset.Ico m (n + 1),
          (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0))
        = (∑ k ∈ Finset.Ico m n,
            (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0))
          + (if n < n then (l n - l (n + 1)) / l 0 else l n / l 0) := by
      apply Finset.sum_Ico_succ_top
      exact hm
    have h2 : (∑ k ∈ Finset.Ico m n,
          (if k < n then (l k - l (k + 1)) / l 0 else l n / l 0))
        = ∑ k ∈ Finset.Ico m n, (l k - l (k + 1)) / l 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ite_eq_left (Finset.mem_Ico.mp hk).2]
    have h3 : (if n < n then (l n - l (n + 1)) / l 0 else l n / l 0)
        = l n / l 0 :=
      ite_eq_right (by omega : ¬n < n)
    rw [h1, h2, h3]
  have htele : (∑ k ∈ Finset.Ico m n, (l k - l (k + 1)) / l 0)
      = (l m - l n) / l 0 := by
    have hdiv : (∑ k ∈ Finset.Ico m n, (l k - l (k + 1)) / l 0)
        = (∑ k ∈ Finset.Ico m n, (l k - l (k + 1))) / l 0 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
    have hts : (∑ k ∈ Finset.Ico m n, (l k - l (k + 1))) = l m - l n := by
      rw [Finset.sum_Ico_eq_sub _ hm, Finset.sum_range_sub' _ n,
        Finset.sum_range_sub' _ m]
      ring
    rw [hdiv, hts]
  unfold survivalFunction
  rw [hμ, ← hbridge, htr, hF, hfilt, hrange, hfilt2, hsplit, htele, ← add_div,
    sub_add_cancel]

theorem survive_lifeTable (n : ℕ) (l : ℕ → ℝ) (hl0 : 0 < l 0)
    (hmono : ∀ k < n, l (k + 1) ≤ l k) (hnonneg : ∀ k ≤ n, 0 ≤ l k)
    (x k : ℕ) (hxk : x + k ≤ n) (_hx : 0 < l x) :
    survive (lifeTableMeasure n l) (lifeTableLifetime n) (k : ℝ) (x : ℝ)
      = l (x + k) / l x := by
  have hmeas : Measurable (lifeTableLifetime n) := by
    apply measurable_of_finite
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hx_le : x ≤ n := Nat.le_trans (Nat.le_add_right x k) hxk
  have hl0' : l 0 ≠ 0 := ne_of_gt hl0
  have hx' : l x ≠ 0 := ne_of_gt _hx
  rw [survive_eq_survivalFunction_ratio hmeas _ hk0, ← Nat.cast_add,
    lifeTable_survivalFunction_eq n l hl0 hmono hnonneg (x + k) hxk,
    lifeTable_survivalFunction_eq n l hl0 hmono hnonneg x hx_le]
  field_simp

end MathFin.SurvivalModel
