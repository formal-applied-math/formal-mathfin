/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.RiskMeasures.ValueAtRisk

/-!
# Value-at-risk and expected shortfall at a finite law

For a loss `L : ι → ℝ` on a finite state space with probability vector `q ∈ stdSimplex ℝ ι`,
value-at-risk is `VaR_α = inf {x | ∑_{L i ≤ x} q i ≥ α}` (`finiteVaR`) and expected shortfall is
the quantile average `ES_α = (1 − α)⁻¹ ∫_α^1 VaR_u du` (`finiteES`). For `α ∈ (0, 1)` these are
`valueAtRisk` and `expectedShortfall` of `RiskMeasures/ValueAtRisk.lean` at the law
`∑ i, q i • δ_i` (`finiteVaR_eq_valueAtRisk`, `finiteES_eq_expectedShortfall`), written as
`Finset` sums so that concrete laws evaluate by case analysis on the loss level.

The file works the two-bond example. A single $100 bond defaulting with probability `1/25` has
`VaR₀.₉₅ = 0`: the loss is 0 with probability `24/25 ≥ 0.95`. The same exposure split into two
$50 bonds defaulting independently has `VaR₀.₉₅ = 50`, so VaR penalises the diversified position.
At the single bond, expected shortfall is `80` while the conditional tail mean `E[L | L ≥ VaR₀.₉₅]`
is the unconditional mean `4`.

These are worked instances of general results in the library: the exact superadditivity window
for independent Bernoulli losses is `valueAtRisk_sum_bernoulli_superadditive_iff`
(`RiskMeasures/VaRSuperadditivity.lean`), and the dual representation of ES over bounded densities
is `isGreatest_integral_mul_expectedShortfall` (`RiskMeasures/ExpectedShortfall.lean`).

## Main results

* `finiteVaR_eq_valueAtRisk`, `finiteES_eq_expectedShortfall`: the finite forms agree with the
  general definitions at the law `∑ i, q i • δ_i`.
* `finiteVaR_eq_value_inf`: VaR at a finite law is attained at a loss value.
* `finiteVaR_two_point`: VaR of a loss that is `0` with mass `a` and `c > 0` with mass `1 - a`.
* `vaR_one_bond`, `vaR_two_halves`: `VaR₀.₉₅` is `0` for the single bond and `50` for the split
  position.
* `vaR_subadditivity_fails`: on the joint space of the two half-bonds, each half has
  `VaR₀.₉₅ = 0` and their sum has `VaR₀.₉₅ = 50`.
* `vaR_counterexample_window`: subadditivity fails exactly for `(24/25)² < α ≤ 24/25`.
* `es_one_bond_eq_80`: `ES₀.₉₅ = 80` for the single bond.
* `condTailMean_one_bond`: at the single bond the tail event `{L ≥ VaR₀.₉₅}` is the whole space,
  so the conditional tail mean is `E[L] = 4`.
* `es_sup_representation_finite`: for the single bond, the greatest `E[Z·L]` over densities
  `0 ≤ Z ≤ (1 − 19/20)⁻¹` with `E[Z] = 1` is `80`.
-/

@[expose] public section

namespace MathFin.DiscreteVaR

open MeasureTheory Set

/-! ## The definitions and the bridge to `valueAtRisk` -/

/-- **VaR at a finite law**: the infimum of the loss levels `x` at which the `q`-mass of
`{i | L i ≤ x}` reaches `α`. The lemmas that need `q` to be a probability vector take
`q ∈ stdSimplex ℝ ι` as a hypothesis. -/
noncomputable def finiteVaR {ι : Type*} [Fintype ι] (q L : ι → ℝ) (α : ℝ) : ℝ :=
  sInf {x | ∑ i ∈ Finset.univ.filter (L · ≤ x), q i ≥ α}

/-- **ES at a finite law**: the quantile average, `1/(1-α)` times the integral of the quantile
function `u ↦ finiteVaR q L u` over `[α, 1]`. -/
noncomputable def finiteES {ι : Type*} [Fintype ι] (q L : ι → ℝ) (α : ℝ) : ℝ :=
  (1 / (1 - α)) * ∫ u in α..1, finiteVaR q L u

/-- The law `∑ i, q i • δ_i` of a probability vector `q`. -/
noncomputable def finiteLaw {ι : Type*} [Fintype ι] [MeasurableSpace ι] (q : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (q i) • Measure.dirac i

section Bridge

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] {q : ι → ℝ}

/-- The law of a probability vector is a probability measure. -/
lemma isProbabilityMeasure_finiteLaw (hq : q ∈ stdSimplex ℝ ι) :
    IsProbabilityMeasure (finiteLaw q) := by
  refine ⟨?_⟩
  simp [finiteLaw, ← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hq.1 i, hq.2]

variable [MeasurableSingletonClass ι]

/-- Under `finiteLaw q`, the probability of `{L ≤ x}` is the tail mass in `finiteVaR`. -/
lemma finiteLaw_real_le (hq : ∀ i, 0 ≤ q i) (L : ι → ℝ) (x : ℝ) :
    (finiteLaw q).real {i | L i ≤ x} = ∑ i ∈ Finset.univ.filter (L · ≤ x), q i := by
  rw [measureReal_def, finiteLaw, Measure.coe_finsetSum, Finset.sum_apply]
  simp_rw [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum fun i _ ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hi : L i ≤ x <;> simp [Measure.dirac_apply, hi, hq i]

/-- `finiteVaR` is `valueAtRisk` at the law `∑ i, q i • δ_i`. -/
theorem finiteVaR_eq_valueAtRisk (hq : q ∈ stdSimplex ℝ ι) {L : ι → ℝ} {α : ℝ}
    (hα : α ∈ Ioo 0 1) : finiteVaR q L α = valueAtRisk L (finiteLaw q) α := by
  have := isProbabilityMeasure_finiteLaw hq
  have hset : {x | ∑ i ∈ Finset.univ.filter (L · ≤ x), q i ≥ α}
      = Ici (valueAtRisk L (finiteLaw q) α) := by
    ext x
    simp [valueAtRisk_le_iff (measurable_of_finite L).aemeasurable hα, finiteLaw_real_le hq.1]
  rw [finiteVaR, hset, csInf_Ici]

/-- `finiteES` is `expectedShortfall` at the law `∑ i, q i • δ_i`. -/
theorem finiteES_eq_expectedShortfall (hq : q ∈ stdSimplex ℝ ι) {L : ι → ℝ} {α : ℝ}
    (hα : α ∈ Ioo 0 1) : finiteES q L α = expectedShortfall L (finiteLaw q) α := by
  rw [finiteES, expectedShortfall, one_div, intervalIntegral.integral_of_le hα.2.le,
    integral_Ioc_eq_integral_Ioo]
  exact congrArg _ <| setIntegral_congr_fun measurableSet_Ioo fun u hu ↦
    finiteVaR_eq_valueAtRisk hq ⟨hα.1.trans hu.1, hu.2⟩

end Bridge

/-! ## Evaluating `finiteVaR` -/

section Evaluation

variable {ι : Type*} [Fintype ι] {q L : ι → ℝ} {α : ℝ}

/-- **The evaluation principle**: if `v₀` is a loss level carrying `q`-mass ≥ α and every strictly
lower level carries mass < α, then `finiteVaR q L α = v₀`. Pure order arithmetic, with no
hypotheses on `q` or `α`. -/
theorem finiteVaR_eq_of_forall {v₀ : ℝ}
    (hmem : ∑ i ∈ Finset.univ.filter (L · ≤ v₀), q i ≥ α)
    (hbelow : ∀ x < v₀, ∑ i ∈ Finset.univ.filter (L · ≤ x), q i < α) :
    finiteVaR q L α = v₀ :=
  IsLeast.csInf_eq ⟨hmem, fun x hx ↦ not_lt.1 fun h ↦ (hbelow x h).not_ge hx⟩

/-- The loss values carrying mass ≥ α form a nonempty finite set: the largest loss value carries
the full mass `1 ≥ α`. -/
theorem finiteVaR_filtered_image_nonempty [Nonempty ι] (hq : q ∈ stdSimplex ℝ ι) (hα1 : α ≤ 1) :
    ((Finset.univ.image L).filter
      (fun v ↦ ∑ i ∈ Finset.univ.filter (L · ≤ v), q i ≥ α)).Nonempty := by
  obtain ⟨v₁, hv₁mem, hv₁sup⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty.image L) id
  have hfull : Finset.univ.filter (L · ≤ v₁) = Finset.univ := Finset.filter_true_of_mem fun i _ ↦
    (Finset.le_sup' id (Finset.mem_image_of_mem _ (Finset.mem_univ i))).trans_eq hv₁sup
  exact ⟨v₁, Finset.mem_filter.2 ⟨hv₁mem, by rwa [hfull, hq.2]⟩⟩

/-- **Attainment.** The infimum over `ℝ` is the minimum over the loss values
`Finset.image L univ` that carry `q`-mass ≥ α (`Finset.inf'`, since `ℝ` has no bottom element).
Every VaR at a finite law is attained at a loss value. -/
theorem finiteVaR_eq_value_inf [Nonempty ι] (hq : q ∈ stdSimplex ℝ ι) (hα0 : 0 < α)
    (hα1 : α ≤ 1) :
    finiteVaR q L α = ((Finset.univ.image L).filter
      (fun v ↦ ∑ i ∈ Finset.univ.filter (L · ≤ v), q i ≥ α)).inf'
      (finiteVaR_filtered_image_nonempty hq hα1) id := by
  obtain ⟨v₀, hv₀T, hv₀inf⟩ :=
    Finset.exists_mem_eq_inf' (finiteVaR_filtered_image_nonempty hq hα1) id
  rw [hv₀inf]
  refine IsLeast.csInf_eq ⟨(Finset.mem_filter.1 hv₀T).2, fun x (hx : _ ≥ α) ↦ ?_⟩
  -- the largest loss value `a₀ ≤ x` has the same tail mass as `x`, so it lies in the filter
  obtain ⟨i₀, hi₀⟩ : (Finset.univ.filter (L · ≤ x)).Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun he ↦ by simp [he] at hx; linarith
  have hA : ((Finset.univ.image L).filter (· ≤ x)).Nonempty :=
    ⟨L i₀, Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i₀),
      (Finset.mem_filter.1 hi₀).2⟩⟩
  obtain ⟨a₀, ha₀A, ha₀sup⟩ := Finset.exists_mem_eq_sup' hA id
  have ha₀x : a₀ ≤ x := (Finset.mem_filter.1 ha₀A).2
  have hfilt : Finset.univ.filter (L · ≤ a₀) = Finset.univ.filter (L · ≤ x) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h ↦ h.trans ha₀x, fun h ↦ (Finset.le_sup' id (Finset.mem_filter.2
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), h⟩)).trans_eq ha₀sup⟩
  have ha₀T : a₀ ∈ (Finset.univ.image L).filter
      (fun v ↦ ∑ i ∈ Finset.univ.filter (L · ≤ v), q i ≥ α) :=
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 ha₀A).1, hfilt ▸ hx⟩
  exact (hv₀inf ▸ Finset.inf'_le id ha₀T).trans ha₀x

/-- **Two-point laws.** If the tail mass of `L` is `a` on `[0, c)` and `a + b = 1` on `[c, ∞)`,
with `c > 0`, then `VaR_α` is `0` for `α ≤ a` and `c` above. -/
theorem finiteVaR_two_point {a b c : ℝ} (hab : a + b = 1) (hc : 0 < c)
    (htail : ∀ x, ∑ i ∈ Finset.univ.filter (L · ≤ x), q i
      = (if 0 ≤ x then a else 0) + (if c ≤ x then b else 0))
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR q L α = if α ≤ a then 0 else c := by
  split_ifs with h <;> refine finiteVaR_eq_of_forall ?_ fun x hx ↦ ?_ <;> rw [htail] <;>
    split_ifs <;> linarith

end Evaluation

/-! ## The single bond -/

/-- Probability vector of the single $100 bond: default (`true`) with probability `1/25`,
survival (`false`) with probability `24/25`. -/
noncomputable def oneQ : Bool → ℝ := fun b ↦ if b then 1/25 else 24/25

/-- Loss of the single $100 bond: 100 on default, 0 on survival. -/
def oneL : Bool → ℝ := fun b ↦ if b then 100 else 0

/-- `oneQ` is a probability vector. -/
lemma oneQ_mem_simplex : oneQ ∈ stdSimplex ℝ Bool :=
  ⟨fun b ↦ by cases b <;> norm_num [oneQ], by norm_num [oneQ]⟩

private lemma one_bond_tail (x : ℝ) :
    ∑ b ∈ Finset.univ.filter (oneL · ≤ x), oneQ b
      = (if 0 ≤ x then 24/25 else 0) + (if 100 ≤ x then 1/25 else 0) := by
  rw [Finset.sum_filter, Fintype.sum_bool]
  simp [oneL, oneQ, add_comm]

/-- The single-bond VaR as a function of the level `u ∈ (0, 1]`: `0` for `u ≤ 24/25`, `100`
above. This is the quantile function integrated in `es_one_bond_eq_80`. -/
theorem vaR_one_bond_window (u : ℝ) (h0 : 0 < u) (h1 : u ≤ 1) :
    finiteVaR oneQ oneL u = if u ≤ 24/25 then 0 else 100 :=
  finiteVaR_two_point (by norm_num) (by norm_num) one_bond_tail h0 h1

/-- The single $100 bond defaulting w.p. `1/25` has `VaR₀.₉₅ = 0`: the loss is 0 with probability
`24/25 ≥ 19/20`. -/
theorem vaR_one_bond : finiteVaR oneQ oneL (19/20) = 0 := by
  rw [vaR_one_bond_window _ (by norm_num) (by norm_num), if_pos (by norm_num)]

/-! ## The split position, lumped into three states -/

/-- Probability vector of the two $50 half-bonds' total loss, lumped into three states: neither
defaults (`0`, w.p. `9216/10000 = (24/25)²`), exactly one (`1`, w.p.
`768/10000 = 2·(24/25)(1/25)`), both (`2`, w.p. `16/10000 = (1/25)²`). -/
noncomputable def splitQ : Fin 3 → ℝ := ![9216/10000, 768/10000, 16/10000]

/-- Total loss of the two half-bonds at the lumped states: 0, 50, 100. -/
def splitL : Fin 3 → ℝ := ![0, 50, 100]

/-- `splitQ` is a probability vector. -/
lemma splitQ_mem_simplex : splitQ ∈ stdSimplex ℝ (Fin 3) :=
  ⟨fun i ↦ by fin_cases i <;> norm_num [splitQ],
    by rw [Fin.sum_univ_three]; norm_num [splitQ, Matrix.cons_val_two]⟩

private lemma split_tail (x : ℝ) :
    ∑ i ∈ Finset.univ.filter (splitL · ≤ x), splitQ i
      = (if 0 ≤ x then 9216/10000 else 0) + (if 50 ≤ x then 768/10000 else 0)
        + (if 100 ≤ x then 16/10000 else 0) := by
  rw [Finset.sum_filter, Fin.sum_univ_three]
  norm_num [splitL, splitQ, Matrix.cons_val_two]

/-- The same exposure split into two independent $50 bonds (lumped three-state law) has
`VaR₀.₉₅ = 50`: `P(L = 0) = 0.9216 < 0.95` but `P(L ≤ 50) = 0.9984 ≥ 0.95`. -/
theorem vaR_two_halves : finiteVaR splitQ splitL (19/20) = 50 :=
  finiteVaR_eq_of_forall (by rw [split_tail]; norm_num) fun x hx ↦ by
    rw [split_tail]; split_ifs <;> linarith

/-! ## The two half-bonds on their joint space `Bool × Bool` -/

/-- Joint law of the two independent $50 half-bonds (`true` = default): the product of the
marginals `1/25` / `24/25`. -/
noncomputable def jointQ : Bool × Bool → ℝ :=
  fun p ↦ (if p.1 then 1/25 else 24/25) * (if p.2 then 1/25 else 24/25)

/-- Loss of the first half-bond: 50 if it defaults, else 0. -/
def halfL₁ : Bool × Bool → ℝ := fun p ↦ if p.1 then 50 else 0

/-- Loss of the second half-bond: 50 if it defaults, else 0. -/
def halfL₂ : Bool × Bool → ℝ := fun p ↦ if p.2 then 50 else 0

/-- `jointQ` is a probability vector. -/
lemma jointQ_mem_simplex : jointQ ∈ stdSimplex ℝ (Bool × Bool) :=
  ⟨fun ⟨a, b⟩ ↦ by cases a <;> cases b <;> norm_num [jointQ],
    by norm_num [jointQ, Fintype.sum_prod_type]⟩

private lemma joint_half₁_tail (x : ℝ) :
    ∑ p ∈ Finset.univ.filter (halfL₁ · ≤ x), jointQ p
      = (if 0 ≤ x then 24/25 else 0) + (if 50 ≤ x then 1/25 else 0) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  norm_num [halfL₁, jointQ]; split_ifs <;> norm_num

private lemma joint_half₂_tail (x : ℝ) :
    ∑ p ∈ Finset.univ.filter (halfL₂ · ≤ x), jointQ p
      = (if 0 ≤ x then 24/25 else 0) + (if 50 ≤ x then 1/25 else 0) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  norm_num [halfL₂, jointQ]; split_ifs <;> norm_num

/-- Tail mass of the total loss `halfL₁ + halfL₂` under the joint law: the lumped split law's
masses. -/
private lemma joint_tail (x : ℝ) :
    ∑ p ∈ Finset.univ.filter ((halfL₁ + halfL₂) · ≤ x), jointQ p
      = (if 0 ≤ x then 9216/10000 else 0) + (if 50 ≤ x then 768/10000 else 0)
        + (if 100 ≤ x then 16/10000 else 0) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  norm_num [halfL₁, halfL₂, jointQ]; split_ifs <;> norm_num

/-- The first half-bond's VaR as a function of the level `α ∈ (0, 1]`. -/
theorem vaR_half₁_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR jointQ halfL₁ α = if α ≤ 24/25 then 0 else 50 :=
  finiteVaR_two_point (by norm_num) (by norm_num) joint_half₁_tail hα0 hα1

/-- The second half-bond's VaR as a function of the level `α ∈ (0, 1]`. -/
theorem vaR_half₂_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR jointQ halfL₂ α = if α ≤ 24/25 then 0 else 50 :=
  finiteVaR_two_point (by norm_num) (by norm_num) joint_half₂_tail hα0 hα1

/-- The total VaR of the two half-bonds as a function of the level `α ∈ (0, 1]`: `0` up to the
mass `9216/10000` of no default, `50` up to the mass `9984/10000` of at most one default, `100`
above. -/
theorem vaR_joint_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR jointQ (halfL₁ + halfL₂) α
      = if α ≤ 9216/10000 then 0 else if α ≤ 9984/10000 then 50 else 100 := by
  split_ifs <;> refine finiteVaR_eq_of_forall ?_ fun x hx ↦ ?_ <;> rw [joint_tail] <;>
    split_ifs <;> linarith

/-- **Subadditivity fails at the 95% level** on one probability space: each $50 half-bond has
`VaR₀.₉₅ = 0`, their sum has `VaR₀.₉₅ = 50` (the value of `vaR_two_halves`). -/
theorem vaR_subadditivity_fails :
    finiteVaR jointQ halfL₁ (19/20) + finiteVaR jointQ halfL₂ (19/20)
      < finiteVaR jointQ (halfL₁ + halfL₂) (19/20) := by
  rw [vaR_half₁_window _ (by norm_num) (by norm_num), vaR_half₂_window _ (by norm_num)
    (by norm_num), vaR_joint_window _ (by norm_num) (by norm_num)]
  norm_num

/-- **The failure window.** Subadditivity fails exactly for `9216/10000 < α ≤ 24/25`, where
`9216/10000 = (24/25)²`. The right endpoint is included because the definition uses
`P(L ≤ x) ≥ α`: at `α = 24/25` each half keeps VaR `0` while the total has VaR `50`. At
`α = 9216/10000` the total VaR is already `0`. -/
theorem vaR_counterexample_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR jointQ halfL₁ α + finiteVaR jointQ halfL₂ α
      < finiteVaR jointQ (halfL₁ + halfL₂) α ↔ 9216/10000 < α ∧ α ≤ 24/25 := by
  rw [vaR_joint_window α hα0 hα1, vaR_half₁_window α hα0 hα1, vaR_half₂_window α hα0 hα1]
  constructor
  · split_ifs <;> intro h <;> norm_num at h <;> exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    rw [if_pos h2, if_neg h1.not_ge, if_pos (by linarith)]
    norm_num

/-! ## Expected shortfall at the single bond -/

/-- `ES₀.₉₅ = 80` for the single bond: the quantile function is `0` on `[19/20, 24/25]` and `100`
on `(24/25, 1]`, so the average is `(1/(1/20)) · 100 · (1 - 24/25) = 80`. -/
theorem es_one_bond_eq_80 : finiteES oneQ oneL (19/20) = 80 := by
  have hz1 (u) (hu : u ∈ Icc (19/20 : ℝ) (24/25)) : finiteVaR oneQ oneL u = 0 := by
    rw [vaR_one_bond_window u (by linarith [hu.1]) (by linarith [hu.2]), if_pos hu.2]
  have hc1 (u) (hu : u ∈ Ioc (24/25 : ℝ) 1) : finiteVaR oneQ oneL u = 100 := by
    rw [vaR_one_bond_window u (by linarith [hu.1]) hu.2, if_neg (not_le.2 hu.1)]
  -- the first piece vanishes pointwise on the closed interval; the second is a.e. the constant 100
  have h1int : IntervalIntegrable (finiteVaR oneQ oneL) volume (19/20 : ℝ) (24/25) :=
    ContinuousOn.intervalIntegrable <| continuousOn_const.congr fun u hu ↦
      hz1 u (by rwa [uIcc_of_le (by norm_num)] at hu)
  have h2int : IntervalIntegrable (finiteVaR oneQ oneL) volume (24/25 : ℝ) 1 :=
    (intervalIntegrable_const (c := (100 : ℝ))).congr_ae <| by
      rw [uIoc_of_le (by norm_num)]
      exact (ae_restrict_mem measurableSet_Ioc).mono fun u hu ↦ (hc1 u hu).symm
  have hval1 : ∫ u in (19/20 : ℝ)..(24/25), finiteVaR oneQ oneL u = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun u hu ↦
      hz1 u (by rwa [uIcc_of_le (by norm_num)] at hu)]
    simp
  have hval2 : ∫ u in (24/25 : ℝ)..1, finiteVaR oneQ oneL u = 4 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ (100 : ℝ)) <|
      Filter.Eventually.of_forall fun u hu ↦ hc1 u (by rwa [uIoc_of_le (by norm_num)] at hu)]
    norm_num
  rw [finiteES, ← intervalIntegral.integral_add_adjacent_intervals h1int h2int, hval1, hval2]
  norm_num

/-! ## The conditional tail mean at an atom -/

/-- **`E[L | L ≥ VaR_α]` at a finite law**: the `q`-weighted mean of `L` over the tail event
`{i | finiteVaR q L α ≤ L i}`. -/
noncomputable def condTailMean {ι : Type*} [Fintype ι] (q L : ι → ℝ) (α : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ.filter (finiteVaR q L α ≤ L ·), q i * L i) /
    (∑ i ∈ Finset.univ.filter (finiteVaR q L α ≤ L ·), q i)

/-- At the single bond the tail event `{L ≥ VaR₀.₉₅} = {L ≥ 0}` is the whole state space, so the
conditional tail mean is the unconditional expectation `E[L] = 4`, while `ES₀.₉₅ = 80`
(`es_one_bond_eq_80`). -/
theorem condTailMean_one_bond :
    condTailMean oneQ oneL (19/20) = ∑ b, oneQ b * oneL b ∧ ∑ b, oneQ b * oneL b = 4 := by
  have hfilt : Finset.univ.filter (finiteVaR oneQ oneL (19/20) ≤ oneL ·) = Finset.univ :=
    Finset.filter_true_of_mem fun b _ ↦ by rw [vaR_one_bond]; cases b <;> norm_num [oneL]
  refine ⟨by rw [condTailMean, hfilt, oneQ_mem_simplex.2, div_one], by norm_num [oneQ, oneL]⟩

/-! ## The bounded-density representation of ES at the single bond -/

/-- For the single bond, the greatest value of `E[Z·L]` over densities `Z` with
`0 ≤ Z ≤ (1 - 19/20)⁻¹ = 20` and `E[Z] = 1` is `80`, the value of `es_one_bond_eq_80`. It is
attained at `Z = 20` on default and `5/24` on survival. This is the two-state instance of
`isGreatest_integral_mul_expectedShortfall`; here the objective is `E[Z·L] = 4·Z(default)`, so
the bound is the cap. -/
theorem es_sup_representation_finite :
    IsGreatest ((fun Z : Bool → ℝ ↦ ∑ b, oneQ b * Z b * oneL b) ''
      {Z | (∀ b, 0 ≤ Z b ∧ Z b ≤ (1 - 19/20)⁻¹) ∧ ∑ b, oneQ b * Z b = 1}) 80 := by
  refine ⟨⟨fun c ↦ if c then 20 else 5/24,
    ⟨fun c ↦ by cases c <;> norm_num, by norm_num [oneQ]⟩, by norm_num [oneQ, oneL]⟩, ?_⟩
  rintro v ⟨Z, ⟨hcap, -⟩, rfl⟩
  have := (hcap true).2
  norm_num [oneQ, oneL] at this ⊢
  linarith

end MathFin.DiscreteVaR
