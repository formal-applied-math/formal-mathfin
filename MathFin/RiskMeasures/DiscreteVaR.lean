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
value-at-risk is `VaR_α = inf {x | α ≤ ∑_{L i ≤ x} q i}` (`finiteVaR`) and expected shortfall is
the quantile average `ES_α = (1 − α)⁻¹ ∫_α^1 VaR_u du` (`finiteES`). For `α ∈ (0, 1)` these are
`valueAtRisk` and `expectedShortfall` of `RiskMeasures/ValueAtRisk.lean` at the law
`∑ i, q i • δ_i` (`finiteVaR_eq_valueAtRisk`, `finiteES_eq_expectedShortfall`), written as
`Finset` sums so that concrete laws evaluate by case analysis on the loss level.

The file works the two-bond example. A single `$100` bond defaulting with probability `1/25` has
`VaR₀.₉₅ = 0`: the loss is 0 with probability `24/25 ≥ 0.95`. The same exposure split into two
`$50` bonds defaulting independently has `VaR₀.₉₅ = 50`, so VaR penalizes the diversified position.
At the single bond, expected shortfall is `80` while the conditional tail mean `E[L | L ≥ VaR₀.₉₅]`
is the unconditional mean `4`.

These are worked instances of general results in the library. In
`RiskMeasures/VaRSuperadditivity.lean`, `valueAtRisk_sum_bernoulli_of_card_two` is the two-loan
example for independent (`iIndepFun`), identically distributed unit losses sharing one default
probability `p`: on `(1 − p)² < α ≤ 1 − p` each loan has VaR `0` and the portfolio VaR `1`. The
exact superadditivity window, for `α ∈ (0, 1)` and any number of independent, identically
distributed Bernoulli losses (same shared `p`), is `valueAtRisk_sum_bernoulli_superadditive_iff`.
The dual representation
of ES over bounded densities is `isGreatest_integral_mul_expectedShortfall`
(`RiskMeasures/ExpectedShortfall.lean`).

## Main results

* `finiteVaR_eq_valueAtRisk`, `finiteES_eq_expectedShortfall`: for `α ∈ (0, 1)` and a probability
  vector `q`, the finite forms agree with the general definitions at the law `∑ i, q i • δ_i`.
* `finiteVaR_eq_value_min`: for `α ∈ (0, 1]` and a probability vector `q`, VaR at a finite law is
  attained at a loss value.
* `finiteVaR_two_point`: for `α ∈ (0, 1]`, VaR of a loss that is `0` with mass `a` and `c > 0` with
  mass `1 - a`.
* `vaR_one_bond`, `vaR_two_halves`: `VaR₀.₉₅` is `0` for the single bond and `50` for the split
  position.
* `vaR_subadditivity_fails`: on the joint space of the two half-bonds, the halves' `VaR₀.₉₅`
  sum to less than the total's (the values are `0`, `0` and `50`).
* `vaR_counterexample_window`: for `α ∈ (0, 1]`, subadditivity fails exactly for
  `(24/25)² < α ≤ 24/25`.
* `es_one_bond_eq_80`: `ES₀.₉₅ = 80` for the single bond.
* `condTailMean_one_bond`: at the single bond the tail event `{L ≥ VaR₀.₉₅}` is the whole space,
  so the conditional tail mean is `E[L] = 4`.
* `isGreatest_es_one_bond`: for the single bond, `ES₀.₉₅` is the greatest `E[Z·L]` over
  densities `0 ≤ Z ≤ (1 − 19/20)⁻¹` with `E[Z] = 1`.
-/

@[expose] public section

namespace MathFin.DiscreteVaR

open MeasureTheory Set
open scoped Interval

variable {ι : Type*} [Fintype ι]

/-! ## The definitions and the bridge to `valueAtRisk` -/

/-- **VaR at a finite law**: the infimum of the loss levels `x` at which the `q`-mass of
`{i | L i ≤ x}` reaches `α`. The lemmas that need `q` to be a probability vector take
`q ∈ stdSimplex ℝ ι` as a hypothesis. -/
noncomputable def finiteVaR (q L : ι → ℝ) (α : ℝ) : ℝ :=
  sInf {x | α ≤ ∑ i with L i ≤ x, q i}

/-- **ES at a finite law**: the quantile average, `(1 - α)⁻¹` times the integral of the quantile
function `u ↦ finiteVaR q L u` over `[α, 1]`. -/
noncomputable def finiteES (q L : ι → ℝ) (α : ℝ) : ℝ :=
  (1 - α)⁻¹ * ∫ u in α..1, finiteVaR q L u

/-- The law `∑ i, q i • δ_i` of a probability vector `q`. -/
noncomputable def finiteLaw [MeasurableSpace ι] (q : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (q i) • Measure.dirac i

section Bridge

variable [MeasurableSpace ι] {q : ι → ℝ}

/-- The law of a probability vector is a probability measure. -/
lemma isProbabilityMeasure_finiteLaw (hq : q ∈ stdSimplex ℝ ι) :
    IsProbabilityMeasure (finiteLaw q) :=
  ⟨by simp [finiteLaw, ← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hq.1 i, hq.2]⟩

variable [MeasurableSingletonClass ι]

/-- For nonnegative weights `q`, under `finiteLaw q` the probability of `{L ≤ x}` is the mass
summed in `finiteVaR`. -/
lemma finiteLaw_real_le (hq : ∀ i, 0 ≤ q i) (L : ι → ℝ) (x : ℝ) :
    (finiteLaw q).real {i | L i ≤ x} = ∑ i with L i ≤ x, q i := by
  rw [measureReal_def, finiteLaw, Measure.coe_finsetSum, Finset.sum_apply]
  simp_rw [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum fun i _ ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hi : L i ≤ x <;> simp [Measure.dirac_apply, hi, hq i]

/-- For `α ∈ (0, 1)` and a probability vector `q`, `finiteVaR` is `valueAtRisk` at the law
`∑ i, q i • δ_i`. -/
theorem finiteVaR_eq_valueAtRisk (hq : q ∈ stdSimplex ℝ ι) {L : ι → ℝ} {α : ℝ}
    (hα : α ∈ Ioo 0 1) : finiteVaR q L α = valueAtRisk L (finiteLaw q) α := by
  have := isProbabilityMeasure_finiteLaw hq
  have hset : {x | α ≤ ∑ i with L i ≤ x, q i}
      = Ici (valueAtRisk L (finiteLaw q) α) := by
    ext x
    simp [valueAtRisk_le_iff (measurable_of_finite L).aemeasurable hα, finiteLaw_real_le hq.1]
  rw [finiteVaR, hset, csInf_Ici]

/-- For `α ∈ (0, 1)` and a probability vector `q`, `finiteES` is `expectedShortfall` at the law
`∑ i, q i • δ_i`. -/
theorem finiteES_eq_expectedShortfall (hq : q ∈ stdSimplex ℝ ι) {L : ι → ℝ} {α : ℝ}
    (hα : α ∈ Ioo 0 1) : finiteES q L α = expectedShortfall L (finiteLaw q) α := by
  rw [finiteES, expectedShortfall, intervalIntegral.integral_of_le hα.2.le,
    integral_Ioc_eq_integral_Ioo]
  exact congrArg _ <| setIntegral_congr_fun measurableSet_Ioo fun u hu ↦
    finiteVaR_eq_valueAtRisk hq ⟨hα.1.trans hu.1, hu.2⟩

end Bridge

/-! ## Evaluating `finiteVaR` -/

section Evaluation

variable {q L : ι → ℝ} {α : ℝ}

/-- **The evaluation principle**: if the `q`-mass of `{L ≤ v₀}` reaches α and the mass of
`{L ≤ x}` stays below α for every `x < v₀`, then `finiteVaR q L α = v₀`. Pure order arithmetic,
with no hypotheses on `q` or `α`. -/
theorem finiteVaR_eq_of_mem_of_forall_lt {v₀ : ℝ}
    (hmem : α ≤ ∑ i with L i ≤ v₀, q i)
    (hbelow : ∀ x < v₀, ∑ i with L i ≤ x, q i < α) :
    finiteVaR q L α = v₀ :=
  IsLeast.csInf_eq ⟨hmem, fun x hx ↦ not_lt.1 fun h ↦ (hbelow x h).not_ge hx⟩

/-- For a probability vector `q` and `α ≤ 1`, the loss values `v` at which the mass of `{L ≤ v}`
is at least α form a nonempty finite set: at the largest loss value that mass is the full mass
`1 ≥ α`. -/
theorem nonempty_values_mass_ge (hq : q ∈ stdSimplex ℝ ι) (hα1 : α ≤ 1) :
    {v ∈ Finset.univ.image L | α ≤ ∑ i with L i ≤ v, q i}.Nonempty := by
  have hne := (Finset.nonempty_of_sum_ne_zero (by rw [hq.2]; norm_num)).image L
  have hfull : {i ∈ (Finset.univ : Finset ι) | L i ≤ (Finset.univ.image L).max' hne}
      = Finset.univ :=
    Finset.filter_true_of_mem fun i _ ↦
      Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  exact ⟨_, Finset.mem_filter.2 ⟨Finset.max'_mem _ hne, by rwa [hfull, hq.2]⟩⟩

/-- **Attainment.** For `α ∈ (0, 1]` and a probability vector `q`, the infimum over `ℝ` is the
minimum over the loss values `v ∈ Finset.image L univ` at which the `q`-mass of `{L ≤ v}` is at
least α, so VaR is attained at a loss value. -/
theorem finiteVaR_eq_value_min (hq : q ∈ stdSimplex ℝ ι) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR q L α = {v ∈ Finset.univ.image L | α ≤ ∑ i with L i ≤ v, q i}.min'
      (nonempty_values_mass_ge hq hα1) := by
  refine IsLeast.csInf_eq ⟨(Finset.mem_filter.1 (Finset.min'_mem _ _)).2,
    fun x (hx : α ≤ _) ↦ ?_⟩
  -- the largest loss value `L j ≤ x` carries the same mass as `x`, so it lies in the filter
  obtain ⟨j, hj, hjmax⟩ :=
    Finset.exists_max_image _ L (Finset.nonempty_of_sum_ne_zero (hα0.trans_le hx).ne')
  have hjx := (Finset.mem_filter.1 hj).2
  have hfilt : {i ∈ (Finset.univ : Finset ι) | L i ≤ L j}
      = {i ∈ (Finset.univ : Finset ι) | L i ≤ x} :=
    Finset.filter_congr fun i _ ↦ ⟨fun h ↦ h.trans hjx, fun h ↦ hjmax i (by simpa using h)⟩
  exact (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ j),
    hfilt ▸ hx⟩)).trans hjx

/-- **Two-point laws.** If the mass of `{L ≤ x}` is `0` for `x < 0`, `a` for `0 ≤ x < c` and
`a + b = 1` for `x ≥ c`, with `c > 0`, then at every level `α ∈ (0, 1]` the VaR is `0` for
`α ≤ a` and `c` above. -/
theorem finiteVaR_two_point {a b c : ℝ} (hab : a + b = 1) (hc : 0 < c)
    (hcdf : ∀ x, ∑ i with L i ≤ x, q i
      = (if 0 ≤ x then a else 0) + (if c ≤ x then b else 0))
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR q L α = if α ≤ a then 0 else c := by
  split_ifs <;> refine finiteVaR_eq_of_mem_of_forall_lt ?_ fun x hx ↦ ?_ <;> rw [hcdf] <;>
    split_ifs <;> linarith

end Evaluation

/-! ## The single bond -/

/-- Probability vector of the single `$100` bond: default (`true`) with probability `1/25`,
survival (`false`) with probability `24/25`. -/
noncomputable def oneQ : Bool → ℝ := fun b ↦ if b then 1 / 25 else 24 / 25

/-- Loss of the single `$100` bond: 100 on default, 0 on survival. -/
def oneL : Bool → ℝ := fun b ↦ if b then 100 else 0

/-- `oneQ` is a probability vector. -/
lemma oneQ_mem_simplex : oneQ ∈ stdSimplex ℝ Bool :=
  ⟨fun b ↦ by cases b <;> norm_num [oneQ], by norm_num [oneQ]⟩

private lemma one_bond_cdf (x : ℝ) :
    ∑ b with oneL b ≤ x, oneQ b
      = (if 0 ≤ x then 24 / 25 else 0) + (if 100 ≤ x then 1 / 25 else 0) := by
  rw [Finset.sum_filter, Fintype.sum_bool]
  simp [oneL, oneQ, add_comm]

/-- The single-bond VaR as a function of the level `α ∈ (0, 1]`: `0` for `α ≤ 24/25`, `100`
above. This is the quantile function integrated in `es_one_bond_eq_80`. -/
theorem vaR_one_bond_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR oneQ oneL α = if α ≤ 24 / 25 then 0 else 100 :=
  finiteVaR_two_point (by norm_num) (by norm_num) one_bond_cdf hα0 hα1

/-- The single `$100` bond defaulting w.p. `1/25` has `VaR₀.₉₅ = 0`: the loss is 0 with probability
`24/25 ≥ 19/20`. -/
theorem vaR_one_bond : finiteVaR oneQ oneL (19 / 20) = 0 := by
  rw [vaR_one_bond_window _ (by norm_num) (by norm_num), if_pos (by norm_num)]

/-! ## The two half-bonds on their joint space `Bool × Bool` -/

/-- Joint law of the two independent `$50` half-bonds (`true` = default): the product of the
marginals `1/25` / `24/25`. -/
noncomputable def jointQ : Bool × Bool → ℝ :=
  fun p ↦ oneQ p.1 * oneQ p.2

/-- Loss of the first half-bond: 50 if it defaults, else 0. -/
def halfL₁ : Bool × Bool → ℝ := fun p ↦ if p.1 then 50 else 0

/-- Loss of the second half-bond: 50 if it defaults, else 0. -/
def halfL₂ : Bool × Bool → ℝ := fun p ↦ if p.2 then 50 else 0

/-- `jointQ` is a probability vector. -/
lemma jointQ_mem_simplex : jointQ ∈ stdSimplex ℝ (Bool × Bool) :=
  ⟨fun ⟨a, b⟩ ↦ by cases a <;> cases b <;> norm_num [jointQ, oneQ],
    by norm_num [jointQ, oneQ, Fintype.sum_prod_type]⟩

private lemma joint_half₁_cdf (x : ℝ) :
    ∑ p with halfL₁ p ≤ x, jointQ p
      = (if 0 ≤ x then 24 / 25 else 0) + (if 50 ≤ x then 1 / 25 else 0) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  norm_num [halfL₁, jointQ, oneQ]
  split_ifs <;> norm_num

private lemma joint_half₂_cdf (x : ℝ) :
    ∑ p with halfL₂ p ≤ x, jointQ p
      = (if 0 ≤ x then 24 / 25 else 0) + (if 50 ≤ x then 1 / 25 else 0) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  norm_num [halfL₂, jointQ, oneQ]
  split_ifs <;> norm_num

/-- Mass of `{halfL₁ + halfL₂ ≤ x}` under the joint law: no default w.p. `9216/10000 = (24/25)²`,
one default w.p. `768/10000 = 2·(24/25)(1/25)`, two w.p. `16/10000 = (1/25)²`. -/
private lemma joint_cdf (x : ℝ) :
    ∑ p with (halfL₁ + halfL₂) p ≤ x, jointQ p
      = (if 0 ≤ x then 9216 / 10000 else 0) + (if 50 ≤ x then 768 / 10000 else 0)
        + (if 100 ≤ x then 16 / 10000 else 0) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  norm_num [halfL₁, halfL₂, jointQ, oneQ]
  split_ifs <;> norm_num

/-- The first half-bond's VaR as a function of the level `α ∈ (0, 1]`. -/
theorem vaR_half₁_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR jointQ halfL₁ α = if α ≤ 24 / 25 then 0 else 50 :=
  finiteVaR_two_point (by norm_num) (by norm_num) joint_half₁_cdf hα0 hα1

/-- The second half-bond's VaR as a function of the level `α ∈ (0, 1]`. -/
theorem vaR_half₂_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR jointQ halfL₂ α = if α ≤ 24 / 25 then 0 else 50 :=
  finiteVaR_two_point (by norm_num) (by norm_num) joint_half₂_cdf hα0 hα1

/-- The total VaR of the two half-bonds as a function of the level `α ∈ (0, 1]`: `0` up to the
mass `9216/10000` of no default, `50` up to the mass `9984/10000` of at most one default, `100`
above. -/
theorem vaR_joint_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR jointQ (halfL₁ + halfL₂) α
      = if α ≤ 9216 / 10000 then 0 else if α ≤ 9984 / 10000 then 50 else 100 := by
  split_ifs <;> refine finiteVaR_eq_of_mem_of_forall_lt ?_ fun x hx ↦ ?_ <;> rw [joint_cdf] <;>
    split_ifs <;> linarith

/-- The same exposure split into two independent `$50` bonds has `VaR₀.₉₅ = 50`:
`P(L = 0) = 0.9216 < 0.95` but `P(L ≤ 50) = 0.9984 ≥ 0.95`. -/
theorem vaR_two_halves : finiteVaR jointQ (halfL₁ + halfL₂) (19 / 20) = 50 := by
  rw [vaR_joint_window _ (by norm_num) (by norm_num)]
  norm_num

/-- **The failure window.** For the level `α ∈ (0, 1]`, subadditivity fails exactly for
`9216/10000 < α ≤ 24/25`, where `9216/10000 = (24/25)²`. The right endpoint is included because
the definition uses `α ≤ P(L ≤ x)`: at `α = 24/25` each half keeps VaR `0` while the total has
VaR `50`. At `α = 9216/10000` the total VaR is still `0`, so the left endpoint is excluded. -/
theorem vaR_counterexample_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR jointQ halfL₁ α + finiteVaR jointQ halfL₂ α
      < finiteVaR jointQ (halfL₁ + halfL₂) α ↔ 9216 / 10000 < α ∧ α ≤ 24 / 25 := by
  rw [vaR_joint_window α hα0 hα1, vaR_half₁_window α hα0 hα1, vaR_half₂_window α hα0 hα1]
  constructor
  · split_ifs <;> intro h <;> norm_num at h <;> exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    rw [if_pos h2, if_neg h1.not_ge, if_pos (by linarith)]
    norm_num

/-- **Subadditivity fails at the 95% level** on one probability space: the two `$50` half-bonds'
`VaR₀.₉₅` sum to less than the `VaR₀.₉₅` of their total. The values are `0` for each half
(`vaR_half₁_window`, `vaR_half₂_window`) and `50` for the total (`vaR_two_halves`). -/
theorem vaR_subadditivity_fails :
    finiteVaR jointQ halfL₁ (19 / 20) + finiteVaR jointQ halfL₂ (19 / 20)
      < finiteVaR jointQ (halfL₁ + halfL₂) (19 / 20) :=
  (vaR_counterexample_window _ (by norm_num) (by norm_num)).2 ⟨by norm_num, by norm_num⟩

/-! ## Expected shortfall at the single bond -/

/-- `ES₀.₉₅ = 80` for the single bond: the quantile function is `0` on `[19/20, 24/25]` and `100`
on `(24/25, 1]`, so the average is `(1/(1/20)) · 100 · (1 - 24/25) = 80`. -/
theorem es_one_bond_eq_80 : finiteES oneQ oneL (19 / 20) = 80 := by
  have hz1 (u) (hu : u ∈ Icc (19 / 20 : ℝ) (24 / 25)) : finiteVaR oneQ oneL u = 0 := by
    rw [vaR_one_bond_window u (by linarith [hu.1]) (by linarith [hu.2]), if_pos hu.2]
  have hc1 (u) (hu : u ∈ Ioc (24 / 25 : ℝ) 1) : finiteVaR oneQ oneL u = 100 := by
    rw [vaR_one_bond_window u (by linarith [hu.1]) hu.2, if_neg (not_le.2 hu.1)]
  -- the quantile function agrees a.e. with a constant on each piece, which gives both
  -- integrability and the value of the integral in one hypothesis
  have hae1 : finiteVaR oneQ oneL =ᵐ[volume.restrict (Ι (19 / 20 : ℝ) (24 / 25))]
      fun _ ↦ (0 : ℝ) :=
    Set.EqOn.aeEq_restrict (fun u hu ↦ by
      rw [uIoc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 24 / 25)] at hu
      exact hz1 u (Ioc_subset_Icc_self hu)) measurableSet_uIoc
  have hae2 : finiteVaR oneQ oneL =ᵐ[volume.restrict (Ι (24 / 25 : ℝ) 1)] fun _ ↦ (100 : ℝ) :=
    Set.EqOn.aeEq_restrict (fun u hu ↦ by
      rw [uIoc_of_le (by norm_num : (24 / 25 : ℝ) ≤ 1)] at hu
      exact hc1 u hu) measurableSet_uIoc
  have h1int : IntervalIntegrable (finiteVaR oneQ oneL) volume (19 / 20 : ℝ) (24 / 25) :=
    intervalIntegrable_const.congr_ae hae1.symm
  have h2int : IntervalIntegrable (finiteVaR oneQ oneL) volume (24 / 25 : ℝ) 1 :=
    intervalIntegrable_const.congr_ae hae2.symm
  have hval1 : ∫ u in (19 / 20 : ℝ)..(24 / 25), finiteVaR oneQ oneL u = 0 := by
    rw [intervalIntegral.integral_congr_ae_restrict hae1]; simp
  have hval2 : ∫ u in (24 / 25 : ℝ)..1, finiteVaR oneQ oneL u = 4 := by
    rw [intervalIntegral.integral_congr_ae_restrict hae2]; norm_num
  rw [finiteES, ← intervalIntegral.integral_add_adjacent_intervals h1int h2int, hval1, hval2]
  norm_num

/-! ## The conditional tail mean at an atom -/

/-- **`E[L | L ≥ VaR_α]` at a finite law**: the `q`-weighted mean of `L` over the tail event
`{i | finiteVaR q L α ≤ L i}`. -/
noncomputable def condTailMean (q L : ι → ℝ) (α : ℝ) : ℝ :=
  (∑ i with finiteVaR q L α ≤ L i, q i * L i) /
    (∑ i with finiteVaR q L α ≤ L i, q i)

/-- At the single bond the tail event `{L ≥ VaR₀.₉₅} = {L ≥ 0}` is the whole state space, so the
conditional tail mean is the unconditional expectation `E[L] = 4`, while `ES₀.₉₅ = 80`
(`es_one_bond_eq_80`). -/
theorem condTailMean_one_bond : condTailMean oneQ oneL (19 / 20) = 4 := by
  have hfilt : {b ∈ (Finset.univ : Finset Bool) | finiteVaR oneQ oneL (19 / 20) ≤ oneL b}
      = Finset.univ :=
    Finset.filter_true_of_mem fun b _ ↦ by rw [vaR_one_bond]; cases b <;> norm_num [oneL]
  rw [condTailMean, hfilt, oneQ_mem_simplex.2, div_one]
  norm_num [oneQ, oneL]

/-! ## The bounded-density representation of ES at the single bond -/

/-- For the single bond, `ES₀.₉₅` is the greatest value of `E[Z·L]` over densities `Z` with
`0 ≤ Z ≤ (1 - 19/20)⁻¹ = 20` and `E[Z] = 1`; both equal `80` (`es_one_bond_eq_80`). This is the
two-state analogue of `isGreatest_integral_mul_expectedShortfall`. The objective is
`E[Z·L] = 4·Z(default)`, so the maximum puts `Z(default)` at the cap `20`, and `E[Z] = 1` then
gives `Z(survival) = 5/24`. -/
theorem isGreatest_es_one_bond :
    IsGreatest ((fun Z : Bool → ℝ ↦ ∑ b, oneQ b * Z b * oneL b) ''
      {Z | (∀ b, 0 ≤ Z b ∧ Z b ≤ (1 - 19 / 20)⁻¹) ∧ ∑ b, oneQ b * Z b = 1})
      (finiteES oneQ oneL (19 / 20)) := by
  rw [es_one_bond_eq_80]
  refine ⟨⟨fun c ↦ if c then 20 else 5 / 24,
    ⟨fun c ↦ by cases c <;> norm_num, by norm_num [oneQ]⟩, by norm_num [oneQ, oneL]⟩, ?_⟩
  rintro v ⟨Z, ⟨hcap, -⟩, rfl⟩
  have := (hcap true).2
  norm_num [oneQ, oneL] at this ⊢
  linarith

end MathFin.DiscreteVaR
