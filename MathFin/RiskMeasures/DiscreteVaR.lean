/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Discrete-law Value at Risk and Expected Shortfall

Chapter 24's first four pages are about **one number and two bonds**. A single
$100 bond defaulting with probability `1/25` has `VaR₀.₉₅ = $0` (the loss is 0
with probability `24/25 ≥ 0.95`); the *same credit exposure* split into two $50
bonds defaulting independently has `VaR₀.₉₅ = $50` — diversification is punished.
This file makes that arithmetic — Def 24.2 (`VaR_α = inf {x | P(L ≤ x) ≥ α}`),
Example 24.1, the α-window where the failure lives, Def 24.3's quantile average
(the ES "eighty against four"), and Thm 24.4's bounded-density supremum at the
two-state law — **proved Lean**, all finite-space: `Finset` sums over
`stdSimplex ℝ ι` probability vectors, plus one interval integral of a step
function. No measurability, no Radon–Nikodym, no ess-sup anywhere.

## Result

* `MathFin.DiscreteVaR.finiteVaR` — Def 24.2 at a finite law; attained at a loss
  value (`finiteVaR_eq_value_inf`).
* `MathFin.DiscreteVaR.vaR_one_bond` / `vaR_two_halves` — Example 24.1: the
  one-bond law has `VaR₀.₉₅ = 0`, the split two-half law has `VaR₀.₉₅ = 50`.
* `MathFin.DiscreteVaR.vaR_subadditivity_fails` — subadditivity fails at α = 19/20
  on the honest joint space, as a theorem.
* `MathFin.DiscreteVaR.vaR_counterexample_window` — failure ⟺
  `9216/10000 < α ≤ 24/25` (right endpoint included under Def 24.2's convention).
* `MathFin.DiscreteVaR.es_one_bond_eq_80` — Def 24.3's quantile average (ES = 80);
  `es_sup_representation_finite` — Thm 24.4's supremum at the two-state law.
* `MathFin.DiscreteVaR.condExp_tail_eq_mean_one_bond` — the conditional tail mean
  collapses to the unconditional mean at an atom (the "$4 against $80" contrast).

Boundary: the general bounded-density form of Thm 24.4 (essential sup /
Radon–Nikodym), elicitability scoring, CVA/exposure objects, and cross-desk
aggregation composition are out of scope. The Bernoulli superadditivity *iff* in
`RiskMeasures.VaRSuperadditivity` covers the general two-point law in
measure-space form; this file complements it with the discrete-law formulation
(`stdSimplex` probability vectors, Def 24.2's attained infimum, the ES quantile
average, and the exact α-window).


## What is built

1. `finiteVaR` — Def 24.2 verbatim: `sInf {x | ∑ i in univ.filter (L · ≤ x), q i ≥ α}`
   on `Fintype ι`, `q ∈ stdSimplex ℝ ι` (the `WorstCaseRisk` probability-vector
   idiom).
2. `finiteVaR_eq_value_inf` — attainment: the infimum over ℝ collapses to the
   `Finset.inf'` of the loss *values* that carry mass ≥ α (the "Finset.inf"; on ℝ the order-bot-free `Finset.inf'` is the right operator).
   The pure evaluation principle `finiteVaR_eq_of_forall` (a witness in the set
   that strictly dominates every lower `x`) is the workhorse for 3–6.
3. `vaR_one_bond` — the one-bond law (loss 0 w.p. `24/25`, loss 100 w.p.
   `1/25`): `finiteVaR oneQ oneL (19/20) = 0` (Example 24.1, first half).
4. `vaR_two_halves` — the split law, lumped three-state form (0 w.p. 0.9216 =
   `9216/10000`, 50 w.p. 0.0768 = `768/10000`, 100 w.p. 0.0016 = `16/10000`):
   `finiteVaR splitQ splitL (19/20) = 50`.
5. `vaR_subadditivity_fails` — **the headline**, on the honest joint space
   `Bool × Bool` (two independent half-bonds, marginal laws 0/50):
   `¬ (finiteVaR jointQ (halfL₁ + halfL₂) (19/20) ≤ finiteVaR jointQ halfL₁
   (19/20) + finiteVaR jointQ halfL₂ (19/20))` — i.e. `50 > 0 + 0` as a theorem.
   Subadditivity is a statement about one probability space, so all three VaRs
   are taken under the *joint* law `jointQ` (the compacted
   `finiteVaR q' (L'+L')` notation reads as exactly this: the VaR of the sum of
   the two half-position losses vs the VaRs of its parts).
6. `vaR_counterexample_window` — the chapter's exercise, sharpened: failure ⟺
   `9216/10000 < α ≤ 24/25`. The right endpoint is **included** under Def
   24.2's `P(L ≤ x) ≥ α` convention (at `α = 24/25`: `P(L ≤ 0) = 24/25 ≥ 24/25`
   keeps each half at VaR 0 while the joint VaR is 50); the chapter states the
   open interval — the Lean statement pins the endpoint. `α = 9216/10000`
   itself is excluded (`P(L ≤ 0) = 9216/10000` collapses the joint VaR to 0).
   The failure window's lower constant is `9216/10000 = (24/25)^2` (the
   chapter's 0.9216);
7. `es_one_bond_eq_80` — Def 24.3 at the one-bond law:
   `finiteES oneQ oneL (19/20) = (1/(1-α)) ∫_α^1 VaR_u du = 80` (the quantile
   function is the step 0 on `[19/20, 24/25]`, 100 on `(24/25, 1]`; encoded as
   the interval integral of that step — `intervalIntegral` split at the jump,
   the ae-congruence handling the jump point).
8. `condExp_tail_eq_mean_one_bond` — `E[L | L ≥ VaR_α] = E[L] = 4` at the
   one-bond law: the tail event `{L ≥ 0}` is the whole space at an atom, so the
   "conditional" form reports the unconditional mean — the $4 against $80
   contrast, proved.

## Stretch (landed)

* `es_sup_representation_finite` — Thm 24.4 at the two-state law: the supremum
  of `E[Z · L]` over densities `0 ≤ Z ≤ 1/(1-α) = 20` with `E[Z] = 1` equals
  `80`, attained by `Z*` = 20 on default, `5/24` on survival. The 2-state LP is
  trivial (the objective touches only the default coordinate: `4·Z_def ≤ 80`
  with equality at the cap), which is exactly why this example is provable
  without the RN/ess-sup machinery the general theorem needs.

## Out of scope

* The general bounded-density form of Thm 24.4: it needs an essential-sup /
  Radon–Nikodym layer. The proved neighbours are `MathFin.worstCase_isLUB`
  (the *unbounded* distortion endpoint, sup over the entire simplex) and
  `MathFin.coherentRisk_isLUB` (the abstract ADEH representation at finite
  state); this file adds the *bounded* member at one two-state law only.
* Elicitability scoring (Def 24.9 / eq. 24.5) — no scoring-function or argmin
  machinery.
* CVA / exposure objects (§24.11).
* Cross-desk aggregation composition (§24.12) — the window theorem's
  α-decomposition is the only proved "aggregation" content here.
-/

@[expose] public section

namespace MathFin.DiscreteVaR

open MeasureTheory intervalIntegral

/-! ## The definition (Def 24.2) and the evaluation principle -/

/-- **Def 24.2 (VaR at a finite law)** — `finiteVaR q L α` is the infimum of the
loss levels `x` at which the `q`-mass of `{i | L i ≤ x}` reaches `α`; `q` a
probability vector in `stdSimplex ℝ ι` (hypothesis at the lemmas that need it,
matching `WorstCaseRisk`'s idiom). -/
noncomputable def finiteVaR {ι : Type*} [Fintype ι] (q L : ι → ℝ) (α : ℝ) : ℝ :=
  sInf {x | ∑ i ∈ Finset.univ.filter (fun i => L i ≤ x), q i ≥ α}

/-- **The evaluation principle**: if `v₀` is a loss level carrying `q`-mass ≥ α
and every strictly lower level carries mass < α, then `finiteVaR q L α = v₀`.
Pure order arithmetic — no hypotheses on `q` or `α`. This is the workhorse
behind items 3–6. -/
theorem finiteVaR_eq_of_forall {ι : Type*} [Fintype ι] {q L : ι → ℝ} {α v₀ : ℝ}
    (hmem : ∑ i ∈ Finset.univ.filter (fun i => L i ≤ v₀), q i ≥ α)
    (hbelow : ∀ x < v₀, ∑ i ∈ Finset.univ.filter (fun i => L i ≤ x), q i < α) :
    finiteVaR q L α = v₀ := by
  have hge : ∀ x ∈ {x | ∑ i ∈ Finset.univ.filter (fun i => L i ≤ x), q i ≥ α}, v₀ ≤ x := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    by_contra h
    linarith [hbelow x (by linarith), hx]
  refine le_antisymm ?_ (le_csInf ⟨v₀, hmem⟩ hge)
  exact csInf_le ⟨v₀, fun x hx => hge x hx⟩ hmem

/-- The loss values carrying mass ≥ α form a nonempty finite set (the maximum
loss value carries the full mass `1 ≥ α`). Attainment half of item 2. -/
theorem finiteVaR_filtered_image_nonempty {ι : Type*} [Fintype ι] [Nonempty ι]
    {q L : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) {α : ℝ} (hα1 : α ≤ 1) :
    ((Finset.univ.image L).filter
      (fun v => ∑ i ∈ Finset.univ.filter (fun i => L i ≤ v), q i ≥ α)).Nonempty := by
  obtain ⟨i₀, hi₀mem⟩ := Finset.univ_nonempty (α := ι)
  have himg : (Finset.univ.image L).Nonempty :=
    ⟨L i₀, Finset.mem_image_of_mem _ hi₀mem⟩
  obtain ⟨v₁, hv₁mem, hv₁sup⟩ := Finset.exists_mem_eq_sup' himg id
  have hLle : ∀ i, L i ≤ v₁ := fun i =>
    (Finset.le_sup' id (Finset.mem_image_of_mem _ (Finset.mem_univ i))).trans_eq hv₁sup
  have hfull : Finset.univ.filter (fun i => L i ≤ v₁) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true (hLle i) trivial
  refine ⟨v₁, Finset.mem_filter.2 ⟨hv₁mem, ?_⟩⟩
  rw [hfull, hq.2]
  exact hα1

/-- **Attainment.** The infimum over ℝ collapses to a `Finset.inf'`
over the loss *values* `Finset.image L univ` that carry `q`-mass ≥ α (a
"Finset.inf"; `Finset.inf'` because ℝ carries no order bot). Every VaR
at a finite law is attained at a loss value. -/
theorem finiteVaR_eq_value_inf {ι : Type*} [Fintype ι] [Nonempty ι] {q L : ι → ℝ}
    (hq : q ∈ stdSimplex ℝ ι) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR q L α = ((Finset.univ.image L).filter
      (fun v => ∑ i ∈ Finset.univ.filter (fun i => L i ≤ v), q i ≥ α)).inf'
      (finiteVaR_filtered_image_nonempty hq hα1) id := by
  have hT : ((Finset.univ.image L).filter
      (fun v => ∑ i ∈ Finset.univ.filter (fun i => L i ≤ v), q i ≥ α)).Nonempty :=
    finiteVaR_filtered_image_nonempty hq hα1
  obtain ⟨v₀, hv₀T, hv₀inf⟩ := Finset.exists_mem_eq_inf' hT id
  have hmemS : v₀ ∈ {x | ∑ i ∈ Finset.univ.filter (fun i => L i ≤ x), q i ≥ α} :=
    (Finset.mem_filter.mp hv₀T).2
  have hex : ∀ x ∈ {x | ∑ i ∈ Finset.univ.filter (fun i => L i ≤ x), q i ≥ α},
      ∃ v ∈ (Finset.univ.image L).filter
        (fun v => ∑ i ∈ Finset.univ.filter (fun i => L i ≤ v), q i ≥ α), v ≤ x := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    have hIx : (Finset.univ.filter (fun i => L i ≤ x)).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      have hzero : ∑ i ∈ Finset.univ.filter (fun i => L i ≤ x), q i = 0 := by
        rw [he]; exact Finset.sum_empty
      linarith [hzero, hx]
    obtain ⟨i₀, hi₀⟩ := hIx
    have hLi₀x : L i₀ ≤ x := (Finset.mem_filter.mp hi₀).2
    have hA : ((Finset.univ.image L).filter (fun v => v ≤ x)).Nonempty :=
      ⟨L i₀, Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i₀), hLi₀x⟩⟩
    obtain ⟨a₀, ha₀A, ha₀sup⟩ := Finset.exists_mem_eq_sup' hA id
    have ha₀img : a₀ ∈ Finset.univ.image L := (Finset.mem_filter.mp ha₀A).1
    have ha₀x : a₀ ≤ x := (Finset.mem_filter.mp ha₀A).2
    have hfilt : Finset.univ.filter (fun i => L i ≤ a₀) = Finset.univ.filter (fun i => L i ≤ x) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; linarith
      · intro h
        have hmemA : L i ∈ (Finset.univ.image L).filter (fun v => v ≤ x) :=
          Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), h⟩
        exact (Finset.le_sup' id hmemA).trans_eq ha₀sup
    have hFa₀ : ∑ i ∈ Finset.univ.filter (fun i => L i ≤ a₀), q i
        = ∑ i ∈ Finset.univ.filter (fun i => L i ≤ x), q i := by rw [hfilt]
    exact ⟨a₀, Finset.mem_filter.2 ⟨ha₀img, hFa₀ ▸ hx⟩, ha₀x⟩
  have hv₀eq : ((Finset.univ.image L).filter
      (fun v => ∑ i ∈ Finset.univ.filter (fun i => L i ≤ v), q i ≥ α)).inf' hT id = v₀ :=
    hv₀inf
  have hv₀le : ∀ x ∈ {x | ∑ i ∈ Finset.univ.filter (fun i => L i ≤ x), q i ≥ α}, v₀ ≤ x := by
    intro x hx
    obtain ⟨v, hvT, hvx⟩ := hex x hx
    exact (hv₀eq ▸ Finset.inf'_le id hvT : v₀ ≤ v).trans hvx
  refine le_antisymm ?_ ?_
  · exact (csInf_le ⟨v₀, fun x hx => hv₀le x hx⟩ hmemS).trans (le_of_eq hv₀eq.symm)
  · exact (le_of_eq hv₀eq).trans (le_csInf ⟨v₀, hmemS⟩ hv₀le)

/-! ## The one-bond law (Example 24.1, first half) -/

/-- Probability vector of the single $100 bond: default (`true`) with
probability `1/25`, survival (`false`) with probability `24/25`. -/
noncomputable def oneQ : Bool → ℝ := fun b => if b then 1/25 else 24/25

/-- Loss of the single $100 bond: 100 on default, 0 on survival. -/
def oneL : Bool → ℝ := fun b => if b then 100 else 0

/-- `oneQ` is a probability vector (the `stdSimplex` idiom). -/
lemma oneQ_mem_simplex : oneQ ∈ stdSimplex ℝ Bool := by
  refine ⟨fun b => ?_, ?_⟩
  · cases b <;> norm_num [oneQ]
  · simp [oneQ]; norm_num

/-- Tail mass of the one-bond law as an if-chain in the loss level `x`. -/
private lemma one_bond_tail (x : ℝ) :
    ∑ b ∈ Finset.univ.filter (fun b => oneL b ≤ x), oneQ b
      = (if (100:ℝ) ≤ x then 1/25 else 0) + (if (0:ℝ) ≤ x then 24/25 else 0) := by
  rw [Finset.sum_filter, Fintype.sum_bool]
  simp [oneL, oneQ]

/-- **Item 3 — Example 24.1, first half.** One $100 bond defaulting w.p.
`1/25`: `VaR₀.₉₅ = 0`, because the loss is 0 with probability `24/25 ≥ 19/20`. -/
theorem vaR_one_bond : finiteVaR oneQ oneL (19/20) = 0 := by
  refine finiteVaR_eq_of_forall ?_ ?_
  · rw [one_bond_tail]; norm_num
  · intro x hx
    rw [one_bond_tail]
    have e1 : ¬ ((0:ℝ) ≤ x) := by linarith
    have e2 : ¬ ((100:ℝ) ≤ x) := by linarith
    simp only [if_neg e1, if_neg e2, add_zero]
    norm_num

/-- The one-bond VaR as a function of the level `u ∈ (0, 1]`: the step quantile
`0` on `[u | u ≤ 24/25]`, `100` above. Item 7's integrand. -/
theorem vaR_one_bond_window (u : ℝ) (h0 : 0 < u) (h1 : u ≤ 1) :
    finiteVaR oneQ oneL u = if u ≤ 24/25 then 0 else 100 := by
  by_cases hu : u ≤ 24/25
  · rw [if_pos hu]
    refine finiteVaR_eq_of_forall ?_ ?_
    · rw [one_bond_tail]; norm_num
      exact hu
    · intro x hx
      rw [one_bond_tail]
      have e1 : ¬ ((0:ℝ) ≤ x) := by linarith
      have e2 : ¬ ((100:ℝ) ≤ x) := by linarith
      simp only [if_neg e1, if_neg e2, add_zero]
      exact h0
  · rw [if_neg hu]
    refine finiteVaR_eq_of_forall ?_ ?_
    · rw [one_bond_tail]; norm_num
      exact h1
    · intro x hx
      rw [one_bond_tail]
      by_cases hx0 : (0:ℝ) ≤ x
      · have e2 : ¬ ((100:ℝ) ≤ x) := by linarith
        simp only [if_pos hx0, if_neg e2]
        linarith
      · have e1 : ¬ ((0:ℝ) ≤ x) := by linarith
        have e2 : ¬ ((100:ℝ) ≤ x) := by linarith
        simp only [if_neg e1, if_neg e2, add_zero]
        exact h0

/-! ## The split law, lumped (Example 24.1, second half) -/

/-- Probability vector of the two $50 half-bonds' total loss, lumped into three
states: neither defaults (`0`, w.p. `9216/10000 = (24/25)²`), exactly one
(`1`, w.p. `768/10000 = 2·(24/25)(1/25)`), both (`2`, w.p. `16/10000`). -/
noncomputable def splitQ : Fin 3 → ℝ :=
  fun i => if i = 0 then 9216/10000 else if i = 1 then 768/10000 else 16/10000

/-- Total loss of the two half-bonds at the lumped states: 0, 50, 100. -/
def splitL : Fin 3 → ℝ := fun i => if i = 0 then 0 else if i = 1 then 50 else 100

/-- `splitQ` is a probability vector. -/
lemma splitQ_mem_simplex : splitQ ∈ stdSimplex ℝ (Fin 3) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [splitQ]
  · simp [splitQ, Fin.sum_univ_three]; norm_num

/-- Tail mass of the lumped split law as an if-chain in the loss level `x`. -/
private lemma split_tail (x : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => splitL i ≤ x), splitQ i
      = (if (0:ℝ) ≤ x then 9216/10000 else 0)
        + (if (50:ℝ) ≤ x then 768/10000 else 0)
        + (if (100:ℝ) ≤ x then 16/10000 else 0) := by
  rw [Finset.sum_filter, Fin.sum_univ_three]
  simp [splitL, splitQ]

/-- **Item 4 — Example 24.1, second half.** The same credit exposure split
into two independent $50 bonds (lumped three-state law):
`VaR₀.₉₅ = 50`, because `P(L = 0) = 0.9216 < 0.95` but
`P(L ≤ 50) = 0.9984 ≥ 0.95`. -/
theorem vaR_two_halves : finiteVaR splitQ splitL (19/20) = 50 := by
  refine finiteVaR_eq_of_forall ?_ ?_
  · rw [split_tail]; norm_num
  · intro x hx
    rw [split_tail]
    by_cases hx0 : (0:ℝ) ≤ x
    · have e50 : ¬ ((50:ℝ) ≤ x) := by linarith
      have e100 : ¬ ((100:ℝ) ≤ x) := by linarith
      simp only [if_pos hx0, if_neg e50, if_neg e100, add_zero]
      norm_num
    · have e0 : ¬ ((0:ℝ) ≤ x) := by linarith
      have e50 : ¬ ((50:ℝ) ≤ x) := by linarith
      have e100 : ¬ ((100:ℝ) ≤ x) := by linarith
      simp only [if_neg e0, if_neg e50, if_neg e100, add_zero]
      norm_num

/-! ## The joint two-half law on `Bool × Bool` (the headline) -/

/-- Joint law of the two independent $50 half-bonds (`true` = default): the
product of the marginals `1/25` / `24/25`. -/
noncomputable def jointQ : Bool × Bool → ℝ :=
  fun p => (if p.1 then 1/25 else 24/25) * (if p.2 then 1/25 else 24/25)

/-- Loss of the first half-bond: 50 if it defaults, else 0. -/
def halfL₁ : Bool × Bool → ℝ := fun p => if p.1 then 50 else 0

/-- Loss of the second half-bond: 50 if it defaults, else 0. -/
def halfL₂ : Bool × Bool → ℝ := fun p => if p.2 then 50 else 0

/-- `jointQ` is a probability vector (product of the two marginal vectors). -/
lemma jointQ_mem_simplex : jointQ ∈ stdSimplex ℝ (Bool × Bool) := by
  refine ⟨fun p => ?_, ?_⟩
  · rcases p with ⟨a, b⟩
    rcases a <;> rcases b <;> simp [jointQ] <;> norm_num
  · have hrow : ∀ a : Bool, ∑ b, jointQ (a, b) = (if a then 1/25 else 24/25) := by
      intro a
      rw [Fintype.sum_bool]; cases a <;> simp [jointQ] <;> norm_num
    rw [Fintype.sum_prod_type]; simp only [hrow, Fintype.sum_bool]; norm_num

/-- Tail mass of the first half-bond's loss under the joint law (its marginal
is the one-bond law rescaled: `24/25` below 50). -/
private lemma joint_half1_tail (x : ℝ) :
    ∑ p ∈ Finset.univ.filter (fun p => halfL₁ p ≤ x), jointQ p
      = (if (50:ℝ) ≤ x then 1/25 else 0) + (if (0:ℝ) ≤ x then 24/25 else 0) := by
  by_cases h50 : (50:ℝ) ≤ x
  · by_cases h0 : (0:ℝ) ≤ x
    · have hf : Finset.univ.filter (fun p => halfL₁ p ≤ x) = Finset.univ := by
        ext p
        rcases p with ⟨a, b⟩
        rcases a <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and, halfL₁]
          <;> simp <;> linarith
      rw [hf, jointQ_mem_simplex.2]
      simp only [if_pos h50, if_pos h0]; norm_num
    · exact absurd (by linarith : (0:ℝ) ≤ x) h0
  · by_cases h0 : (0:ℝ) ≤ x
    · rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
      simp [halfL₁, jointQ, h50, h0]; norm_num
    · rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
      simp [halfL₁, h50, h0]

/-- Tail mass of the second half-bond's loss under the joint law (symmetric to
`joint_half1_tail`). -/
private lemma joint_half2_tail (x : ℝ) :
    ∑ p ∈ Finset.univ.filter (fun p => halfL₂ p ≤ x), jointQ p
      = (if (50:ℝ) ≤ x then 1/25 else 0) + (if (0:ℝ) ≤ x then 24/25 else 0) := by
  by_cases h50 : (50:ℝ) ≤ x
  · by_cases h0 : (0:ℝ) ≤ x
    · have hf : Finset.univ.filter (fun p => halfL₂ p ≤ x) = Finset.univ := by
        ext p
        rcases p with ⟨a, b⟩
        rcases b <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and, halfL₂]
          <;> simp <;> linarith
      rw [hf, jointQ_mem_simplex.2]
      simp only [if_pos h50, if_pos h0]; norm_num
    · exact absurd (by linarith : (0:ℝ) ≤ x) h0
  · by_cases h0 : (0:ℝ) ≤ x
    · rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
      simp [halfL₂, jointQ, h50, h0]; norm_num
    · rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
      simp [halfL₂, h50, h0]

/-- Tail mass of the joint loss `halfL₁ + halfL₂` under the joint law: the
lumped split law's masses (0.9216 / +0.0768 / +0.0016). -/
private lemma joint_tail (x : ℝ) :
    ∑ p ∈ Finset.univ.filter (fun p => (halfL₁ + halfL₂) p ≤ x), jointQ p
      = (if (0:ℝ) ≤ x then 9216/10000 else 0)
        + (if (50:ℝ) ≤ x then 768/10000 else 0)
        + (if (100:ℝ) ≤ x then 16/10000 else 0) := by
  have ktt : (halfL₁ (true, true) + halfL₂ (true, true) ≤ x) = ((100:ℝ) ≤ x) := by
    norm_num [halfL₁, halfL₂]
  have ktf : (halfL₁ (true, false) + halfL₂ (true, false) ≤ x) = ((50:ℝ) ≤ x) := by
    norm_num [halfL₁, halfL₂]
  have kft : (halfL₁ (false, true) + halfL₂ (false, true) ≤ x) = ((50:ℝ) ≤ x) := by
    norm_num [halfL₁, halfL₂]
  have kff : (halfL₁ (false, false) + halfL₂ (false, false) ≤ x) = ((0:ℝ) ≤ x) := by
    norm_num [halfL₁, halfL₂]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Pi.add_apply, ktt, ktf, kft, kff]
  by_cases h0 : (0:ℝ) ≤ x
  · by_cases h50 : (50:ℝ) ≤ x
    · by_cases h100 : (100:ℝ) ≤ x
      · simp only [if_pos h0, if_pos h50, if_pos h100, jointQ]; norm_num
      · simp only [if_pos h0, if_pos h50, if_neg h100, jointQ]; norm_num
    · have e100 : ¬ ((100:ℝ) ≤ x) := by linarith
      simp only [if_pos h0, if_neg h50, if_neg e100, jointQ]; norm_num
  · have e50 : ¬ ((50:ℝ) ≤ x) := by linarith
    have e100 : ¬ ((100:ℝ) ≤ x) := by linarith
    simp only [if_neg h0, if_neg e50, if_neg e100, jointQ]; norm_num

/-- The half-bond VaR as a function of the level `α ∈ (0, 1]`. -/
theorem vaR_half_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR jointQ halfL₁ α = if α ≤ 24/25 then 0 else 50 := by
  by_cases h24 : α ≤ 24/25
  · rw [if_pos h24]
    refine finiteVaR_eq_of_forall ?_ ?_
    · rw [joint_half1_tail]; norm_num; linarith
    · intro x hx
      rw [joint_half1_tail]
      have e1 : ¬ ((0:ℝ) ≤ x) := by linarith
      have e2 : ¬ ((50:ℝ) ≤ x) := by linarith
      simp only [if_neg e1, if_neg e2]; linarith
  · rw [if_neg h24]
    refine finiteVaR_eq_of_forall ?_ ?_
    · rw [joint_half1_tail]; norm_num; linarith
    · intro x hx
      rw [joint_half1_tail]
      by_cases hx0 : (0:ℝ) ≤ x
      · have e2 : ¬ ((50:ℝ) ≤ x) := by linarith
        simp only [if_pos hx0, if_neg e2]; linarith
      · have e1 : ¬ ((0:ℝ) ≤ x) := by linarith
        have e2 : ¬ ((50:ℝ) ≤ x) := by linarith
        simp only [if_neg e1, if_neg e2]; linarith

/-- The second half-bond's VaR window (symmetric). -/
theorem vaR_half2_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR jointQ halfL₂ α = if α ≤ 24/25 then 0 else 50 := by
  by_cases h24 : α ≤ 24/25
  · rw [if_pos h24]
    refine finiteVaR_eq_of_forall ?_ ?_
    · rw [joint_half2_tail]; norm_num; linarith
    · intro x hx
      rw [joint_half2_tail]
      have e1 : ¬ ((0:ℝ) ≤ x) := by linarith
      have e2 : ¬ ((50:ℝ) ≤ x) := by linarith
      simp only [if_neg e1, if_neg e2]; linarith
  · rw [if_neg h24]
    refine finiteVaR_eq_of_forall ?_ ?_
    · rw [joint_half2_tail]; norm_num; linarith
    · intro x hx
      rw [joint_half2_tail]
      by_cases hx0 : (0:ℝ) ≤ x
      · have e2 : ¬ ((50:ℝ) ≤ x) := by linarith
        simp only [if_pos hx0, if_neg e2]; linarith
      · have e1 : ¬ ((0:ℝ) ≤ x) := by linarith
        have e2 : ¬ ((50:ℝ) ≤ x) := by linarith
        simp only [if_neg e1, if_neg e2]; linarith

/-- The joint (two-half) VaR as a function of the level `α ∈ (0, 1]`: 0 below
the atom mass `9216/10000`, 50 through the `9984/10000` mass, 100 above. -/
theorem vaR_joint_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finiteVaR jointQ (halfL₁ + halfL₂) α
      = if α ≤ 9216/10000 then 0 else if α ≤ 9984/10000 then 50 else 100 := by
  by_cases hA : α ≤ 9216/10000
  · rw [if_pos hA]
    refine finiteVaR_eq_of_forall ?_ ?_
    · rw [joint_tail]; norm_num; linarith
    · intro x hx
      rw [joint_tail]
      have e1 : ¬ ((0:ℝ) ≤ x) := by linarith
      have e2 : ¬ ((50:ℝ) ≤ x) := by linarith
      have e3 : ¬ ((100:ℝ) ≤ x) := by linarith
      simp only [if_neg e1, if_neg e2, if_neg e3]; linarith
  · by_cases hB : α ≤ 9984/10000
    · rw [if_neg hA, if_pos hB]
      refine finiteVaR_eq_of_forall ?_ ?_
      · rw [joint_tail]; norm_num; linarith
      · intro x hx
        rw [joint_tail]
        by_cases hx0 : (0:ℝ) ≤ x
        · have e2 : ¬ ((50:ℝ) ≤ x) := by linarith
          have e3 : ¬ ((100:ℝ) ≤ x) := by linarith
          simp only [if_pos hx0, if_neg e2, if_neg e3]; linarith
        · have e1 : ¬ ((0:ℝ) ≤ x) := by linarith
          have e2 : ¬ ((50:ℝ) ≤ x) := by linarith
          have e3 : ¬ ((100:ℝ) ≤ x) := by linarith
          simp only [if_neg e1, if_neg e2, if_neg e3]; linarith
    · rw [if_neg hA, if_neg hB]
      refine finiteVaR_eq_of_forall ?_ ?_
      · rw [joint_tail]; norm_num; linarith
      · intro x hx
        rw [joint_tail]
        by_cases hx50 : (50:ℝ) ≤ x
        · by_cases hx100 : (100:ℝ) ≤ x
          · have e1 : (0:ℝ) ≤ x := by linarith
            simp only [if_pos e1, if_pos hx50, if_neg (by linarith : ¬ ((100:ℝ) ≤ x))]
            linarith
          · have e1 : (0:ℝ) ≤ x := by linarith
            simp only [if_pos e1, if_pos hx50, if_neg hx100]; linarith
        · by_cases hx0 : (0:ℝ) ≤ x
          · have e3 : ¬ ((100:ℝ) ≤ x) := by linarith
            simp only [if_pos hx0, if_neg hx50, if_neg e3]; linarith
          · have e2 : ¬ ((50:ℝ) ≤ x) := by linarith
            have e3 : ¬ ((100:ℝ) ≤ x) := by linarith
            simp only [if_neg hx0, if_neg e2, if_neg e3]; linarith

/-- Each half-bond alone has `VaR₀.₉₅ = 0` (its marginal loss is 0 w.p.
`24/25 ≥ 19/20`). -/
theorem vaR_half_eq_zero : finiteVaR jointQ halfL₁ (19/20) = 0 := by
  rw [vaR_half_window (19/20) (by norm_num) (by norm_num), if_pos (by norm_num)]

theorem vaR_half2_eq_zero : finiteVaR jointQ halfL₂ (19/20) = 0 := by
  rw [vaR_half2_window (19/20) (by norm_num) (by norm_num), if_pos (by norm_num)]

/-- The joint two-half position on its honest product space:
`VaR₀.₉₅ = 50` — the same number as the lumped `vaR_two_halves`. -/
theorem vaR_joint_two_halves : finiteVaR jointQ (halfL₁ + halfL₂) (19/20) = 50 := by
  rw [vaR_joint_window (19/20) (by norm_num) (by norm_num), if_neg (by norm_num),
    if_pos (by norm_num)]

/-- **Item 5 — THE HEADLINE (Example 24.1).** Subadditivity fails at the 95%
level, as a *theorem* on one probability space: each $50 half-bond has
`VaR = 0`, their sum (the $100 exposure, same law as the lumped split law)
has `VaR = 50` — `50 > 0 + 0`. VaR punishes the split. -/
theorem vaR_subadditivity_fails :
    ¬ (finiteVaR jointQ (halfL₁ + halfL₂) (19/20)
      ≤ finiteVaR jointQ halfL₁ (19/20) + finiteVaR jointQ halfL₂ (19/20)) := by
  intro h
  rw [vaR_joint_two_halves, vaR_half_eq_zero, vaR_half2_eq_zero] at h
  norm_num at h

/-- **Item 6 — the α-window (chapter exercise, p. 421, sharpened).** The
subadditivity failure happens *exactly* for `9216/10000 < α ≤ 24/25`. The
right endpoint is included under Def 24.2's `P(L ≤ x) ≥ α` convention (at
`α = 24/25` the halves stay at VaR 0 while the joint stays at 50); the chapter
states the open interval. `α = 9216/10000` itself is excluded — the joint VaR
collapses to 0 there. -/
theorem vaR_counterexample_window (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (¬ (finiteVaR jointQ (halfL₁ + halfL₂) α
      ≤ finiteVaR jointQ halfL₁ α + finiteVaR jointQ halfL₂ α)
      ↔ 9216/10000 < α ∧ α ≤ 24/25) := by
  rw [vaR_joint_window α hα0 hα1, vaR_half_window α hα0 hα1,
    vaR_half2_window α hα0 hα1]
  by_cases hA : α ≤ 9216/10000
  · have h24 : α ≤ 24/25 := by
      have hle : (9216/10000 : ℝ) ≤ 24/25 := by norm_num
      linarith
    simp only [if_pos hA]
    simp only [if_pos h24]
    exact iff_of_false (by simp) (by rintro ⟨h1, -⟩; linarith)
  · by_cases h24 : α ≤ 24/25
    · have hB : α ≤ 9984/10000 := by
        have hle : (24/25 : ℝ) ≤ 9984/10000 := by norm_num
        linarith
      simp only [if_neg hA, if_pos hB]
      simp only [if_pos h24]
      constructor
      · intro _; exact ⟨by linarith, h24⟩
      · intro _; norm_num
    · rw [if_neg h24]
      by_cases hB : α ≤ 9984/10000
      · rw [if_neg hA, if_pos hB]
        exact iff_of_false (by norm_num) (by rintro ⟨-, h⟩; linarith)
      · rw [if_neg hA, if_neg hB]
        exact iff_of_false (by norm_num) (by rintro ⟨-, h⟩; linarith)

/-! ## Expected shortfall at the one-bond law (Def 24.3) -/

/-- **Def 24.3 (ES at a finite law)** — the quantile average: `1/(1-α)` times
the integral of the quantile function `u ↦ finiteVaR q L u` over `[α, 1]`. -/
noncomputable def finiteES {ι : Type*} [Fintype ι] (q L : ι → ℝ) (α : ℝ) : ℝ :=
  (1 / (1 - α)) * ∫ u in α..1, finiteVaR q L u

/-- **Item 7 — "eighty".** Def 24.3 at the one-bond law, `α = 19/20`: the
quantile function is the step `0` on `[19/20, 24/25]`, `100` on `(24/25, 1]`,
so the average is `(1/(1/20)) · 100 · (1 - 24/25) = 80`. -/
theorem es_one_bond_eq_80 : finiteES oneQ oneL (19/20) = 80 := by
  have hstep : ∀ u ∈ Set.Icc (19/20:ℝ) 1,
      finiteVaR oneQ oneL u = if u ≤ 24/25 then 0 else 100 := fun u hu =>
    vaR_one_bond_window u (by linarith [hu.1]) (by linarith [hu.2])
  have hz1 : ∀ u ∈ Set.Icc (19/20:ℝ) (24/25), finiteVaR oneQ oneL u = 0 := by
    intro u hu
    rw [hstep u ⟨hu.1, by linarith [hu.2]⟩, if_pos (by linarith [hu.2])]
  have hc1 : ∀ u ∈ Set.Ioc (24/25:ℝ) 1, finiteVaR oneQ oneL u = 100 := by
    intro u hu
    rw [hstep u ⟨by linarith [hu.1], hu.2⟩, if_neg (by linarith [hu.1])]
  -- integrability: piece 1 is pointwise 0 on the closed interval (continuous there);
  -- piece 2 is ae-equal to the constant 100 on the half-open interval.
  have h1int : IntervalIntegrable (finiteVaR oneQ oneL) volume (19/20:ℝ) (24/25) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num : (19/20:ℝ) ≤ 24/25)]
    exact continuousOn_const.congr (fun u hu => hz1 u hu)
  have h2int : IntervalIntegrable (finiteVaR oneQ oneL) volume (24/25:ℝ) 1 := by
    refine IntervalIntegrable.congr_ae
      (intervalIntegrable_const (c := (100:ℝ))) ?_
    filter_upwards [ae_restrict_mem
      (by rw [Set.uIoc_of_le (by norm_num : (24/25:ℝ) ≤ 1)]; exact measurableSet_Ioc)] with u hu
    rw [Set.uIoc_of_le (by norm_num : (24/25:ℝ) ≤ 1)] at hu
    exact (hc1 u hu).symm
  -- values: 0 on the first piece, 4 on the second.
  have hval1 : ∫ u in (19/20:ℝ)..(24/25), finiteVaR oneQ oneL u = 0 := by
    rw [intervalIntegral.integral_congr (f := finiteVaR oneQ oneL)
      (g := fun _ => (0:ℝ)) (by
        intro u hu
        rw [Set.uIcc_of_le (by norm_num : (19/20:ℝ) ≤ 24/25)] at hu
        exact hz1 u hu),
      intervalIntegral.integral_const]
    norm_num
  have hval2 : ∫ u in (24/25:ℝ)..1, finiteVaR oneQ oneL u = 4 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (100:ℝ)) (by
        refine Filter.Eventually.of_forall
          (fun u (hu : u ∈ Set.uIoc (24/25:ℝ) 1) => ?_)
        rw [Set.uIoc_of_le (by norm_num : (24/25:ℝ) ≤ 1)] at hu
        exact hc1 u hu),
      intervalIntegral.integral_const]
    norm_num
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h1int h2int
  simp only [finiteES]
  rw [← hsplit, hval1, hval2]
  norm_num

/-! ## The conditional tail mean at an atom ("four against eighty") -/

/-- **`E[L | L ≥ VaR_α]` at a finite law**: the `q`-weighted mean of `L` over
the tail event `{i | finiteVaR q L α ≤ L i}`. -/
noncomputable def condTailMean {ι : Type*} [Fintype ι] (q L : ι → ℝ) (α : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => finiteVaR q L α ≤ L i), q i * L i) /
    (∑ i ∈ Finset.univ.filter (fun i => finiteVaR q L α ≤ L i), q i)

/-- **Item 8 — "four".** At the one-bond law the tail event `{L ≥ VaR₀.₉₅} =
{L ≥ 0}` is the whole state space (an atom carries the VaR), so the
"conditional" tail mean collapses to the unconditional expectation `E[L] = 4` —
while ES is 80. The conditional form is not imprecise but useless at atoms. -/
theorem condExp_tail_eq_mean_one_bond :
    condTailMean oneQ oneL (19/20) = ∑ b, oneQ b * oneL b ∧ (∑ b, oneQ b * oneL b) = 4 := by
  have hfilt : Finset.univ.filter (fun i => finiteVaR oneQ oneL (19/20) ≤ oneL i)
      = Finset.univ := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, vaR_one_bond, oneL]
    cases b <;> simp
  constructor
  · simp only [condTailMean]
    rw [hfilt, oneQ_mem_simplex.2, div_one]
  · simp [oneQ, oneL]; norm_num

/-! ## Stretch: Thm 24.4's bounded-density supremum at the two-state law -/

/-- **Stretch — Thm 24.4 at the two-state law.** The supremum of `E[Z·L]` over
densities `Z` with `0 ≤ Z ≤ 1/(1-α) = 20` and `E[Z] = 1` equals `80` — the ES
value (`es_one_bond_eq_80`). The two-state LP is trivial (the objective
`E[Z·L] = 4·Z_def` touches only the default coordinate), which is exactly why
the example is provable without the RN/ess-sup machinery the general theorem
needs. The optimizer `Z*` = 20 on default, `5/24` on survival. -/
theorem es_sup_representation_finite :
    IsLUB ((fun Z : Bool → ℝ => ∑ b, oneQ b * Z b * oneL b) ''
      {Z : Bool → ℝ | (∀ b, 0 ≤ Z b ∧ Z b ≤ 20) ∧ ∑ b, oneQ b * Z b = 1}) 80 := by
  constructor
  · rintro v ⟨Z, ⟨hcap, -⟩, rfl⟩
    show ∑ b, oneQ b * Z b * oneL b ≤ 80
    rw [Fintype.sum_bool]
    have hval : oneQ true * Z true * oneL true + oneQ false * Z false * oneL false
        = 4 * Z true := by
      norm_num [oneQ, oneL]
      ring_nf
    rw [hval]
    exact (mul_le_mul_of_nonneg_left (hcap true).2 (by norm_num : (0:ℝ) ≤ 4)).trans_eq
      (by norm_num : (4:ℝ) * 20 = 80)
  · intro b hb
    have hZstar : (fun c : Bool => if c then (20:ℝ) else 5/24)
        ∈ {Z : Bool → ℝ | (∀ b, 0 ≤ Z b ∧ Z b ≤ 20) ∧ ∑ b, oneQ b * Z b = 1} := by
      constructor
      · intro c; cases c <;> simp <;> norm_num
      · rw [Fintype.sum_bool]; simp [oneQ]; norm_num
    have hv : ∑ b, oneQ b * (if b then (20:ℝ) else 5/24) * oneL b ≤ b :=
      hb ⟨(fun c : Bool => if c then (20:ℝ) else 5/24), hZstar, rfl⟩
    rw [Fintype.sum_bool] at hv
    simp only [oneQ, oneL] at hv
    norm_num at hv
    exact hv

end MathFin.DiscreteVaR
