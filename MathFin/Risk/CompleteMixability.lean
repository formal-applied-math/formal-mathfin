/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Laws.ConvexOrder
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Complete mixability

A law `μ` is **`n`-completely mixable** when there are `n` random variables, each with law `μ`,
whose sum is almost surely constant. Such a coupling is the extreme negative dependence of risk
aggregation: among all sums of `n` risks with law `μ`, the constant one is the smallest in convex
order (`convexOrder_sum_of_completelyMixable`), so it minimises every risk measure that respects
convex order; for expected shortfall that is `expectedShortfall_le_of_convexOrder`. Sharp
bounds on the `VaR` of a sum with given marginals are built from completely mixable pieces.

This file gives a criterion and the cases it proves for uniform laws. If `n` maps preserve `μ`
and their values add up to a constant, the joint law of the images is a complete mix
(`CompletelyMixable.of_measurePreserving`). Mixes concatenate, so `n`- and `m`-mixability give
`(n + m)`-mixability. For uniform laws on sets of `ℝᵈ`, the maps come from the symmetries of
the set:

* a set symmetric about a point `c` is `2`-mixable through `x ↦ 2c − x`, hence `2k`-mixable;
* a simplex with vertices `b₀, …, b_{n−1}` is `n`-mixable through the `n` affine maps that shift
  the vertices cyclically, `b j ↦ b (j + k)`: in barycentric coordinates the images of `x` add
  up to `b₀ + ⋯ + b_{n−1}`.

Whether the uniform law on every convex body of `ℝᵈ` is `n`-mixable for all `n ≥ d + 1` is open
(MF-OP-016, Wang 2015, Open Problem 5); the simplex result is its boundary case `n = d + 1` for
simplices, and the frontier statement is `MathFinFrontier.uniform_convex_completelyMixable`.

## Main definitions

* `CompletelyMixable n μ`: there is a coupling of `n` copies of `μ` with an a.s. constant sum.
* `simplexShift b k`: the affine map of an affine basis `b` sending `b j` to `b (j + k)`.

## Main results

* `CompletelyMixable.of_measurePreserving`: measure-preserving maps with a constant sum give a
  complete mix.
* `CompletelyMixable.add`, `CompletelyMixable.mul`: mixes concatenate.
* `measurePreserving_of_preimage_eq`: an affine bijection mapping a set of finite positive Haar
  measure onto itself preserves the Haar measure.
* `completelyMixable_of_symmetric`: the uniform law on a centrally symmetric set is
  `2k`-completely mixable.
* `completelyMixable_simplex`: the uniform law on a simplex with `n` vertices is
  `n`-completely mixable.
* `convexOrder_sum_of_completelyMixable`: the sum of a complete mix is below, in convex order,
  the sum of every other coupling of the same law.

## References

* [R. Wang, *Current open questions in complete mixability*][Wang2015CompleteMixability],
  §2.5, Open Problem 5
* [C. Bernard, X. Jiang and R. Wang, *Risk aggregation with dependence
  uncertainty*][BernardJiangWang2014]

## Tags

complete mixability, joint mixability, risk aggregation, dependence uncertainty, convex order,
uniform distribution, simplex, central symmetry, MSC 60E05, MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- **Joint mixability**: a coupling of the laws `μ i`, i.e. a probability measure on `Fin n → E`
whose `i`-th coordinate has law `μ i`, under which the sum is almost surely constant. -/
def JointlyMixable {E : Type*} [MeasurableSpace E] [AddCommMonoid E] {n : ℕ}
    (μ : Fin n → Measure E) : Prop :=
  ∃ π : Measure (Fin n → E), IsProbabilityMeasure π ∧ (∀ i, π.map (fun x ↦ x i) = μ i) ∧
    ∃ c, ∀ᵐ x ∂π, ∑ i, x i = c

/-- **Complete mixability**: a coupling of `n` copies of `μ`, i.e. a probability measure on
`Fin n → E` whose coordinates all have law `μ`, under which the sum is almost surely constant.
It is joint mixability of `n` copies of one law. -/
def CompletelyMixable {E : Type*} [MeasurableSpace E] [AddCommMonoid E] (n : ℕ)
    (μ : Measure E) : Prop :=
  JointlyMixable fun _ : Fin n ↦ μ

section Criterion

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  [SecondCountableTopology E]

lemma measurableSet_sum_eq {n : ℕ} (c : E) : MeasurableSet {x : Fin n → E | ∑ i, x i = c} :=
  measurableSet_eq_fun (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i) measurable_const

/-- **Random variables with a constant sum give a joint mix.** If `X i` has law `μ i` under a
probability measure `P` and `∑ i, X i` is a.s. constant, the joint law of the `X i` is a joint
mix of the `μ i`. This is the form in which constructions produce mixes. -/
theorem JointlyMixable.of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {μ : Fin n → Measure E} {X : Fin n → Ω → E}
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, P.map (X i) = μ i) (c : E)
    (hc : ∀ᵐ ω ∂P, ∑ i, X i ω = c) : JointlyMixable μ := by
  have hF : Measurable fun ω i ↦ X i ω := measurable_pi_iff.2 hX
  refine ⟨P.map fun ω i ↦ X i ω, (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).2 inferInstance, fun i ↦ ?_, c, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply i) hF]
    exact hlaw i
  · exact (ae_map_iff hF.aemeasurable (measurableSet_sum_eq c)).2 hc

/-- **An affine image of a joint mix is a joint mix.** -/
theorem JointlyMixable.map_affine {n : ℕ} {μ : Fin n → Measure ℝ} (h : JointlyMixable μ)
    (a b : ℝ) : JointlyMixable fun i ↦ (μ i).map fun x ↦ a * x + b := by
  obtain ⟨π, hπ, hm, c, hc⟩ := h
  have hg : Measurable fun (x : Fin n → ℝ) i ↦ a * x i + b :=
    measurable_pi_iff.2 fun i ↦ by fun_prop
  refine ⟨π.map fun x i ↦ a * x i + b, (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 hπ, fun i ↦ ?_,
    a * c + n * b, ?_⟩
  · show _ = (μ i).map _
    rw [Measure.map_map (measurable_pi_apply i) hg, ← hm i,
      Measure.map_map (by fun_prop) (measurable_pi_apply i)]
    rfl
  · refine (ae_map_iff hg.aemeasurable (measurableSet_sum_eq _)).2 ?_
    filter_upwards [hc] with x hx
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, hx]

namespace CompletelyMixable

variable {μ : Measure E} {n m : ℕ}

/-- **Mixing maps.** If the maps `f i` preserve `μ` and `∑ i, f i x` is a.s. constant, the law of
`(f 1 X, …, f n X)` for `X ∼ μ` is a complete mix. -/
theorem of_measurePreserving [IsProbabilityMeasure μ] (f : Fin n → E → E)
    (hf : ∀ i, MeasurePreserving (f i) μ μ) (c : E) (hc : ∀ᵐ x ∂μ, ∑ i, f i x = c) :
    CompletelyMixable n μ := by
  have hF : Measurable fun x i ↦ f i x := measurable_pi_iff.2 fun i ↦ (hf i).measurable
  refine ⟨μ.map fun x i ↦ f i x, inferInstance, fun i ↦ ?_, c, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply i) hF]
    exact (hf i).map_eq
  · exact (ae_map_iff hF.aemeasurable (measurableSet_sum_eq c)).2 hc

/-- **Mixes concatenate**: independent `n`- and `m`-mixes side by side form an `(n + m)`-mix. -/
theorem add (h₁ : CompletelyMixable n μ) (h₂ : CompletelyMixable m μ) :
    CompletelyMixable (n + m) μ := by
  obtain ⟨π₁, _, hm₁, c₁, hc₁⟩ := h₁
  obtain ⟨π₂, _, hm₂, c₂, hc₂⟩ := h₂
  have hA : Measurable fun p : (Fin n → E) × (Fin m → E) ↦ Fin.append p.1 p.2 := by
    refine measurable_pi_iff.2 fun i ↦ ?_
    induction i using Fin.addCases with
    | left j => simp only [Fin.append_left]; exact (measurable_pi_apply j).comp measurable_fst
    | right j => simp only [Fin.append_right]; exact (measurable_pi_apply j).comp measurable_snd
  refine ⟨(π₁.prod π₂).map fun p ↦ Fin.append p.1 p.2, inferInstance, fun i ↦ ?_, c₁ + c₂, ?_⟩
  · rw [Measure.map_map (measurable_pi_apply i) hA]
    induction i using Fin.addCases with
    | left j =>
      rw [show ((fun x ↦ x (Fin.castAdd m j)) ∘ fun p : _ × _ ↦ Fin.append p.1 p.2) =
          (fun x ↦ x j) ∘ Prod.fst by ext p; simp,
        ← Measure.map_map (measurable_pi_apply j) measurable_fst, Measure.map_fst_prod,
        measure_univ, one_smul, hm₁]
    | right j =>
      rw [show ((fun x ↦ x (Fin.natAdd n j)) ∘ fun p : _ × _ ↦ Fin.append p.1 p.2) =
          (fun x ↦ x j) ∘ Prod.snd by ext p; simp,
        ← Measure.map_map (measurable_pi_apply j) measurable_snd, Measure.map_snd_prod,
        measure_univ, one_smul, hm₂]
  · rw [ae_map_iff hA.aemeasurable (measurableSet_sum_eq _)]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hc₁,
      Measure.quasiMeasurePreserving_snd.ae hc₂] with p h₁ h₂
    simp [Fin.sum_univ_add, h₁, h₂]

/-- An `n`-mixable law is `k n`-mixable for every `k ≥ 1`. -/
theorem mul (h : CompletelyMixable n μ) {k : ℕ} (hk : 1 ≤ k) : CompletelyMixable (k * n) μ := by
  induction k, hk using Nat.le_induction with
  | base => simpa using h
  | succ k _ ih => simpa [add_mul] using ih.add h

end CompletelyMixable

end Criterion

/-- A measure-preserving map that maps `C` onto itself preserves the conditional law on `C`. -/
lemma _root_.MeasureTheory.MeasurePreserving.cond {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → α} (hf : MeasurePreserving f μ μ) {C : Set α}
    (hC : MeasurableSet C) (hfC : f ⁻¹' C = C) : MeasurePreserving f μ[|C] μ[|C] := by
  have := hf.restrict_preimage hC
  rw [hfC] at this
  refine ⟨hf.measurable, ?_⟩
  rw [ProbabilityTheory.cond, Measure.map_smul, this.map_eq]
  exact hf.measurable.aemeasurable

section Simplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- The affine map of an affine basis that shifts the vertices, `b j ↦ b (j + k)`: the point
with barycentric coordinates `λ` goes to the point with coordinates `j ↦ λ (j − k)`. -/
noncomputable def simplexShift (b : AffineBasis (Fin n) ℝ E) (k : Fin n) : E →ᵃ[ℝ] E where
  toFun x := ∑ j, b.coord (j - k) x • b j
  linear := ∑ j, (LinearMap.id.smulRight (b j)).comp (b.coord (j - k)).linear
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smulRight_apply,
      LinearMap.id_apply, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← vadd_eq_add v p, AffineMap.map_vadd, vadd_eq_add]

lemma simplexShift_apply (b : AffineBasis (Fin n) ℝ E) (k : Fin n) (x : E) :
    simplexShift b k x = ∑ j, b.coord (j - k) x • b j := rfl

lemma coord_simplexShift [NeZero n] (b : AffineBasis (Fin n) ℝ E) (k j : Fin n) (x : E) :
    b.coord j (simplexShift b k x) = b.coord (j - k) x := by
  have hw : ∑ j, b.coord (j - k) x = 1 := by
    rw [← b.sum_coord_apply_eq_one x]
    exact Fintype.sum_equiv (Equiv.subRight k) _ _ fun _ ↦ rfl
  have := b.coord_apply_combination_of_mem (Finset.mem_univ j) hw
  rwa [Finset.univ.affineCombination_eq_linear_combination _ _ hw, ← simplexShift_apply] at this

/-- The shifts of a point add up to the sum of the vertices. -/
lemma sum_simplexShift [NeZero n] (b : AffineBasis (Fin n) ℝ E) (x : E) :
    ∑ k, simplexShift b k x = ∑ j, b j := by
  simp_rw [simplexShift_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have : ∑ k, b.coord (j - k) x = 1 := by
    rw [← b.sum_coord_apply_eq_one x]
    exact Fintype.sum_equiv (Equiv.subLeft j) _ _ fun _ ↦ rfl
  rw [← Finset.sum_smul, this, one_smul]

end Simplex

section Uniform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **An affine bijection that maps a set of finite positive Haar measure onto itself preserves
the Haar measure.** It scales the Haar measure by `|det|⁻¹`, and the set's measure shows the
factor is `1`. -/
lemma measurePreserving_of_preimage_eq (f : E →ᵃ[ℝ] E) (hf : Function.Bijective f) {C : Set E}
    (hC : MeasurableSet C) (h0 : μ C ≠ 0) (htop : μ C ≠ ∞) (hfC : f ⁻¹' C = C) :
    MeasurePreserving f μ μ := by
  have hmeas : Measurable f := f.continuous_of_finiteDimensional.measurable
  have hlin : Function.Bijective f.linear := by
    rw [show (f.linear : E → E) = fun x ↦ f x - f 0 from f.decomp']
    refine ⟨fun x y h ↦ hf.1 (by simpa using h), fun v ↦ ?_⟩
    obtain ⟨x, hx⟩ := hf.2 (v + f 0)
    exact ⟨x, by simp [hx]⟩
  have hdet : LinearMap.det f.linear ≠ 0 :=
    (LinearEquiv.ofBijective f.linear hlin).isUnit_det'.ne_zero
  set r := ENNReal.ofReal |(LinearMap.det f.linear)⁻¹|
  have hmap : μ.map f = r • μ := by
    have : (f : E → E) = (· + f 0) ∘ f.linear := funext fun x ↦ congrFun f.decomp x
    rw [this, ← Measure.map_map (measurable_add_const _)
      f.linear.continuous_of_finiteDimensional.measurable,
      Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet, Measure.map_smul,
      map_add_right_eq_self μ (f 0)]
    exact (measurable_add_const _).aemeasurable
  have hr : r = 1 := by
    have h := congrArg (· C) hmap
    simp only [Measure.map_apply hmeas hC, hfC, Measure.smul_apply, smul_eq_mul] at h
    exact (ENNReal.mul_eq_right h0 htop).1 h.symm
  exact ⟨hmeas, by rw [hmap, hr, one_smul]⟩

/-- **The uniform law on a centrally symmetric set is `2k`-completely mixable**: `X` and its
reflection `2c − X` through the centre have the same law and add up to `2c`. No convexity is
needed. -/
theorem completelyMixable_of_symmetric {C : Set E} (hC : MeasurableSet C) (h0 : μ C ≠ 0)
    (htop : μ C ≠ ∞) (c : E) (hsymm : ∀ x ∈ C, 2 • c - x ∈ C) {k : ℕ} (hk : 1 ≤ k) :
    CompletelyMixable (k * 2) μ[|C] := by
  have := cond_isProbabilityMeasure_of_finite h0 htop
  let g : E →ᵃ[ℝ] E := AffineEquiv.pointReflection ℝ c
  have hg (x : E) : g x = 2 • c - x := by
    simp only [g, AffineEquiv.coe_coe, AffineEquiv.pointReflection_apply, vsub_eq_sub,
      vadd_eq_add, two_nsmul]
    abel
  have hgC : g ⁻¹' C = C := by
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ by simpa [hg] using hsymm x hx⟩
    simpa [hg] using hsymm _ hx
  have hgμ := (measurePreserving_of_preimage_eq μ g
    (AffineEquiv.pointReflection ℝ c).bijective hC h0 htop hgC).cond hC hgC
  refine CompletelyMixable.mul (CompletelyMixable.of_measurePreserving ![id, g]
    (fun i ↦ ?_) (2 • c) (ae_of_all _ fun x ↦ ?_)) hk
  · fin_cases i
    · exact MeasurePreserving.id _
    · exact hgμ
  · simp [hg]

/-- **The uniform law on a simplex is completely mixable in as many copies as the simplex has
vertices.** For the `n` vertex shifts `b j ↦ b (j + k)`, each preserves the simplex and the
Haar measure, and the images of a point add up to the sum of the vertices. In `ℝᵈ` a simplex has
`d + 1` vertices, so this is the case `n = d + 1` of MF-OP-016 for simplices. -/
theorem completelyMixable_simplex {n : ℕ} [NeZero n] (b : AffineBasis (Fin n) ℝ E) :
    CompletelyMixable n μ[|convexHull ℝ (range b)] := by
  set S := convexHull ℝ (range b)
  have hS : IsCompact S := (finite_range b).isCompact_convexHull (𝕜 := ℝ)
  have hint : (interior S).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.2 b.tot
  have h0 : μ S ≠ 0 :=
    ((isOpen_interior.measure_pos μ hint).trans_le (measure_mono interior_subset)).ne'
  have htop : μ S ≠ ∞ := hS.measure_lt_top.ne
  have := cond_isProbabilityMeasure_of_finite h0 htop
  have hpre (k : Fin n) : simplexShift b k ⁻¹' S = S := by
    ext x
    simp only [mem_preimage, S, b.convexHull_eq_nonneg_coord, mem_ofPred_eq, coord_simplexShift]
    exact ⟨fun h i ↦ by simpa using h (i + k), fun h i ↦ h _⟩
  have hbij (k : Fin n) : Function.Bijective (simplexShift b k) := by
    refine ⟨fun x y h ↦ b.ext_elem fun j ↦ ?_, fun y ↦ ⟨simplexShift b (-k) y, ?_⟩⟩
    · simpa [coord_simplexShift] using congrArg (b.coord (j + k)) h
    · exact b.ext_elem fun j ↦ by simp [coord_simplexShift]
  exact CompletelyMixable.of_measurePreserving (fun k ↦ simplexShift b k) (fun k ↦
    (measurePreserving_of_preimage_eq μ _ (hbij k) hS.isClosed.measurableSet h0 htop
      (hpre k)).cond hS.isClosed.measurableSet (hpre k)) (∑ j, b j)
    (ae_of_all _ (sum_simplexShift b))

end Uniform

section UniformInterval

/-- The representative in `(0, 1]` of a point of the circle `ℝ/ℤ`. -/
private noncomputable def circleVal (z : UnitAddCircle) : ℝ :=
  (AddCircle.equivIoc 1 0 z : Ioc (0 : ℝ) (0 + 1))

private lemma circleVal_mem (z : UnitAddCircle) : circleVal z ∈ Ioc (0 : ℝ) 1 := by
  simpa [circleVal] using (AddCircle.equivIoc 1 0 z).2

private lemma coe_circleVal (z : UnitAddCircle) : ((circleVal z : ℝ) : UnitAddCircle) = z :=
  AddCircle.coe_equivIoc

private lemma circleVal_eq {y : ℝ} {z : UnitAddCircle} (hy : y ∈ Ioc (0 : ℝ) 1)
    (h : (y : UnitAddCircle) = z) : circleVal z = y :=
  (AddCircle.coe_eq_coe_iff_of_mem_Ioc (p := 1) (a := 0) (by simpa using circleVal_mem z)
    (by simpa using hy)).1 ((coe_circleVal z).trans h.symm)

/-- The uniform law on `(0, 1]` maps onto the uniform law on `[a, b]` under `x ↦ (b - a) x + a`. -/
private lemma map_affine_uniform {a b : ℝ} (hab : a < b) :
    (volume.restrict (Ioc (0 : ℝ) 1)).map (fun x ↦ (b - a) * x + a) = volume[|Icc a b] := by
  have hp : 0 < b - a := sub_pos.2 hab
  let e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ (b - a) hp.ne').trans (Homeomorph.addRight a)
  have he : MeasurableEmbedding e := e.measurableEmbedding
  have hmap : volume.map e = ENNReal.ofReal |(b - a)⁻¹| • volume := by
    show volume.map ((· + a) ∘ ((b - a) * ·)) = _
    rw [← Measure.map_map (measurable_add_const a) (measurable_const_mul _),
      Real.map_volume_mul_left hp.ne', Measure.map_smul, map_add_right_eq_self]
  have hpre : e ⁻¹' Icc a b = Icc 0 1 := by
    ext x
    simp only [mem_preimage, mem_Icc, e, Homeomorph.trans_apply, Homeomorph.coe_mulLeft₀,
      Homeomorph.coe_addRight]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by by_contra h; push_neg at h; nlinarith, by by_contra h; push_neg at h; nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith [mul_nonneg hp.le h1], by nlinarith [mul_nonneg hp.le (sub_nonneg.2 h2)]⟩
  show (volume.restrict (Ioc (0 : ℝ) 1)).map e = _
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc, ← hpre, ← he.restrict_map, hmap,
    Measure.restrict_smul, ProbabilityTheory.cond, Real.volume_Icc, abs_of_pos (inv_pos.2 hp),
    ENNReal.ofReal_inv_of_pos hp]

private lemma measurePreserving_circleVal :
    MeasurePreserving circleVal volume (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have := (measurePreserving_subtype_coe (μa := volume) measurableSet_Ioc).comp
    (AddCircle.measurePreserving_equivIoc (T := 1) (a := 0))
  simpa [circleVal, Function.comp_def] using this

/-- **The uniform law on `(0, 1]` is `3`-completely mixable**, through `x`, the fractional part
of `-2x` and the fractional part of `x + 1/2`. Off the null set `{1/2, 1}` the three add up to
`3/2`: for `x < 1/2` they are `x`, `1 - 2x`, `x + 1/2`, and for `x > 1/2` they are `x`,
`2 - 2x`, `x - 1/2`. On the circle `ℝ/ℤ` the three maps are the identity, multiplication by
`-2` and a rotation, each preserving the Haar measure. -/
theorem completelyMixable_three_uniformIoc :
    CompletelyMixable 3 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hmk : MeasurePreserving ((↑) : ℝ → UnitAddCircle) (volume.restrict (Ioc 0 1)) volume := by
    simpa using UnitAddCircle.measurePreserving_mk 0
  have h1 := (measurePreserving_circleVal.comp
    (Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) (n := -2) (by norm_num))).comp hmk
  have h2 := (measurePreserving_circleVal.comp
    (measurePreserving_add_right (volume : Measure UnitAddCircle) ((1 / 2 : ℝ) : UnitAddCircle))).comp
    hmk
  refine CompletelyMixable.of_measurePreserving
    ![fun x ↦ x, fun x ↦ circleVal ((-2 : ℤ) • (x : UnitAddCircle)),
      fun x ↦ circleVal ((x : UnitAddCircle) + ((1 / 2 : ℝ) : UnitAddCircle))]
    (fun i ↦ ?_) (3 / 2) ?_
  · fin_cases i
    · exact MeasurePreserving.id _
    · exact h1
    · exact h2
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [(countable_singleton (1 / 2 : ℝ)).ae_notMem volume,
      (countable_singleton (1 : ℝ)).ae_notMem volume] with x hx2 hx1 hx
    have hx2 : x ≠ 1 / 2 := hx2
    have hx1 : x ≠ 1 := hx1
    have hx1 : x < 1 := lt_of_le_of_ne hx.2 hx1
    have h0 := hx.1
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rcases lt_or_gt_of_ne hx2 with h | h
    · rw [circleVal_eq (y := 1 - 2 * x) ⟨by linarith, by linarith⟩ (by
          rw [show 1 - 2 * x = (-2 : ℤ) • x + 1 by rw [zsmul_eq_mul]; push_cast; ring,
            AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, add_zero]),
        circleVal_eq (y := x + 1 / 2) ⟨by linarith, by linarith⟩ (AddCircle.coe_add _ _)]
      ring
    · rw [circleVal_eq (y := 2 - 2 * x) ⟨by linarith, by linarith⟩ (by
          rw [show 2 - 2 * x = (-2 : ℤ) • x + 1 + 1 by rw [zsmul_eq_mul]; push_cast; ring,
            AddCircle.coe_add, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period,
            add_zero, add_zero]),
        circleVal_eq (y := x - 1 / 2) ⟨by linarith, by linarith⟩ (by
          rw [show x - 1 / 2 = x + 1 / 2 - 1 by ring, AddCircle.coe_sub, AddCircle.coe_period,
            sub_zero, AddCircle.coe_add])]
      ring

/-- **The uniform law on an interval is `n`-completely mixable for every `n ≥ 2`**
(Gaffke–Rüschendorf): `2` by reflection through the midpoint, `3` by
`completelyMixable_three_uniformIoc`, and every `n ≥ 2` is a sum of twos and threes. -/
theorem completelyMixable_uniformIcc {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (volume[|Icc a b]) := by
  have hp : 0 < b - a := sub_pos.2 hab
  have h0 : volume (Icc a b) ≠ 0 := by simpa using hab
  have h2 : CompletelyMixable 2 (volume[|Icc a b]) := by
    simpa using completelyMixable_of_symmetric (volume : Measure ℝ) isClosed_Icc.measurableSet h0
      (by simp) ((a + b) / 2) (k := 1) (fun x hx ↦ by
        simp only [two_nsmul]
        exact ⟨by linarith [hx.2], by linarith [hx.1]⟩) le_rfl
  have h3 : CompletelyMixable 3 (volume[|Icc a b]) := by
    rw [← map_affine_uniform hab]
    exact completelyMixable_three_uniformIoc.map_affine (b - a) a
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | h4
    · exact h2
    · exact h3
    · simpa [Nat.sub_add_cancel hn] using (ih (n - 2) (by omega) (by omega)).add h2

end UniformInterval

/-- **A complete mix is the convex-order minimum of the sum.** If `π` couples `n` copies of an
integrable law `μ` on `ℝ` with an a.s. constant sum, the law of that sum is below, in convex
order, the law of the sum under every other coupling `π'` of `n` copies of `μ`. The constant is
the common mean `n ∫ x dμ`, and Jensen's inequality does the rest. -/
theorem convexOrder_sum_of_completelyMixable {n : ℕ} {μ : Measure ℝ} (hμ : Integrable id μ)
    {π π' : Measure (Fin n → ℝ)} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : ∀ i, π.map (fun x ↦ x i) = μ) (hπ' : ∀ i, π'.map (fun x ↦ x i) = μ) {c : ℝ}
    (hc : ∀ᵐ x ∂π, ∑ i, x i = c) :
    ConvexOrder (π.map fun x ↦ ∑ i, x i) (π'.map fun x ↦ ∑ i, x i) := by
  have hs : Measurable fun x : Fin n → ℝ ↦ ∑ i, x i :=
    Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  have hint (ρ : Measure (Fin n → ℝ)) (hρ : ∀ i, ρ.map (fun x ↦ x i) = μ) (i : Fin n) :
      Integrable (fun x ↦ x i) ρ :=
    (integrable_map_measure aestronglyMeasurable_id (measurable_pi_apply i).aemeasurable).1
      (hρ i ▸ hμ)
  have hmean (ρ : Measure (Fin n → ℝ)) (hρ : ∀ i, ρ.map (fun x ↦ x i) = μ) :
      ∫ x, ∑ i, x i ∂ρ = n * ∫ x, x ∂μ := by
    have h1 (i : Fin n) : ∫ x, x i ∂ρ = ∫ x, x ∂μ := by
      rw [← hρ i]
      exact (integral_map (φ := fun x : Fin n → ℝ ↦ x i) (measurable_pi_apply i).aemeasurable
        aestronglyMeasurable_id).symm
    rw [integral_finsetSum _ fun i _ ↦ hint ρ hρ i]
    simp [h1]
  have hdir : π.map (fun x ↦ ∑ i, x i) = Measure.dirac c := by
    rw [Measure.map_congr hc, Measure.map_const, measure_univ, one_smul]
  have hcmean : c = ∫ y, y ∂(π'.map fun x ↦ ∑ i, x i) := by
    rw [integral_map hs.aemeasurable (f := fun y ↦ y) aestronglyMeasurable_id, hmean π' hπ',
      ← hmean π hπ, integral_congr_ae hc]
    simp
  rw [hdir, hcmean]
  exact ConvexOrder.dirac_integral_le _ <|
    (integrable_map_measure aestronglyMeasurable_id hs.aemeasurable).2
      (by simpa [Function.comp_def] using integrable_finsetSum Finset.univ fun i _ ↦ hint π' hπ' i)

/-- **A completely mixable law has a convex-order-minimal sum**: some coupling of `n` copies of
`μ` has a sum below, in convex order, the sum of every coupling. This is the case of MF-OP-018
where the minimum exists. -/
theorem CompletelyMixable.exists_convexOrder_min {n : ℕ} {μ : Measure ℝ}
    (h : CompletelyMixable n μ) (hμ : Integrable id μ) :
    ∃ π : Measure (Fin n → ℝ), IsProbabilityMeasure π ∧ (∀ i, π.map (fun x ↦ x i) = μ) ∧
      ∀ π' : Measure (Fin n → ℝ), IsProbabilityMeasure π' → (∀ i, π'.map (fun x ↦ x i) = μ) →
        ConvexOrder (π.map fun x ↦ ∑ i, x i) (π'.map fun x ↦ ∑ i, x i) := by
  obtain ⟨π, hπ, hm, c, hc⟩ := h
  exact ⟨π, hπ, hm, fun π' _ hm' ↦ convexOrder_sum_of_completelyMixable hμ hm hm' hc⟩

end MathFin
