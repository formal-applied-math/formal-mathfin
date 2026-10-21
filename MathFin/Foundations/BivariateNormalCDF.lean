/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.NormalQuantile

/-!
# The standard bivariate normal CDF `N₂(a, b; r)`

For independent standard normals `Z₁, Z₂` (the coordinates of `N(0,1) ⊗ N(0,1)`) and
`r ∈ [-1, 1]`, the Cholesky construction

    X = r Z₂ + √(1 − r²) Z₁,   Y = Z₂

gives a standard bivariate normal pair with correlation `r`, and
`N₂(a, b; r) = P(X ≤ a, Y ≤ b)`.

## Main results

* `bivariateNormalCDF`: `N₂(a, b; r)`, and `bivariateNormalLaw r`, the law of `(X, Y)`.
* `stdNormalPair`, `map_linear_stdNormalPair`: `c Z₁ + d Z₂ ∼ N(0, c² + d²)`.
* `map_fst_bivariateNormalLaw`, `map_snd_bivariateNormalLaw`: both margins are `N(0, 1)`.
* `covariance_bivariateNormalLaw`: `Cov(X, Y) = r` (with unit variances, so `Corr(X, Y) = r`).
* `bivariateNormalLaw_map_swap`, `bivariateNormalCDF_comm`: `(Y, X)` has the same law as
  `(X, Y)`, so `N₂(a, b; r) = N₂(b, a; r)`.
* `bivariateNormalCDF_zero`, `bivariateNormalCDF_one`, `bivariateNormalCDF_neg_one`: the
  independent, comonotone and countermonotone cases; `posPart_Phi_sub_Phi`:
  `(Φ(t) − Φ(k))⁺` is the standard normal probability of `(k, t]`.
* `bivariateNormalCDF_flip_snd`: **`N₂(a, b; r) + N₂(a, -b; -r) = Φ(a)`**, the two-asset
  analogue of `Phi_add_Phi_neg` — the key algebraic ingredient behind exact two-asset closed
  forms (Stulz 1982, Heynen & Kat 1994/96) that package `N₂(·,·;ρ)` / `N₂(·,·;-ρ)` pairs.
* `bivariateNormalCDF_neg_neg`: **`N₂(-a, -b; r) = 1 - Φ(a) - Φ(b) + N₂(a, b; r)`**, the joint
  survival identity, derived purely algebraically from `bivariateNormalCDF_flip_snd` and
  `bivariateNormalCDF_comm` (no new measure-theoretic argument).

Outside `r ∈ [-1, 1]` the square root truncates to `0` and the construction is no longer the
standard bivariate normal with correlation `r` (it degenerates to the law of `(rY, Y)`); every
result that needs it carries the hypothesis `r ^ 2 ≤ 1`.

Neighbouring notions: Mathlib's `ProbabilityTheory.multivariateGaussian` (on
`EuclideanSpace ℝ (Fin 2)`) and the hypothesis bundle `BivariateGaussianHyp`
(`Foundations/BivariateGaussian.lean`). The bridges from `bivariateNormalLaw` to them are not
stated here.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set

/-- The law of two independent standard normals, `N(0,1) ⊗ N(0,1)`. -/
noncomputable abbrev stdNormalPair : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

/-- The Cholesky map `(z₁, z₂) ↦ (r z₂ + √(1 − r²) z₁, z₂)`. -/
noncomputable def choleskyPair (r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (r * p.2 + √(1 - r ^ 2) * p.1, p.2)

@[fun_prop]
lemma measurable_choleskyPair (r : ℝ) : Measurable (choleskyPair r) := by
  unfold choleskyPair; fun_prop

/-- The standard bivariate normal law with correlation `r`: the law of the Cholesky pair. -/
noncomputable def bivariateNormalLaw (r : ℝ) : Measure (ℝ × ℝ) :=
  stdNormalPair.map (choleskyPair r)

instance (r : ℝ) : IsProbabilityMeasure (bivariateNormalLaw r) :=
  Measure.isProbabilityMeasure_map (measurable_choleskyPair r).aemeasurable

/-- **The standard bivariate normal CDF** `N₂(a, b; r) = P(X ≤ a, Y ≤ b)` for the Cholesky pair
`X = r Z₂ + √(1 − r²) Z₁`, `Y = Z₂`. -/
noncomputable def bivariateNormalCDF (a b r : ℝ) : ℝ :=
  stdNormalPair.real {p : ℝ × ℝ | r * p.2 + √(1 - r ^ 2) * p.1 ≤ a ∧ p.2 ≤ b}

/-- `N₂(a, b; r)` is the `bivariateNormalLaw r`-measure of the quadrant `(-∞, a] × (-∞, b]`. -/
lemma bivariateNormalCDF_eq_law (a b r : ℝ) :
    bivariateNormalCDF a b r = (bivariateNormalLaw r).real (Iic a ×ˢ Iic b) := by
  rw [bivariateNormalLaw, map_measureReal_apply (measurable_choleskyPair r)
    (measurableSet_Iic.prod measurableSet_Iic)]
  rfl

/-- A linear combination of independent standard normals: `c Z₁ + d Z₂ ∼ N(0, c² + d²)`. -/
lemma map_linear_stdNormalPair (c d : ℝ) :
    stdNormalPair.map (fun p ↦ c * p.1 + d * p.2) =
      gaussianReal 0 (c ^ 2 + d ^ 2).toNNReal := by
  have hf : (fun p : ℝ × ℝ ↦ c * p.1 + d * p.2) =
      (fun q : ℝ × ℝ ↦ q.1 + q.2) ∘ Prod.map (c * ·) (d * ·) := rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_prod_map _ _
    (by fun_prop) (by fun_prop), gaussianReal_map_const_mul, gaussianReal_map_const_mul]
  change gaussianReal _ _ ∗ gaussianReal _ _ = _
  rw [gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · ext; rw [Real.coe_toNNReal _ (by positivity)]; simp

/-- A linear functional of the bivariate normal pair: `c X + d Y ∼ N(0, c² + 2cdr + d²)`. -/
lemma map_linear_bivariateNormalLaw {r : ℝ} (hr : r ^ 2 ≤ 1) (c d : ℝ) :
    (bivariateNormalLaw r).map (fun q ↦ c * q.1 + d * q.2) =
      gaussianReal 0 (c ^ 2 + 2 * c * d * r + d ^ 2).toNNReal := by
  have hs : √(1 - r ^ 2) ^ 2 = 1 - r ^ 2 := sq_sqrt (by linarith)
  rw [bivariateNormalLaw, Measure.map_map (by fun_prop) (measurable_choleskyPair r)]
  have hf : (fun q : ℝ × ℝ ↦ c * q.1 + d * q.2) ∘ choleskyPair r =
      fun p ↦ (c * √(1 - r ^ 2)) * p.1 + (c * r + d) * p.2 := by
    ext p; simp only [Function.comp, choleskyPair]; ring
  rw [hf, map_linear_stdNormalPair]
  congr 2
  rw [mul_pow, hs]; ring

/-- The first margin `X ∼ N(0, 1)` (needs `r ^ 2 ≤ 1`: for `|r| > 1` the junk-valued root
makes `X = r Y`, which is not `N(0, 1)`). -/
lemma map_fst_bivariateNormalLaw {r : ℝ} (hr : r ^ 2 ≤ 1) :
    (bivariateNormalLaw r).map Prod.fst = gaussianReal 0 1 := by
  have e : (Prod.fst : ℝ × ℝ → ℝ) = fun q ↦ 1 * q.1 + 0 * q.2 := by ext; simp
  rw [e, map_linear_bivariateNormalLaw hr]
  congr 1
  simp

/-- The second margin `Y = Z₂ ∼ N(0, 1)`, for every `r` (unconditional: `Y` never involves
the possibly-junk-valued root). -/
lemma map_snd_bivariateNormalLaw (r : ℝ) :
    (bivariateNormalLaw r).map Prod.snd = gaussianReal 0 1 := by
  rw [bivariateNormalLaw, Measure.map_map measurable_snd (measurable_choleskyPair r)]
  exact Measure.map_snd_prod.trans (by simp)

/-- `Var[c X + d Y] = c ^ 2 + 2 c d r + d ^ 2`, read off `map_linear_bivariateNormalLaw`'s
pushforward. -/
lemma variance_linear_bivariateNormalLaw {r : ℝ} (hr : r ^ 2 ≤ 1) (c d : ℝ) :
    Var[fun q ↦ c * q.1 + d * q.2; bivariateNormalLaw r] = c ^ 2 + 2 * c * d * r + d ^ 2 := by
  rw [← variance_id_map (by fun_prop), map_linear_bivariateNormalLaw hr, variance_id_gaussianReal,
    Real.coe_toNNReal _ (by nlinarith [sq_nonneg (c * r + d)])]

/-- `c X + d Y ∈ L²(bivariateNormalLaw r)`, transported from the Gaussian `L²`-membership
along `map_linear_bivariateNormalLaw`. -/
lemma memLp_linear_bivariateNormalLaw {r : ℝ} (hr : r ^ 2 ≤ 1) (c d : ℝ) :
    MemLp (fun q : ℝ × ℝ ↦ c * q.1 + d * q.2) 2 (bivariateNormalLaw r) := by
  have h := memLp_id_gaussianReal (μ := 0)
    (v := (c ^ 2 + 2 * c * d * r + d ^ 2).toNNReal) 2
  rw [← map_linear_bivariateNormalLaw hr] at h
  exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).1 h

/-- **The correlation is the parameter `r`**: `Cov(X, Y) = r`, and `Var X = Var Y = 1`. -/
theorem covariance_bivariateNormalLaw {r : ℝ} (hr : r ^ 2 ≤ 1) :
    cov[Prod.fst, Prod.snd; bivariateNormalLaw r] = r ∧
      Var[Prod.fst; bivariateNormalLaw r] = 1 ∧ Var[Prod.snd; bivariateNormalLaw r] = 1 := by
  have e1 : (Prod.fst : ℝ × ℝ → ℝ) = fun q ↦ 1 * q.1 + 0 * q.2 := by ext; simp
  have e2 : (Prod.snd : ℝ × ℝ → ℝ) = fun q ↦ 0 * q.1 + 1 * q.2 := by ext; simp
  have e3 : (Prod.fst + Prod.snd : ℝ × ℝ → ℝ) = fun q ↦ 1 * q.1 + 1 * q.2 := by ext; simp
  have v1 : Var[Prod.fst; bivariateNormalLaw r] = 1 := by
    rw [e1, variance_linear_bivariateNormalLaw hr]; ring
  have v2 : Var[Prod.snd; bivariateNormalLaw r] = 1 := by
    rw [e2, variance_linear_bivariateNormalLaw hr]; ring
  have m1 : MemLp Prod.fst 2 (bivariateNormalLaw r) := by
    rw [e1]; exact memLp_linear_bivariateNormalLaw hr 1 0
  have m2 : MemLp Prod.snd 2 (bivariateNormalLaw r) := by
    rw [e2]; exact memLp_linear_bivariateNormalLaw hr 0 1
  have hadd := variance_add m1 m2
  rw [e3, variance_linear_bivariateNormalLaw hr, v1, v2] at hadd
  exact ⟨by linarith, v1, v2⟩

/-- **Exchangeability**: for `r ∈ [-1, 1]`, `(Y, X)` has the same law as `(X, Y)`. -/
theorem bivariateNormalLaw_map_swap {r : ℝ} (hr : r ^ 2 ≤ 1) :
    (bivariateNormalLaw r).map Prod.swap = bivariateNormalLaw r := by
  refine Measure.ext_of_charFunDual (funext fun L ↦ ?_)
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
    Measure.map_map L.continuous.measurable measurable_swap]
  have hL (q : ℝ × ℝ) : L q = L (1, 0) * q.1 + L (0, 1) * q.2 := by
    have : q = q.1 • ((1 : ℝ), (0 : ℝ)) + q.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [this]
    simp only [map_add, map_smul, smul_eq_mul]; ring
  have h1 : (L : ℝ × ℝ → ℝ) = fun q ↦ L (1, 0) * q.1 + L (0, 1) * q.2 := funext hL
  have h2 : (L : ℝ × ℝ → ℝ) ∘ Prod.swap = fun q ↦ L (0, 1) * q.1 + L (1, 0) * q.2 := by
    ext q; rw [Function.comp_apply, hL (Prod.swap q)]; simp only [Prod.fst_swap, Prod.snd_swap]
    ring
  rw [h2, h1, map_linear_bivariateNormalLaw hr, map_linear_bivariateNormalLaw hr]
  congr 3
  ring

/-- **Symmetry**: `N₂(a, b; r) = N₂(b, a; r)` for `r ∈ [-1, 1]`. -/
theorem bivariateNormalCDF_comm (a b : ℝ) {r : ℝ} (hr : r ^ 2 ≤ 1) :
    bivariateNormalCDF a b r = bivariateNormalCDF b a r := by
  rw [bivariateNormalCDF_eq_law, bivariateNormalCDF_eq_law]
  conv_lhs => rw [← bivariateNormalLaw_map_swap hr]
  rw [map_measureReal_apply measurable_swap (measurableSet_Iic.prod measurableSet_Iic),
    preimage_swap_prod]

/-- `N₂(a, b; r)` in terms of `Y = Z₂` alone, when the `Z₁` coefficient vanishes. -/
private lemma bivariateNormalCDF_of_sqrt_eq_zero {a b r : ℝ} (h : √(1 - r ^ 2) = 0) :
    bivariateNormalCDF a b r = (gaussianReal 0 1).real {y | r * y ≤ a ∧ y ≤ b} := by
  have hset : {p : ℝ × ℝ | r * p.2 + √(1 - r ^ 2) * p.1 ≤ a ∧ p.2 ≤ b} =
      Prod.snd ⁻¹' {y | r * y ≤ a ∧ y ≤ b} := by ext p; simp [h]
  have hm : MeasurableSet {y : ℝ | r * y ≤ a ∧ y ≤ b} :=
    (measurableSet_le (measurable_id.const_mul r) measurable_const).inter
      (measurableSet_le measurable_id measurable_const)
  rw [bivariateNormalCDF, hset, ← map_measureReal_apply measurable_snd hm, Measure.map_snd_prod]
  simp

/-- **Independence** (`r = 0`): `N₂(a, b; 0) = Φ(a) Φ(b)`. -/
theorem bivariateNormalCDF_zero (a b : ℝ) : bivariateNormalCDF a b 0 = Phi a * Phi b := by
  have hset : {p : ℝ × ℝ | 0 * p.2 + √(1 - 0 ^ 2) * p.1 ≤ a ∧ p.2 ≤ b} = Iic a ×ˢ Iic b := by
    ext p; simp only [mem_ofPred_eq, mem_prod, mem_Iic]; norm_num
  rw [bivariateNormalCDF, hset, measureReal_prod_prod]
  rfl

/-- **Comonotone** (`r = 1`): `N₂(a, b; 1) = Φ(min a b)`. -/
theorem bivariateNormalCDF_one (a b : ℝ) : bivariateNormalCDF a b 1 = Phi (min a b) := by
  rw [bivariateNormalCDF_of_sqrt_eq_zero (by simp)]
  congr 1
  ext y; simp

/-- `(Φ(t) − Φ(k))⁺` is the standard normal probability of `(k, t]`. -/
lemma posPart_Phi_sub_Phi (k t : ℝ) :
    (Phi t - Phi k)⁺ = (gaussianReal 0 1).real (Ioc k t) := by
  rcases le_total t k with h | h
  · rw [Ioc_eq_empty (not_lt.2 h), measureReal_empty, posPart_eq_zero]
    exact sub_nonpos.2 (strictMono_Phi.monotone h)
  · rw [posPart_eq_self.2 (sub_nonneg.2 (strictMono_Phi.monotone h)), ← Iic_sdiff_Iic,
      measureReal_sdiff (Iic_subset_Iic.2 h) measurableSet_Iic, ← cdf_eq_real, ← cdf_eq_real,
      cdf_gaussianReal_zero_one]

/-- **Countermonotone** (`r = -1`): `N₂(a, b; -1) = (Φ(b) − Φ(−a))⁺`. -/
theorem bivariateNormalCDF_neg_one (a b : ℝ) :
    bivariateNormalCDF a b (-1) = (Phi b - Phi (-a))⁺ := by
  rw [bivariateNormalCDF_of_sqrt_eq_zero (by simp), posPart_Phi_sub_Phi]
  have hset : {y : ℝ | -1 * y ≤ a ∧ y ≤ b} = Icc (-a) b := by
    ext y; simp only [mem_ofPred_eq, mem_Icc]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      linarith
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  rw [hset, measureReal_congr Ioc_ae_eq_Icc.symm]

/-! ## A sign-flip identity: `N₂(a, b; r) + N₂(a, -b; -r) = Φ(a)`

Negating the second coordinate of the Cholesky pair sends correlation `r` to `-r` without
touching the `X`-margin, so splitting the real line into the closed rays `Iic b` and `Ici b`
(covering `ℝ`, meeting only at the null set `{b}` for the atom-free `Y`-margin) gives the
identity below. It is the two-asset analogue of `Phi_add_Phi_neg`. -/

/-- The sign-flip map `(x, y) ↦ (x, -y)` sends `bivariateNormalLaw r` to `bivariateNormalLaw
(-r)`: negating `Y` negates the correlation, unconditionally in `r`. -/
lemma bivariateNormalLaw_map_negSnd (r : ℝ) :
    (bivariateNormalLaw r).map (fun p : ℝ × ℝ ↦ (p.1, -p.2)) = bivariateNormalLaw (-r) := by
  have hnegStd : stdNormalPair.map (fun p : ℝ × ℝ ↦ (p.1, -p.2)) = stdNormalPair := by
    have hf : (fun p : ℝ × ℝ ↦ (p.1, -p.2)) = Prod.map id (fun x : ℝ ↦ -x) := rfl
    have hneg : (gaussianReal (0 : ℝ) (1 : NNReal)).map ((-1 : ℝ) * ·) = gaussianReal 0 1 := by
      have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : NNReal)) (-1)
      simpa using h
    have hneg' : (gaussianReal (0 : ℝ) (1 : NNReal)).map (fun x : ℝ ↦ -x) = gaussianReal 0 1 := by
      simpa [neg_one_mul] using hneg
    rw [hf, stdNormalPair, ← Measure.map_prod_map _ _ measurable_id (by fun_prop),
      Measure.map_id, hneg']
  have hcomm : (fun p : ℝ × ℝ ↦ (p.1, -p.2)) ∘ choleskyPair r =
      choleskyPair (-r) ∘ (fun p : ℝ × ℝ ↦ (p.1, -p.2)) := by
    funext p
    simp only [Function.comp, choleskyPair, neg_sq, Prod.mk.injEq]
    constructor <;> first | ring | trivial
  rw [bivariateNormalLaw, bivariateNormalLaw,
    Measure.map_map (by fun_prop) (measurable_choleskyPair r), hcomm,
    ← Measure.map_map (measurable_choleskyPair (-r)) (by fun_prop), hnegStd]

/-- **The sign-flip identity**: `N₂(a, b; r) + N₂(a, -b; -r) = Φ(a)`. Splits `(bivariateNormalLaw
r).real (Iic a ×ˢ ·)` across the closed-ray cover `Iic b ∪ Ici b = univ` (meeting at the null
set `{b}`, since the `Y`-margin `map_snd_bivariateNormalLaw` is atom-free), then reads off the
`X`-margin via `map_fst_bivariateNormalLaw`. -/
theorem bivariateNormalCDF_flip_snd (a b : ℝ) {r : ℝ} (hr : r ^ 2 ≤ 1) :
    bivariateNormalCDF a b r + bivariateNormalCDF a (-b) (-r) = Phi a := by
  have hflip : bivariateNormalCDF a (-b) (-r) = (bivariateNormalLaw r).real (Iic a ×ˢ Ici b) := by
    rw [bivariateNormalCDF_eq_law, ← bivariateNormalLaw_map_negSnd r,
      map_measureReal_apply (by fun_prop) (measurableSet_Iic.prod measurableSet_Iic)]
    congr 1
    ext p
    simp only [mem_preimage, mem_prod, mem_Iic, mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  have hsingleton : (bivariateNormalLaw r).real (Iic a ×ˢ ({b} : Set ℝ)) = 0 := by
    have hsub : (Iic a ×ˢ ({b} : Set ℝ) : Set (ℝ × ℝ)) ⊆ univ ×ˢ ({b} : Set ℝ) :=
      prod_mono (subset_univ _) subset_rfl
    have hzero : (bivariateNormalLaw r).real (univ ×ˢ ({b} : Set ℝ)) = 0 := by
      have : NullSingletonClass (gaussianReal (0 : ℝ) (1 : NNReal)) :=
        nullSingletonClass_gaussianReal one_ne_zero
      rw [show (univ ×ˢ ({b} : Set ℝ) : Set (ℝ × ℝ)) = Prod.snd ⁻¹' {b} by ext p; simp,
        ← map_measureReal_apply measurable_snd (measurableSet_singleton b),
        map_snd_bivariateNormalLaw]
      simp [measureReal_def]
    exact le_antisymm (hzero ▸ measureReal_mono hsub) measureReal_nonneg
  have hunion : (Iic a ×ˢ Iic b : Set (ℝ × ℝ)) ∪ (Iic a ×ˢ Ici b) = Iic a ×ˢ univ := by
    rw [← prod_union]; congr 1; ext x; simp
  have hinter : (Iic a ×ˢ Iic b : Set (ℝ × ℝ)) ∩ (Iic a ×ˢ Ici b) = Iic a ×ˢ {b} := by
    rw [← prod_inter]; congr 1; ext x; simp [le_antisymm_iff]
  have hkey := measureReal_union_add_inter (μ := bivariateNormalLaw r)
    (s := Iic a ×ˢ Iic b) (t := Iic a ×ˢ Ici b) (measurableSet_Iic.prod measurableSet_Ici)
  rw [hunion, hinter, hsingleton, add_zero] at hkey
  have hmargin : (bivariateNormalLaw r).real (Iic a ×ˢ (univ : Set ℝ)) = Phi a := by
    rw [show (Iic a ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) = Prod.fst ⁻¹' Iic a by ext p; simp,
      ← map_measureReal_apply measurable_fst measurableSet_Iic,
      map_fst_bivariateNormalLaw hr]
    simp [measureReal_def, Phi_def]
  rw [bivariateNormalCDF_eq_law, hflip, ← hkey, hmargin]

/-- **Joint survival identity**: `N₂(-a, -b; r) = 1 - Φ(a) - Φ(b) + N₂(a, b; r)`, derived purely
algebraically from the sign-flip identity `bivariateNormalCDF_flip_snd` and the symmetry
`bivariateNormalCDF_comm` — no new measure-theoretic content. This is the identity that
collapses the strike-side terms of Stulz-style two-asset closed forms. -/
theorem bivariateNormalCDF_neg_neg (a b : ℝ) {r : ℝ} (hr : r ^ 2 ≤ 1) :
    bivariateNormalCDF (-a) (-b) r = 1 - Phi a - Phi b + bivariateNormalCDF a b r := by
  have hr' : (-r) ^ 2 ≤ 1 := by rwa [neg_sq]
  have h1 := bivariateNormalCDF_flip_snd a b hr
  have h2 := bivariateNormalCDF_flip_snd (-b) a hr'
  rw [neg_neg, Phi_neg, bivariateNormalCDF_comm (-b) a hr',
    bivariateNormalCDF_comm (-b) (-a) hr] at h2
  linarith

end MathFin
