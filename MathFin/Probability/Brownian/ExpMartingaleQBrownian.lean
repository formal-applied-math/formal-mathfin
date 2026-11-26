/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Dependence.IndepPast
public import MathFin.Probability.Laws.Esscher
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess
public import Mathlib.Probability.Process.Adapted

/-!
# Brownian increment laws from an exponential martingale

A process-agnostic packaging of the argument that turns an **exponential-martingale
hypothesis** into the increment laws of a Brownian motion under a probability measure `Q`. Fix a
probability space `(Ω, Q)`, a filtration `𝓕`, a horizon `T`, and a real process
`Y : ℝ≥0 → Ω → ℝ` that is `𝓕`-adapted, starts at `0` (a.e. `Q`), and satisfies

  `for every a : ℝ, the process t ↦ exp(a·Y_t − ½a² t) is a Q-martingale on [0,T]`.

These three data are bundled as `IsExpQMartingale Q 𝓕 Y T`. The single theorem
`isBrownianOn_of_expMartingale` restates the zero start and derives two more properties of `Y`
under `Q` on `[0,T]`: `N(0,t−s)` increments, and independent increments in Mathlib's sense
(`HasIndepIncrements`). Together they fix every finite-dimensional law of `Y` on `[0,T]` to that
of a Brownian motion; that implication is not restated here (on the whole time axis `ℝ≥0` it is
Mathlib's `HasIndepIncrements.isPreBrownianReal_of_hasLaw`). Path continuity is not part of the
conclusion. The independence of each increment `Y_t − Y_s` from `𝓕_s`
(`indep_increment_of_expMartingale`) is proved here and is what gives independent increments.
Nothing in the argument refers to how `Y` or `Q` was constructed.

The mechanism: the exponential martingale at `s = 0` fixes the marginal moment-generating
function `𝔼_Q[exp(a·Y_t)] = exp(½a²t)`, hence the marginal law, and the conditional form
`𝔼_Q[exp(a·(Y_t − Y_s))|𝓕_s] = exp(½a²(t−s))` is deterministic. That gives Gaussian increments,
and integrated over `A ∈ 𝓕_s` it says that the law of `Y_t − Y_s` under `Q` restricted to `A` has
the moment-generating function of `Q(A)·N(0,t−s)`, hence is that measure
(`measure_eq_of_mgf_id_eq`): the increment is independent of `𝓕_s`. Adaptedness and independence
of the past give independent increments (`hasIndepIncrements_of_indep_past`, in
`Dependence/IndepPast.lean`).

The value of the abstraction is coherence: the constant-, simple-, continuous- and
predictable-`θ` Girsanov drift-corrected processes each need only supply their own
exponential martingale (via the Bayes change-of-measure engine) and then instantiate this
one theorem.

## Main definitions

* `IsExpQMartingale`: the characterization data on a process `Y` under `Q`: adapted, starting at
  `0` almost surely, and for every `a : ℝ` the set-integral martingale identity for
  `exp(a·Y_t − ½a²t)` on `[0, T]` (integrability is not a field).
* `IsBrownianOn`: under `Q`, `Y` starts at `0` almost surely, has `N(0, t − s)` increments and
  independent increments (`HasIndepIncrements`) on `[0, T]`; these fix the finite-dimensional
  laws of a Brownian motion, but path continuity is not part of it.

## Main results

* `MathFin.map_eq_gaussianReal_of_expMartingale` — the marginal law `Q.map Y_t = N(0,t)`.
* `MathFin.increment_map_eq_gaussianReal_of_expMartingale` — the increment law `N(0,t−s)`.
* `MathFin.indep_increment_of_expMartingale` — `Y_t − Y_s` is `Q`-independent of `𝓕_s`.
* `MathFin.hasIndepIncrements_of_expMartingale` — `Y` has independent increments on `[0,T]`.
* `MathFin.IsExpQMartingale.isGaussianProcess` — `Y` is a Gaussian process on `[0,T]`.
* `MathFin.isBrownianOn_of_expMartingale` — `IsExpQMartingale Q 𝓕 Y T → IsBrownianOn Q T Y`.
* `MathFin.IsBrownianOn.congr_modification` — invariance under a modification.

## Tags

Girsanov theorem, Lévy characterization, exponential martingale, Brownian increments,
moment generating function, Q-Brownian motion, MSC 60J65, MSC 60G44
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The exponential-martingale characterization data.** A real process `Y` on the filtered
probability space `(Ω, 𝓕, Q)` that is `𝓕`-adapted, starts at `0` a.e. `Q`, and for which every
`t ↦ exp(a·Y_t − ½a² t)` is a `Q`-martingale on `[0,T]` (stated as the set-integral identity over
`𝓕_s`-sets). These are exactly the data output by the Bayes change-of-measure engine for a
drift-corrected process, and exactly the data consumed by `isBrownianOn_of_expMartingale`. -/
structure IsExpQMartingale (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    Prop where
  /-- `Y` is adapted to the filtration. -/
  adapted : StronglyAdapted 𝓕 Y
  /-- `Y` starts at `0` (a.e. `Q`). -/
  zero_start : Y 0 =ᵐ[Q] 0
  /-- For every `a`, `exp(a·Y_· − ½a²·)` is a `Q`-martingale on `[0,T]`. -/
  martingale : ∀ (a : ℝ) {s t : ℝ≥0}, s ≤ t → t ≤ T → ∀ {A : Set Ω},
    MeasurableSet[(𝓕 s : MeasurableSpace Ω)] A →
      ∫ ω in A, Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) ∂Q
        = ∫ ω in A, Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2) ∂Q

/-- Each `Y_u` of the characterization data is measurable, being `𝓕_u`-measurable. -/
protected theorem IsExpQMartingale.measurable {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {Y : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} (h : IsExpQMartingale Q 𝓕 Y T) (u : ℝ≥0) : Measurable (Y u) :=
  h.adapted.stronglyMeasurable.measurable

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ}
  {Y : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- **A Gaussian MGF identifies the Gaussian law.** If a real random variable has the
moment-generating function `a ↦ exp(v·a²/2)` of `N(0,v)` under `Q`, its law is `N(0,v)`:
`N(0,v)` has every exponential moment, so its moment-generating function determines it
(`measure_eq_of_mgf_id_eq`). -/
theorem map_eq_gaussianReal_of_mgf {X : Ω → ℝ} (hX : AEMeasurable X Q) {v : ℝ≥0}
    (hmgf : ∀ a, mgf X Q a = Real.exp (v * a ^ 2 / 2)) : Q.map X = gaussianReal 0 v := by
  refine Eq.symm (measure_eq_of_mgf_id_eq integrable_exp_mul_gaussianReal ?_)
  rw [mgf_id_gaussianReal, mgf_id_map hX]
  funext a
  rw [hmgf, zero_mul, zero_add]

/-- **Marginal `Q`-MGF.** `𝔼_Q[exp(a·Y_t)] = exp(½ t a²)`: read off from the exponential
martingale at `s = 0` (the `Q`-integral of `exp(a·Y_t − ½a²t)` equals its value at `0`, which is
`exp(a·Y_0) = 1` a.e. since `Y_0 = 0`). -/
private theorem mgf_expY_eq (h : IsExpQMartingale Q 𝓕 Y T) {t : ℝ≥0} (htT : t ≤ T) (a : ℝ) :
    ∫ ω, Real.exp (a * Y t ω) ∂Q = Real.exp ((t : ℝ) * a ^ 2 / 2) := by
  have hbrick := h.martingale a (zero_le : (0 : ℝ≥0) ≤ t) htT (A := Set.univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at hbrick
  have hRHS : ∫ ω, Real.exp (a * Y 0 ω - a ^ 2 * ((0 : ℝ≥0) : ℝ) / 2) ∂Q = 1 := by
    have hae : (fun ω ↦ Real.exp (a * Y 0 ω - a ^ 2 * ((0 : ℝ≥0) : ℝ) / 2))
        =ᵐ[Q] fun _ ↦ (1 : ℝ) := by
      filter_upwards [h.zero_start] with ω hω; simp [hω]
    rw [integral_congr_ae hae]; simp
  rw [hRHS] at hbrick
  have hLHS : ∫ ω, Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) ∂Q
      = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * ∫ ω, Real.exp (a * Y t ω) ∂Q := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦
      (congrArg Real.exp (sub_eq_neg_add (a * Y t ω) (a ^ 2 * (t : ℝ) / 2))).trans
        (Real.exp_add _ _))
  rw [hLHS, mul_comm] at hbrick
  have hfac : Real.exp (-(a ^ 2 * (t : ℝ) / 2)) ≠ 0 := (Real.exp_pos _).ne'
  rw [(mul_eq_one_iff_eq_inv₀ hfac).mp hbrick, ← Real.exp_neg]
  congr 1; ring

/-- **Marginal law.** `Q.map Y_t = N(0, t)`: the `Q`-MGF is the Gaussian MGF (`mgf_expY_eq`),
which identifies the law (`map_eq_gaussianReal_of_mgf`). -/
theorem map_eq_gaussianReal_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {t : ℝ≥0}
    (htT : t ≤ T) : Q.map (Y t) = gaussianReal 0 t :=
  map_eq_gaussianReal_of_mgf (h.measurable t).aemeasurable (mgf_expY_eq h htT)

/-- **Marginal `Q`-integrability.** `exp(a·Y_u)` is `Q`-integrable for `u ≤ T` — its law is
`N(0,u)` and the Gaussian MGF is finite. -/
private theorem integrable_expY (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {u : ℝ≥0} (huT : u ≤ T) :
    Integrable (fun ω ↦ Real.exp (a * Y u ω)) Q :=
  (⟨(h.measurable u).aemeasurable, map_eq_gaussianReal_of_expMartingale h huT⟩ :
    HasLaw (Y u) (gaussianReal 0 u) Q).integrable_fun_comp (integrable_exp_mul_gaussianReal a)

/-- **Integrability of the exponential martingale's terms.** `exp(a·Y_u − ½a²u)` is
`Q`-integrable for `u ≤ T`. -/
private theorem integrable_expY_sub (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {u : ℝ≥0}
    (huT : u ≤ T) : Integrable (fun ω ↦ Real.exp (a * Y u ω - a ^ 2 * (u : ℝ) / 2)) Q :=
  ((integrable_expY h a huT).const_mul (Real.exp (-(a ^ 2 * (u : ℝ) / 2)))).congr
    (Filter.Eventually.of_forall fun ω ↦
      ((congrArg Real.exp (sub_eq_neg_add (a * Y u ω) (a ^ 2 * (u : ℝ) / 2))).trans
        (Real.exp_add _ _)).symm)

omit [IsProbabilityMeasure Q] in
/-- **Cauchy–Schwarz for exponentials.** If `exp(2f)` and `exp(2g)` are `Q`-integrable, so is
`exp(f)·exp(g)`: `exp f` and `exp g` are then in `L²(Q)`. -/
theorem integrable_exp_mul_exp {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun ω ↦ Real.exp (2 * f ω)) Q)
    (hg2 : Integrable (fun ω ↦ Real.exp (2 * g ω)) Q) :
    Integrable (fun ω ↦ Real.exp (f ω) * Real.exp (g ω)) Q := by
  have hL2 {u : Ω → ℝ} (hu : Measurable u) (hu2 : Integrable (fun ω ↦ Real.exp (2 * u ω)) Q) :
      MemLp (fun ω ↦ Real.exp (u ω)) 2 Q := by
    refine (memLp_two_iff_integrable_sq hu.exp.aestronglyMeasurable).2 (hu2.congr ?_)
    filter_upwards with ω
    rw [two_mul, Real.exp_add, pow_two]
  exact (hL2 hf hf2).integrable_mul (hL2 hg hg2)

/-- **Conditional exponential martingale.** `𝔼_Q[exp(a·Y_t − ½a² t)|𝓕_s] = exp(a·Y_s − ½a² s)`
a.e., the conditional form of the `martingale` field (its set-integral identity converted via
`ae_eq_condExp_of_forall_setIntegral_eq`). -/
private theorem condExp_expY (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t)
    (htT : t ≤ T) :
    Q[fun ω ↦ Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) | 𝓕 s]
      =ᵐ[Q] fun ω ↦ Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2) := by
  have hsm : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)]
      (fun ω ↦ Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2)) := by
    have hcont : Continuous fun x : ℝ ↦ a * x - a ^ 2 * (s : ℝ) / 2 := by fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable (hcont.comp_stronglyMeasurable (h.adapted s))
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (integrable_expY_sub h a htT)
    (fun A _ _ ↦ (integrable_expY_sub h a (hst.trans htT)).integrableOn) (fun A hA _ ↦ ?_)
    hsm.aestronglyMeasurable).symm
  exact (h.martingale a hst htT hA).symm

/-- **Conditional moment-generating function of an increment.**
`𝔼_Q[exp(a·(Y_t − Y_s)) | 𝓕_s] = exp(½a²(t−s))` a.e., deterministic: pull the `𝓕_s`-measurable
factor `exp(½a²t − a·Y_s)` out of `condExp_expY`. -/
theorem IsExpQMartingale.condExp_exp_increment (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Q[fun ω ↦ Real.exp (a * (Y t ω - Y s ω)) | 𝓕 s]
      =ᵐ[Q] fun _ ↦ Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
  set ft : Ω → ℝ := fun ω ↦ Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) with hftdef
  set gs : Ω → ℝ := fun ω ↦ Real.exp (a ^ 2 * (t : ℝ) / 2 - a * Y s ω) with hgsdef
  have hgs_sm : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)] gs := by
    have hcont : Continuous fun x : ℝ ↦ a ^ 2 * (t : ℝ) / 2 - a * x := by fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable (hcont.comp_stronglyMeasurable (h.adapted s))
  have hft_int : Integrable ft Q := integrable_expY_sub h a htT
  have hprod : (fun ω ↦ gs ω * ft ω) = fun ω ↦ Real.exp (a * (Y t ω - Y s ω)) := by
    funext ω; rw [hgsdef, hftdef, ← Real.exp_add]; congr 1; ring
  have hprod_int : Integrable (fun ω ↦ gs ω * ft ω) Q := by
    rw [hprod]
    refine (integrable_exp_mul_exp ((h.measurable t).const_mul a) ((h.measurable s).const_mul (-a))
      (by simpa only [mul_assoc] using integrable_expY h (2 * a) htT)
      (by simpa only [mul_assoc] using integrable_expY h (2 * -a) (hst.trans htT))).congr ?_
    filter_upwards with ω
    rw [← Real.exp_add]
    congr 1
    ring
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := (𝓕 s : MeasurableSpace Ω))
    hgs_sm hprod_int hft_int
  have hcond := condExp_expY h a hst htT
  have hint_eq : (fun ω ↦ Real.exp (a * (Y t ω - Y s ω))) = gs * ft := hprod.symm
  rw [hint_eq]
  filter_upwards [hpull, hcond] with ω hp hc
  rw [hp, Pi.mul_apply,
    show (Q[ft | 𝓕 s]) ω = Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2) from hc,
    hgsdef, ← Real.exp_add]
  congr 1; ring

/-- **Unconditional `Q`-MGF of the increment.** `𝔼_Q[exp(a·(Y_t − Y_s))] = exp(½a²(t−s))` — the
tower property on the deterministic conditional MGF `IsExpQMartingale.condExp_exp_increment`. -/
private theorem mgf_increment_eq (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t)
    (htT : t ≤ T) :
    ∫ ω, Real.exp (a * (Y t ω - Y s ω)) ∂Q = Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
  rw [← integral_condExp (𝓕.le s), integral_congr_ae (h.condExp_exp_increment a hst htT),
    integral_const, show Q.real Set.univ = 1 from by simp, one_smul]

/-- **Increment law.** `Q.map (Y_t − Y_s) = N(0, t−s)`: the unconditional increment MGF
(`mgf_increment_eq`) is the Gaussian one. -/
theorem increment_map_eq_gaussianReal_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Q.map (fun ω ↦ Y t ω - Y s ω) = gaussianReal 0 (t - s) := by
  refine map_eq_gaussianReal_of_mgf ((h.measurable t).sub (h.measurable s)).aemeasurable
    fun a ↦ (mgf_increment_eq h a hst htT).trans ?_
  rw [NNReal.coe_sub hst]
  congr 1
  ring

/-- **Increments are independent of the past.** For `s ≤ t ≤ T`, `Y_t − Y_s` is `Q`-independent
of `𝓕_s`. Integrating the deterministic conditional moment-generating function
(`IsExpQMartingale.condExp_exp_increment`) over `A ∈ 𝓕_s` shows that the law of `Y_t − Y_s` under
`Q` restricted to `A` has the moment-generating function of `Q(A)·N(0,t−s)`, hence is that measure
(`measure_eq_of_mgf_id_eq`); on a Borel set `B` this reads
`Q({Y_t − Y_s ∈ B} ∩ A) = Q(A)·N(0,t−s)(B) = Q(A)·Q(Y_t − Y_s ∈ B)`. -/
theorem indep_increment_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Indep (MeasurableSpace.comap (fun ω ↦ Y t ω - Y s ω) inferInstance) (𝓕 s) Q := by
  have hD : Measurable fun ω ↦ Y t ω - Y s ω := (h.measurable t).sub (h.measurable s)
  have hlaw := increment_map_eq_gaussianReal_of_expMartingale h hst htT
  have hlaw' : HasLaw (fun ω ↦ Y t ω - Y s ω) (gaussianReal 0 (t - s)) Q :=
    ⟨hD.aemeasurable, hlaw⟩
  have hexp (u : ℝ) : Integrable (fun ω ↦ Real.exp (u * (Y t ω - Y s ω))) Q :=
    hlaw'.integrable_fun_comp (integrable_exp_mul_gaussianReal u)
  refine (Indep_iff _ _ Q).2 fun _ A ⟨B, hB, hBA⟩ hA ↦ ?_
  subst hBA
  have : IsFiniteMeasure (Q A • gaussianReal 0 (t - s)) :=
    Measure.smul_finite _ (measure_ne_top Q A)
  have hrestrict : (Q.restrict A).map (fun ω ↦ Y t ω - Y s ω) = Q A • gaussianReal 0 (t - s) := by
    refine measure_eq_of_mgf_id_eq (fun u ↦ (integrable_map_measure (by fun_prop)
      hD.aemeasurable).2 (hexp u).restrict) ?_
    funext u
    rw [mgf_id_map hD.aemeasurable, mgf_smul_measure, mgf_id_gaussianReal, mgf,
      ← setIntegral_condExp (𝓕.le s) (hexp u) hA,
      setIntegral_congr_ae (𝓕.le s A hA) ((h.condExp_exp_increment u hst
        htT).mono fun _ hω _ ↦ hω), setIntegral_const, NNReal.coe_sub hst, measureReal_def,
      smul_eq_mul]
    ring_nf
  have hB' := congrArg (· B) hrestrict
  simp only [Measure.map_apply hD hB, Measure.restrict_apply (hD hB), Measure.smul_apply,
    smul_eq_mul, ← hlaw] at hB'
  rw [hB', mul_comm]

/-- **Independent increments under `Q`.** On `[0,T]`, `Y` has independent increments under `Q` in
Mathlib's sense: for times `t₀ ≤ ⋯ ≤ tₙ` in `[0,T]`, the increments `Y_{t₁} − Y_{t₀}, …,
Y_{tₙ} − Y_{tₙ₋₁}` are jointly independent. Each increment is independent of the past
(`indep_increment_of_expMartingale`), and independence of the past gives joint independence
(`hasIndepIncrements_of_indep_past`). -/
theorem hasIndepIncrements_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) :
    HasIndepIncrements (fun t : Set.Iic T ↦ Y t) Q :=
  hasIndepIncrements_of_indep_past (fun t ↦ 𝓕 t) (fun _ _ hst ↦ 𝓕.mono hst)
    (fun t ↦ (h.adapted t).measurable) fun _ t hst ↦ indep_increment_of_expMartingale h hst t.2

/-- **`Y` is a Gaussian process on `[0,T]` under `Q`.** The marginals are `N(0,t)`
(`map_eq_gaussianReal_of_expMartingale`), `Y_0 = 0` a.e., and the increments are independent
(`hasIndepIncrements_of_expMartingale`), which is what
`HasIndepIncrements.isGaussianProcess` needs; `Set.Iic T` has a bottom element. -/
theorem IsExpQMartingale.isGaussianProcess (h : IsExpQMartingale Q 𝓕 Y T) :
    IsGaussianProcess (fun t : Set.Iic T ↦ Y t) Q :=
  (hasIndepIncrements_of_expMartingale h).isGaussianProcess
    (fun t ↦ (⟨(h.measurable t).aemeasurable, map_eq_gaussianReal_of_expMartingale h t.2⟩ :
      HasLaw (Y t) (gaussianReal 0 t) Q).hasGaussianLaw)
    (h.zero_start.mono fun ω hω ↦ by simpa using hω)

/-- **Mean.** `𝔼_Q[Y_t] = 0` for `t ≤ T`: the marginal law is the centred `N(0,t)`. -/
theorem IsExpQMartingale.integral_eq_zero (h : IsExpQMartingale Q 𝓕 Y T) {t : ℝ≥0}
    (htT : t ≤ T) : Q[Y t] = 0 := by
  rw [(⟨(h.measurable t).aemeasurable, map_eq_gaussianReal_of_expMartingale h htT⟩ :
    HasLaw (Y t) (gaussianReal 0 t) Q).integral_eq, integral_id_gaussianReal]

/-- **Covariance.** `cov(Y_s, Y_t) = s` for `s ≤ t ≤ T`, that is `min s t`: write
`Y_t = (Y_t − Y_s) + Y_s`; the increment is independent of `𝓕_s` and so of `Y_s`
(`indep_increment_of_expMartingale`), and `Var(Y_s) = s`. -/
theorem IsExpQMartingale.covariance_eq (h : IsExpQMartingale Q 𝓕 Y T) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) : cov[Y s, Y t; Q] = s := by
  have hs : HasLaw (Y s) (gaussianReal 0 s) Q :=
    ⟨(h.measurable s).aemeasurable, map_eq_gaussianReal_of_expMartingale h (hst.trans htT)⟩
  have hD : HasLaw (fun ω ↦ Y t ω - Y s ω) (gaussianReal 0 (t - s)) Q :=
    ⟨((h.measurable t).sub (h.measurable s)).aemeasurable,
      increment_map_eq_gaussianReal_of_expMartingale h hst htT⟩
  have hind : IndepFun (fun ω ↦ Y t ω - Y s ω) (Y s) Q :=
    (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
      (indep_increment_of_expMartingale h hst htT) (h.adapted s).measurable.comap_le)
  have h2 : Y t = (fun ω ↦ Y t ω - Y s ω) + Y s := by ext; simp
  have hs2 := hs.hasGaussianLaw.memLp_two
  have hD2 := hD.hasGaussianLaw.memLp_two
  rw [h2, covariance_add_right hs2 hD2 hs2, hind.symm.covariance_eq_zero hs2 hD2,
    covariance_self hs.aemeasurable, hs.variance_eq, variance_id_gaussianReal, zero_add]

/-- **`Y` has the finite-dimensional laws of a Brownian motion on `[0,T]` under `Q`**: zero start,
`N(0,t−s)` increments, and independent increments (`HasIndepIncrements`). Path continuity is not
part of it.

This is `IsPreBrownianReal` restricted to a horizon, and it has to be a separate predicate:
`IsPreBrownianReal Y Q` quantifies over all of `ℝ≥0`, while a Girsanov measure
`Q = μ.withDensity(Z_T)` is only defined up to the horizon `T`. Nor can it be phrased as
`IsPreBrownianReal` of the process stopped at `T`, whose increments past `T` vanish and whose
variance is `t ∧ T`, not `t`. -/
def IsBrownianOn (Q : Measure Ω) (T : ℝ≥0) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂Q, Y 0 ω = 0)
    ∧ (∀ ⦃s t : ℝ≥0⦄, s ≤ t → t ≤ T → Q.map (fun ω ↦ Y t ω - Y s ω) = gaussianReal 0 (t - s))
    ∧ HasIndepIncrements (fun t : Set.Iic T ↦ Y t) Q

/-- **Being Brownian on `[0,T]` is invariant under a modification.** If `X` and `Y` agree
`Q`-a.e. at every time `u ≤ T`, each of the three properties depends on the process only through
finitely many of its coordinates, up to `Q`-null sets. -/
theorem IsBrownianOn.congr_modification {Q : Measure Ω} {T : ℝ≥0} {X Y : ℝ≥0 → Ω → ℝ}
    (h : ∀ u ≤ T, X u =ᵐ[Q] Y u) (hX : IsBrownianOn Q T X) : IsBrownianOn Q T Y := by
  obtain ⟨h0, hlaw, hind⟩ := hX
  refine ⟨?_, fun s t hst htT ↦ ?_, fun n t ht ↦ ?_⟩
  · filter_upwards [h0, h 0 zero_le] with ω h1 h2
    rw [← h2]
    exact h1
  · rw [← hlaw hst htT]
    exact Measure.map_congr ((h t htT).sub (h s (hst.trans htT))).symm
  · exact iIndepFun.congr
      (fun i ↦ (h (t i.succ) (t i.succ).2).sub (h (t i.castSucc) (t i.castSucc).2))
      (hind n t ht)

/-- **Brownian increment laws from an exponential martingale.** From the exponential-martingale
data `IsExpQMartingale Q 𝓕 Y T`, the process `Y` is Brownian on `[0,T]` under `Q`
(`IsBrownianOn`):

* **zero start**: `Y_0 = 0` a.e. `Q` (the hypothesis `zero_start`, restated);
* **Gaussian increments**: `Y_t − Y_s ~ N(0, t−s)`
  (`increment_map_eq_gaussianReal_of_expMartingale`);
* **independent increments**: `HasIndepIncrements` for `Y` restricted to `[0,T]`
  (`hasIndepIncrements_of_expMartingale`).

Together these fix every finite-dimensional law of `Y` on `[0,T]` to that of a Brownian motion.
Path continuity is not part of the conclusion.
Process- and measure-agnostic: any drift-corrected Girsanov process supplying its own exponential
martingale (via the Bayes engine) gets these three properties by one application of this
theorem. -/
theorem isBrownianOn_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) : IsBrownianOn Q T Y :=
  ⟨h.zero_start, fun _ _ hst htT ↦ increment_map_eq_gaussianReal_of_expMartingale h hst htT,
    hasIndepIncrements_of_expMartingale h⟩

end MathFin
