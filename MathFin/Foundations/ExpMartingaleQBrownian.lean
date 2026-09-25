/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.BrownianMartingale

/-!
# Brownian increment laws from an exponential martingale

A process-agnostic packaging of the argument that turns an **exponential-martingale
hypothesis** into the increment laws of a Brownian motion under a probability measure `Q`. Fix a
probability space `(Ω, Q)`, a filtration `𝓕`, a horizon `T`, and a real process
`Y : ℝ≥0 → Ω → ℝ` that is `𝓕`-adapted, starts at `0` (a.e. `Q`), and satisfies

  `for every a : ℝ, the process t ↦ exp(a·Y_t − ½a² t) is a Q-martingale on [0,T]`.

These three data are bundled as `IsExpQMartingale Q 𝓕 Y T`. The single theorem
`isQBrownianMotion_of_expMartingale` then reads off three properties of `Y` under `Q` on `[0,T]`:
zero start, `N(0,t−s)` increments, and independent increments in Mathlib's sense
(`HasIndepIncrements`). Together they fix every finite-dimensional law of `Y` on `[0,T]` to that
of a Brownian motion. Path continuity is not part of the conclusion. Nothing in the argument
refers to how `Y` or `Q` was constructed.

The mechanism: the exponential martingale at `s = 0` fixes the marginal moment-generating
function `𝔼_Q[exp(a·Y_t)] = exp(½a²t)`, hence the marginal law, and the conditional form
`𝔼_Q[exp(a·(Y_t − Y_s))|𝓕_s] = exp(½a²(t−s))` is deterministic, giving Gaussian increments. For
successive increments over `t₀ ≤ t₁ ≤ ⋯ ≤ tₙ`, the earlier ones are `𝓕_{tₙ₋₁}`-measurable and
factor out of the conditional expectation given `𝓕_{tₙ₋₁}`, so by induction the joint
moment-generating function is the product of the Gaussian ones. Every linear combination of the
increments is then Gaussian with the diagonal variance, and `iIndepFun_iff_charFun_pi` turns that
into joint independence.

The value of the abstraction is coherence: the constant-, simple-, continuous- and
predictable-`θ` Girsanov drift-corrected processes each need only supply their own
exponential martingale (via the Bayes change-of-measure engine) and then instantiate this
one theorem.

## Main definitions and results

* `MathFin.IsExpQMartingale` — the hypothesis bundle (adapted, zero-start, exp-martingale).
* `MathFin.map_eq_gaussianReal_of_expMartingale` — the marginal law `Q.map Y_t = N(0,t)`.
* `MathFin.increment_map_eq_gaussianReal_of_expMartingale` — the increment law `N(0,t−s)`.
* `MathFin.increments_iIndepFun_of_expMartingale` — successive increments are jointly
  `Q`-independent.
* `MathFin.hasIndepIncrements_of_expMartingale` — `Y` has independent increments on `[0,T]`.
* `MathFin.increments_indepFun_of_expMartingale` — two non-overlapping increments are
  `Q`-independent.
* `MathFin.isQBrownianMotion_of_expMartingale` — the three properties packaged.
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
drift-corrected process, and exactly the data consumed by `isQBrownianMotion_of_expMartingale`. -/
structure IsExpQMartingale (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    Prop where
  /-- `Y` is adapted to the filtration. -/
  adapted : ∀ u, StronglyMeasurable[(𝓕 u : MeasurableSpace Ω)] (Y u)
  /-- `Y` starts at `0` (a.e. `Q`). -/
  zero_start : Y 0 =ᵐ[Q] 0
  /-- For every `a`, `exp(a·Y_· − ½a²·)` is a `Q`-martingale on `[0,T]`. -/
  martingale : ∀ (a : ℝ) {s t : ℝ≥0}, s ≤ t → t ≤ T → ∀ {A : Set Ω},
    MeasurableSet[(𝓕 s : MeasurableSpace Ω)] A →
      ∫ ω in A, Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) ∂Q
        = ∫ ω in A, Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2) ∂Q

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ}
  {Y : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- **A Gaussian MGF identifies the Gaussian law.** If a real random variable has the
moment-generating function of `N(0,v)` under `Q`, its law is `N(0,v)`: the MGF is then finite on
all of `ℝ`, so the complex MGFs agree, and they determine the law. -/
private theorem map_eq_gaussianReal_of_mgf {X : Ω → ℝ} (hX : Measurable X) {v : ℝ≥0}
    (hmgf : mgf X Q = mgf id (gaussianReal 0 v)) : Q.map X = gaussianReal 0 v := by
  have hIES : integrableExpSet X Q = Set.univ := by
    rw [integrableExpSet_eq_of_mgf hmgf, Set.eq_univ_iff_forall]
    exact fun a ↦ integrable_exp_mul_gaussianReal a
  have hset : {z : ℂ | z.re ∈ interior (integrableExpSet X Q)} = Set.univ := by
    rw [hIES, interior_univ]; ext z; simp
  have hcomplexeq : complexMGF X Q = complexMGF id (gaussianReal 0 v) := by
    funext z; exact eqOn_complexMGF_of_mgf hmgf (hset ▸ Set.mem_univ z)
  have hmap := Measure.ext_of_complexMGF_eq (μ := Q) (μ' := gaussianReal 0 v)
    hX.aemeasurable aemeasurable_id hcomplexeq
  rwa [Measure.map_id] at hmap

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
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    show Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2)
        = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * Real.exp (a * Y t ω)
    rw [show a * Y t ω - a ^ 2 * (t : ℝ) / 2 = -(a ^ 2 * (t : ℝ) / 2) + a * Y t ω from by ring,
      Real.exp_add]
  rw [hLHS, mul_comm] at hbrick
  have hfac : Real.exp (-(a ^ 2 * (t : ℝ) / 2)) ≠ 0 := (Real.exp_pos _).ne'
  rw [(mul_eq_one_iff_eq_inv₀ hfac).mp hbrick, ← Real.exp_neg]
  congr 1; ring

/-- **Marginal law.** `Q.map Y_t = N(0, t)`: the `Q`-MGF is the Gaussian MGF (`mgf_expY_eq`),
which identifies the law (`map_eq_gaussianReal_of_mgf`). -/
theorem map_eq_gaussianReal_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {t : ℝ≥0}
    (htT : t ≤ T) : Q.map (Y t) = gaussianReal 0 t := by
  refine map_eq_gaussianReal_of_mgf ((h.adapted t).mono (𝓕.le t)).measurable ?_
  rw [mgf_id_gaussianReal]
  funext a
  show ∫ ω, Real.exp (a * Y t ω) ∂Q = Real.exp (0 * a + (t : ℝ) * a ^ 2 / 2)
  rw [mgf_expY_eq h htT a, zero_mul, zero_add]

/-- **Marginal `Q`-integrability.** `exp(a·Y_u)` is `Q`-integrable for `u ≤ T` — its law is
`N(0,u)` and the Gaussian MGF is finite. -/
private theorem integrable_expY (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {u : ℝ≥0} (huT : u ≤ T) :
    Integrable (fun ω ↦ Real.exp (a * Y u ω)) Q := by
  have hmeasY : Measurable (Y u) := ((h.adapted u).mono (𝓕.le u)).measurable
  rw [show (fun ω ↦ Real.exp (a * Y u ω)) = (fun x ↦ Real.exp (a * x)) ∘ (Y u) from rfl,
      ← integrable_map_measure (by fun_prop) hmeasY.aemeasurable,
      map_eq_gaussianReal_of_expMartingale h huT]
  exact integrable_exp_mul_gaussianReal a

/-- **Conditional exponential martingale.** `𝔼_Q[exp(a·Y_t − ½a² t)|𝓕_s] = exp(a·Y_s − ½a² s)`
a.e., the conditional form of the `martingale` field (its set-integral identity converted via
`ae_eq_condExp_of_forall_setIntegral_eq`). -/
private theorem condExp_expY (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t)
    (htT : t ≤ T) :
    Q[fun ω ↦ Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) | 𝓕 s]
      =ᵐ[Q] fun ω ↦ Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2) := by
  have hfint : ∀ u : ℝ≥0, u ≤ T →
      Integrable (fun ω ↦ Real.exp (a * Y u ω - a ^ 2 * (u : ℝ) / 2)) Q := by
    intro u huT
    have hfac : (fun ω ↦ Real.exp (a * Y u ω - a ^ 2 * (u : ℝ) / 2))
        = fun ω ↦ Real.exp (-(a ^ 2 * (u : ℝ) / 2)) * Real.exp (a * Y u ω) := by
      funext ω
      rw [show a * Y u ω - a ^ 2 * (u : ℝ) / 2 = -(a ^ 2 * (u : ℝ) / 2) + a * Y u ω from by ring,
        Real.exp_add]
    rw [hfac]; exact (integrable_expY h a huT).const_mul _
  have hsm : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)]
      (fun ω ↦ Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2)) := by
    have hcont : Continuous fun x : ℝ ↦ a * x - a ^ 2 * (s : ℝ) / 2 := by fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable (hcont.comp_stronglyMeasurable (h.adapted s))
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hfint t htT)
    (fun A _ _ ↦ (hfint s (hst.trans htT)).integrableOn) (fun A hA _ ↦ ?_)
    hsm.aestronglyMeasurable).symm
  exact (h.martingale a hst htT hA).symm

/-- **Conditional `Q`-MGF of the increment.** `𝔼_Q[exp(a·(Y_t − Y_s))|𝓕_s] = exp(½a²(t−s))` a.e.,
deterministic. Pull the `𝓕_s`-measurable factor `exp(½a²t − a·Y_s)` out of `condExp_expY`. -/
private theorem condExp_Y_increment (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Q[fun ω ↦ Real.exp (a * (Y t ω - Y s ω)) | 𝓕 s]
      =ᵐ[Q] fun _ ↦ Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
  have hmeasY : ∀ v, Measurable (Y v) := fun v ↦ ((h.adapted v).mono (𝓕.le v)).measurable
  set ft : Ω → ℝ := fun ω ↦ Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) with hftdef
  set gs : Ω → ℝ := fun ω ↦ Real.exp (a ^ 2 * (t : ℝ) / 2 - a * Y s ω) with hgsdef
  have hgs_sm : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)] gs := by
    have hcont : Continuous fun x : ℝ ↦ a ^ 2 * (t : ℝ) / 2 - a * x := by fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable (hcont.comp_stronglyMeasurable (h.adapted s))
  have hft_int : Integrable ft Q := by
    have hfac : ft = fun ω ↦ Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * Real.exp (a * Y t ω) := by
      funext ω
      show Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2)
          = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * Real.exp (a * Y t ω)
      rw [show a * Y t ω - a ^ 2 * (t : ℝ) / 2 = -(a ^ 2 * (t : ℝ) / 2) + a * Y t ω from by ring,
        Real.exp_add]
    rw [hfac]; exact (integrable_expY h a htT).const_mul _
  have hprod : (fun ω ↦ gs ω * ft ω) = fun ω ↦ Real.exp (a * (Y t ω - Y s ω)) := by
    funext ω; rw [hgsdef, hftdef, ← Real.exp_add]; congr 1; ring
  have hprod_int : Integrable (fun ω ↦ gs ω * ft ω) Q := by
    rw [hprod]
    have hbnd : Integrable (fun ω ↦ Real.exp (2 * a * Y t ω) + Real.exp (-2 * a * Y s ω)) Q :=
      (integrable_expY h (2 * a) htT).add (integrable_expY h (-2 * a) (hst.trans htT))
    refine Integrable.mono' hbnd
      (Real.measurable_exp.comp (((hmeasY t).sub (hmeasY s)).const_mul a)).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    have ep : Real.exp (2 * a * Y t ω) = Real.exp (a * Y t ω) ^ 2 := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have eq' : Real.exp (-2 * a * Y s ω) = Real.exp (-a * Y s ω) ^ 2 := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have eprod : Real.exp (a * (Y t ω - Y s ω))
        = Real.exp (a * Y t ω) * Real.exp (-a * Y s ω) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [ep, eq', eprod]
    nlinarith [sq_nonneg (Real.exp (a * Y t ω) - Real.exp (-a * Y s ω)),
      (Real.exp_pos (a * Y t ω)).le, (Real.exp_pos (-a * Y s ω)).le]
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
tower property on the deterministic conditional MGF `condExp_Y_increment`. -/
private theorem Y_increment_mgf (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t)
    (htT : t ≤ T) :
    ∫ ω, Real.exp (a * (Y t ω - Y s ω)) ∂Q = Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
  rw [← integral_condExp (𝓕.le s), integral_congr_ae (condExp_Y_increment h a hst htT),
    integral_const, show Q.real Set.univ = 1 from by simp, one_smul]

/-- **Increment law.** `Q.map (Y_t − Y_s) = N(0, t−s)`: the unconditional increment MGF
(`Y_increment_mgf`) is the Gaussian one. -/
theorem increment_map_eq_gaussianReal_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Q.map (fun ω ↦ Y t ω - Y s ω) = gaussianReal 0 (t - s) := by
  have hmeasY : ∀ v, Measurable (Y v) := fun v ↦ ((h.adapted v).mono (𝓕.le v)).measurable
  have hincmeas : Measurable (fun ω ↦ Y t ω - Y s ω) := (hmeasY t).sub (hmeasY s)
  refine map_eq_gaussianReal_of_mgf hincmeas ?_
  rw [mgf_id_gaussianReal]
  funext a
  show ∫ ω, Real.exp (a * (Y t ω - Y s ω)) ∂Q = Real.exp (0 * a + ((t - s : ℝ≥0) : ℝ) * a ^ 2 / 2)
  rw [Y_increment_mgf h a hst htT, NNReal.coe_sub hst]; congr 1; ring

/-- **`Q`-integrability of the increment exponential.** `exp(c·(Y_t − Y_s))` is `Q`-integrable —
its law is `N(0,t−s)`. -/
private theorem integrable_exp_Y_increment (h : IsExpQMartingale Q 𝓕 Y T) (c : ℝ) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Integrable (fun ω ↦ Real.exp (c * (Y t ω - Y s ω))) Q := by
  have hmeasY : ∀ v, Measurable (Y v) := fun v ↦ ((h.adapted v).mono (𝓕.le v)).measurable
  have hincmeas : Measurable (fun ω ↦ Y t ω - Y s ω) := (hmeasY t).sub (hmeasY s)
  rw [show (fun ω ↦ Real.exp (c * (Y t ω - Y s ω)))
        = (fun x ↦ Real.exp (c * x)) ∘ (fun ω ↦ Y t ω - Y s ω) from rfl,
      ← integrable_map_measure (by fun_prop) hincmeas.aemeasurable,
      increment_map_eq_gaussianReal_of_expMartingale h hst htT]
  exact integrable_exp_mul_gaussianReal c

/-! ### Independence of any number of increments -/

/-- **Joint `Q`-MGF of successive increments.** For a monotone sequence of times `t` in `[0,T]` and
reals `a`, `exp(∑_{k<n} a_k·(Y_{t_{k+1}} − Y_{t_k}))` is `Q`-integrable, with integral
`∏_{k<n} exp(½a_k²(t_{k+1} − t_k))`. Induction on `n`: the first `n` increments are
`𝓕_{t_n}`-measurable, so they factor out of the conditional expectation given `𝓕_{t_n}`, and the
conditional MGF of the last one is the deterministic `exp(½a_n²(t_{n+1} − t_n))`
(`condExp_Y_increment`). Integrability comes along the induction, from `eˣeʸ ≤ e²ˣ + e²ʸ`. -/
private theorem Y_increments_mgf_range (h : IsExpQMartingale Q 𝓕 Y T) {t : ℕ → ℝ≥0}
    (ht : Monotone t) (htT : ∀ k, t k ≤ T) (n : ℕ) (a : ℕ → ℝ) :
    Integrable (fun ω ↦ Real.exp (∑ k ∈ Finset.range n, a k * (Y (t (k + 1)) ω - Y (t k) ω))) Q ∧
      ∫ ω, Real.exp (∑ k ∈ Finset.range n, a k * (Y (t (k + 1)) ω - Y (t k) ω)) ∂Q
        = ∏ k ∈ Finset.range n, Real.exp (a k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ)) / 2) := by
  induction n generalizing a with
  | zero => constructor <;> simp [integrable_const]
  | succ n ih =>
    have hmeasY : ∀ w, Measurable (Y w) := fun w ↦ ((h.adapted w).mono (𝓕.le w)).measurable
    have htn : t n ≤ t (n + 1) := ht (Nat.le_add_right n 1)
    set e1 : Ω → ℝ :=
      fun ω ↦ Real.exp (∑ k ∈ Finset.range n, a k * (Y (t (k + 1)) ω - Y (t k) ω)) with he1def
    set e2 : Ω → ℝ := fun ω ↦ Real.exp (a n * (Y (t (n + 1)) ω - Y (t n) ω)) with he2def
    have hsplit : (fun ω ↦ Real.exp (∑ k ∈ Finset.range (n + 1),
        a k * (Y (t (k + 1)) ω - Y (t k) ω))) = e1 * e2 := by
      funext ω
      simp only [he1def, he2def, Pi.mul_apply]
      rw [Finset.sum_range_succ, Real.exp_add]
    have he1_sm : StronglyMeasurable[(𝓕 (t n) : MeasurableSpace Ω)] e1 := by
      refine Real.continuous_exp.comp_stronglyMeasurable
        (Finset.stronglyMeasurable_fun_sum _ fun k hk ↦ ?_)
      have hk : k + 1 ≤ n := Finset.mem_range.mp hk
      have hpair : StronglyMeasurable[(𝓕 (t n) : MeasurableSpace Ω)]
          (fun ω ↦ (Y (t (k + 1)) ω, Y (t k) ω)) :=
        ((h.adapted _).mono (𝓕.mono (ht hk))).prodMk
          ((h.adapted _).mono (𝓕.mono (ht (Nat.le_of_succ_le hk))))
      have hcont : Continuous fun p : ℝ × ℝ ↦ a k * (p.1 - p.2) := by fun_prop
      exact hcont.comp_stronglyMeasurable hpair
    have he1meas : Measurable e1 := (he1_sm.mono (𝓕.le (t n))).measurable
    have he2meas : Measurable e2 := by
      rw [he2def]
      exact Real.measurable_exp.comp (((hmeasY (t (n + 1))).sub (hmeasY (t n))).const_mul (a n))
    have he2_int : Integrable e2 Q := by
      rw [he2def]; exact integrable_exp_Y_increment h (a n) htn (htT _)
    have hprod_int : Integrable (e1 * e2) Q := by
      have hbnd : Integrable (fun ω ↦
          Real.exp (∑ k ∈ Finset.range n, (2 * a k) * (Y (t (k + 1)) ω - Y (t k) ω))
            + Real.exp ((2 * a n) * (Y (t (n + 1)) ω - Y (t n) ω))) Q :=
        (ih fun k ↦ 2 * a k).1.add (integrable_exp_Y_increment h (2 * a n) htn (htT _))
      refine Integrable.mono' hbnd (he1meas.mul he2meas).aestronglyMeasurable ?_
      filter_upwards with ω
      simp only [Pi.mul_apply, he1def, he2def]
      rw [Real.norm_of_nonneg (by positivity)]
      have ep1 : Real.exp (∑ k ∈ Finset.range n, (2 * a k) * (Y (t (k + 1)) ω - Y (t k) ω))
          = Real.exp (∑ k ∈ Finset.range n, a k * (Y (t (k + 1)) ω - Y (t k) ω)) ^ 2 := by
        rw [pow_two, ← Real.exp_add, ← Finset.sum_add_distrib]
        exact congrArg Real.exp (Finset.sum_congr rfl fun k _ ↦ by ring)
      have ep2 : Real.exp ((2 * a n) * (Y (t (n + 1)) ω - Y (t n) ω))
          = Real.exp (a n * (Y (t (n + 1)) ω - Y (t n) ω)) ^ 2 := by
        rw [pow_two, ← Real.exp_add]; congr 1; ring
      rw [ep1, ep2]
      nlinarith [sq_nonneg (Real.exp (∑ k ∈ Finset.range n, a k * (Y (t (k + 1)) ω - Y (t k) ω))
          - Real.exp (a n * (Y (t (n + 1)) ω - Y (t n) ω))),
        (Real.exp_pos (∑ k ∈ Finset.range n, a k * (Y (t (k + 1)) ω - Y (t k) ω))).le,
        (Real.exp_pos (a n * (Y (t (n + 1)) ω - Y (t n) ω))).le]
    have hpull := condExp_mul_of_stronglyMeasurable_left (m := (𝓕 (t n) : MeasurableSpace Ω))
      he1_sm hprod_int he2_int
    have hcond2 := condExp_Y_increment h (a n) htn (htT (n + 1))
    rw [← he2def] at hcond2
    have he1int : ∫ ω, e1 ω ∂Q
        = ∏ k ∈ Finset.range n, Real.exp (a k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ)) / 2) := by
      simp only [he1def]; exact (ih a).2
    refine ⟨by rw [hsplit]; exact hprod_int, ?_⟩
    calc ∫ ω, Real.exp (∑ k ∈ Finset.range (n + 1), a k * (Y (t (k + 1)) ω - Y (t k) ω)) ∂Q
        = ∫ ω, (e1 * e2) ω ∂Q := by rw [hsplit]
      _ = ∫ ω, (Q[e1 * e2 | 𝓕 (t n)]) ω ∂Q := (integral_condExp (𝓕.le (t n))).symm
      _ = ∫ ω, e1 ω * Real.exp (a n ^ 2 * ((t (n + 1) : ℝ) - (t n : ℝ)) / 2) ∂Q := by
          refine integral_congr_ae ?_
          filter_upwards [hpull, hcond2] with ω hp hc
          rw [hp, Pi.mul_apply, hc]
      _ = (∫ ω, e1 ω ∂Q) * Real.exp (a n ^ 2 * ((t (n + 1) : ℝ) - (t n : ℝ)) / 2) :=
          integral_mul_const _ _
      _ = ∏ k ∈ Finset.range (n + 1), Real.exp (a k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ)) / 2) := by
          rw [he1int, Finset.prod_range_succ]

/-- **Linear combinations of successive increments are Gaussian under `Q`.** For a monotone
sequence of times in `[0,T]` and reals `c`, `∑_{k<n} c_k·(Y_{t_{k+1}} − Y_{t_k})` has law
`N(0, ∑_{k<n} c_k²(t_{k+1} − t_k))` under `Q`: its `Q`-MGF is the Gaussian one
(`Y_increments_mgf_range`). -/
private theorem Y_linComb_range_map_eq_gaussianReal (h : IsExpQMartingale Q 𝓕 Y T)
    {t : ℕ → ℝ≥0} (ht : Monotone t) (htT : ∀ k, t k ≤ T) (n : ℕ) (c : ℕ → ℝ) :
    Q.map (fun ω ↦ ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω))
      = gaussianReal 0
          (Real.toNNReal (∑ k ∈ Finset.range n, c k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ)))) := by
  have hmeasY : ∀ w, Measurable (Y w) := fun w ↦ ((h.adapted w).mono (𝓕.le w)).measurable
  have hσ2 : 0 ≤ ∑ k ∈ Finset.range n, c k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ)) :=
    Finset.sum_nonneg fun k _ ↦ mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (by exact_mod_cast ht (Nat.le_add_right k 1)))
  have hlin : Measurable fun ω ↦ ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω) :=
    Finset.measurable_sum _ fun k _ ↦ ((hmeasY _).sub (hmeasY _)).const_mul (c k)
  refine map_eq_gaussianReal_of_mgf hlin ?_
  rw [mgf_id_gaussianReal]
  funext r
  have hr : (fun ω ↦ Real.exp (r * ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω)))
      = fun ω ↦ Real.exp (∑ k ∈ Finset.range n, (r * c k) * (Y (t (k + 1)) ω - Y (t k) ω)) := by
    funext ω; simp only [Finset.mul_sum, mul_assoc]
  have hmgfn :
      ∫ ω, Real.exp (∑ k ∈ Finset.range n, (r * c k) * (Y (t (k + 1)) ω - Y (t k) ω)) ∂Q
        = ∏ k ∈ Finset.range n, Real.exp ((r * c k) ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ)) / 2) :=
    (Y_increments_mgf_range h ht htT n fun k ↦ r * c k).2
  show ∫ ω, Real.exp (r * ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω)) ∂Q
      = Real.exp (0 * r + ((∑ k ∈ Finset.range n,
          c k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ))).toNNReal : ℝ) * r ^ 2 / 2)
  rw [hr, hmgfn, ← Real.exp_sum, Real.coe_toNNReal _ hσ2, zero_mul, zero_add, Finset.sum_mul,
    Finset.sum_div]
  exact congrArg Real.exp (Finset.sum_congr rfl fun k _ ↦ by ring)

/-- **Successive increments are jointly `Q`-independent.** For a monotone sequence of times `t` in
`[0,T]`, the increments `Y_{t_{k+1}} − Y_{t_k}`, `k < n`, are independent under `Q`. By
`iIndepFun_iff_charFun_pi` independence is the factorisation of the joint characteristic function.
At `w` it is the characteristic function at `1` of the Gaussian linear combination
`∑_k w_k·(Y_{t_{k+1}} − Y_{t_k})` (`Y_linComb_range_map_eq_gaussianReal`), which is the product of
the marginal Gaussian characteristic functions. -/
theorem increments_iIndepFun_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {t : ℕ → ℝ≥0}
    (ht : Monotone t) (htT : ∀ k, t k ≤ T) (n : ℕ) :
    iIndepFun (fun (i : Fin n) ω ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω) Q := by
  have hmeasY : ∀ w, Measurable (Y w) := fun w ↦ ((h.adapted w).mono (𝓕.le w)).measurable
  have hX (i : Fin n) : AEMeasurable (fun ω ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω) Q :=
    ((hmeasY _).sub (hmeasY _)).aemeasurable
  refine (iIndepFun_iff_charFun_pi hX).mpr fun w ↦ ?_
  set c : ℕ → ℝ := fun k ↦ if hk : k < n then w ⟨k, hk⟩ else 0
  have hc (i : Fin n) : c i = w i := dif_pos i.isLt
  have hσ2 : 0 ≤ ∑ k ∈ Finset.range n, c k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ)) :=
    Finset.sum_nonneg fun k _ ↦ mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (by exact_mod_cast ht (Nat.le_add_right k 1)))
  -- the joint characteristic function at `w` is that of `∑ₖ wₖ·(Y_{tₖ₊₁} − Y_{tₖ})` at `1`
  have hjoint : charFun (Q.map fun ω ↦
        WithLp.toLp 2 fun i : Fin n ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω) w
      = charFun (Q.map fun ω ↦ ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω)) 1 := by
    have hvec : Measurable fun ω ↦
        WithLp.toLp 2 fun i : Fin n ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω :=
      (WithLp.measurable_toLp 2 _).comp <| measurable_pi_lambda
        (fun ω (i : Fin n) ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω) fun i ↦ (hmeasY _).sub (hmeasY _)
    have hlin : Measurable fun ω ↦ ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω) :=
      Finset.measurable_sum _ fun k _ ↦ ((hmeasY _).sub (hmeasY _)).const_mul (c k)
    rw [charFun_apply, charFun_apply_real, integral_map hvec.aemeasurable (by fun_prop),
      integral_map hlin.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    have hinner : ⟪WithLp.toLp 2 fun i : Fin n ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω, w⟫
        = ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω) := by
      rw [PiLp.inner_apply, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hc i]
      simp only [PiLp.toLp_apply, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
      ring
    simp only [hinner, Complex.ofReal_one, one_mul]
  have hmarg (i : Fin n) : charFun (Q.map fun ω ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω) (w i)
      = Complex.exp ((-(w i ^ 2 * ((t ((i : ℕ) + 1) : ℝ) - (t i : ℝ)) / 2) : ℝ) : ℂ) := by
    rw [increment_map_eq_gaussianReal_of_expMartingale h (ht (Nat.le_add_right _ 1)) (htT _),
      charFun_gaussianReal, NNReal.coe_sub (ht (Nat.le_add_right _ 1))]
    congr 1
    push_cast
    ring
  have hsum : ∑ i : Fin n, -(w i ^ 2 * ((t ((i : ℕ) + 1) : ℝ) - (t i : ℝ)) / 2)
      = -(∑ k ∈ Finset.range n, c k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ))) / 2 := by
    rw [← Fin.sum_univ_eq_sum_range, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hc i]
  have hL : charFun (Q.map fun ω ↦ ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω)) 1
      = Complex.exp ((-(∑ k ∈ Finset.range n, c k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ))) / 2 : ℝ)
          : ℂ) := by
    rw [Y_linComb_range_map_eq_gaussianReal h ht htT n c, charFun_gaussianReal,
      Real.coe_toNNReal _ hσ2]
    congr 1
    push_cast
    ring
  have hR : ∏ i : Fin n, charFun (Q.map fun ω ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω) (w i)
      = Complex.exp ((-(∑ k ∈ Finset.range n, c k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ))) / 2 : ℝ)
          : ℂ) := by
    rw [Finset.prod_congr rfl fun i _ ↦ hmarg i, ← Complex.exp_sum, ← Complex.ofReal_sum, hsum]
  exact hjoint.trans (hL.trans hR.symm)

/-- **Independent increments under `Q`.** On `[0,T]`, `Y` has independent increments under `Q` in
Mathlib's sense: for times `t₀ ≤ ⋯ ≤ tₙ` in `[0,T]`, the increments `Y_{t₁} − Y_{t₀}, …,
Y_{tₙ} − Y_{tₙ₋₁}` are jointly independent. Every finite family of increments along a monotone
sequence sits inside the first `N` of them (`increments_iIndepFun_of_expMartingale`). -/
theorem hasIndepIncrements_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) :
    HasIndepIncrements (fun t : Set.Iic T ↦ Y t) Q := by
  refine HasIndepIncrements.of_nat fun τ hτ _ ↦ iIndepFun_iff_finset.2 fun S ↦ ?_
  obtain ⟨N, hN⟩ : ∃ N, ∀ k ∈ S, k < N :=
    ⟨S.sup id + 1, fun k hk ↦ Nat.lt_add_one_of_le (Finset.le_sup (f := id) hk)⟩
  exact (increments_iIndepFun_of_expMartingale h (t := fun k ↦ (τ k : ℝ≥0))
      (fun i j hij ↦ Subtype.coe_le_coe.mpr (hτ hij)) (fun k ↦ Set.mem_Iic.mp (τ k).2) N).precomp
    (g := fun k : S ↦ (⟨k, hN k k.2⟩ : Fin N)) fun a b hab ↦ Subtype.ext (congrArg Fin.val hab)

/-- **Two non-overlapping increments are `Q`-independent.** For `s ≤ t ≤ u ≤ v ≤ T`, `Y_t − Y_s`
and `Y_v − Y_u` are independent under `Q`: they are the first and third increments along
`s ≤ t ≤ u ≤ v` (`increments_iIndepFun_of_expMartingale`). -/
theorem increments_indepFun_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {s t u v : ℝ≥0}
    (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    IndepFun (fun ω ↦ Y t ω - Y s ω) (fun ω ↦ Y v ω - Y u ω) Q := by
  let τ : ℕ → ℝ≥0
    | 0 => s
    | 1 => t
    | 2 => u
    | _ => v
  have hτ : Monotone τ := monotone_nat_of_le_succ fun
    | 0 => hst
    | 1 => htu
    | 2 => huv
    | _ + 3 => le_rfl
  have hτT : ∀ k, τ k ≤ T := fun
    | 0 => hst.trans (htu.trans (huv.trans hvT))
    | 1 => htu.trans (huv.trans hvT)
    | 2 => huv.trans hvT
    | _ + 3 => hvT
  exact (increments_iIndepFun_of_expMartingale h hτ hτT 3).indepFun
    (show (0 : Fin 3) ≠ 2 by decide)

/-- **Brownian increment laws from an exponential martingale.** From the exponential-martingale
data `IsExpQMartingale Q 𝓕 Y T`, the process `Y` has three properties under `Q` on `[0,T]`:

* **zero start**: `Y_0 = 0` a.e. `Q`;
* **Gaussian increments**: `Y_t − Y_s ~ N(0, t−s)`
  (`increment_map_eq_gaussianReal_of_expMartingale`);
* **independent increments**: `HasIndepIncrements` for `Y` restricted to `[0,T]`
  (`hasIndepIncrements_of_expMartingale`).

Together these fix every finite-dimensional law of `Y` on `[0,T]` to that of a Brownian motion.
Path continuity is not part of the conclusion. Process- and measure-agnostic: any drift-corrected
Girsanov process supplying its own exponential martingale (via the Bayes engine) gets these three
properties by one application of this theorem. -/
theorem isQBrownianMotion_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) :
    (∀ᵐ ω ∂Q, Y 0 ω = 0)
      ∧ (∀ ⦃s t : ℝ≥0⦄, s ≤ t → t ≤ T →
          Q.map (fun ω ↦ Y t ω - Y s ω) = gaussianReal 0 (t - s))
      ∧ HasIndepIncrements (fun t : Set.Iic T ↦ Y t) Q := by
  refine ⟨?_, fun s t hst htT ↦ increment_map_eq_gaussianReal_of_expMartingale h hst htT,
    hasIndepIncrements_of_expMartingale h⟩
  filter_upwards [h.zero_start] with ω hω
  simpa using hω

end MathFin
