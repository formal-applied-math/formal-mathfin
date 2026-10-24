/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Foundations.CarrMadan
public import MathFin.Foundations.GyongyMimicry
public import MathFin.BlackScholes.CallSpreadDigital


/-!
# Dupire's formula, distributional form

Bagaria ch. 9 Thm 9.5 at zero rates reads `σ²_loc(T, K) = 2·∂_T C / (K²·∂²_K C)`. The
classical proof tests the forward equation against the call payoff `(x − K)⁺` and integrates
by parts twice (`(x − K)⁺'' = δ_K`). That step has no honest counterpart here: `(x − K)⁺` is
not `C²`, so it is outside the test class of the landed weak forward equation
(`GyongyMimicry.marginal_flow_weak_equation_fn_constructed`), and evaluating at `x = K` is
the pointwise-density route — the route this module does not take. Instead the strike is
smeared first: every smooth compactly supported strike density `ψ` yields a legitimate test
function `f_ψ` (its double primitive) which *is* the static call book
`∫ ψ(K)(x − K)⁺ dK` (Carr–Madan, `MathFin.carrMadan_spanning`). Fubini then turns
`𝔼[f_ψ(X_T)]` into the pairing `∫ ψ(K) C(T, K) dK` of the *defined* call surface.

## Proved (complete proofs, standard-three axioms)

* `callSurface` — `C(s, K) = 𝔼[(X_{s⁺} − K)⁺]`, a `def`; no theorem takes `C` as a variable.
* `span_of_vanish_left` — all-`S` Carr–Madan spanning for a payoff flat-zero on the left.
* `call_spanning_compactSupport` — the test-function factory `ψ ↦ f_ψ`.
* `integral_payoff_eq_integral_call` — Fubini: `𝔼[∫ψ(K)(X_s − K)⁺dK] = ∫ψ(K)C(s, K)dK`.
* `breedenLitzenberger_weak` — `∫ ψ''(K) C(s, K) dK = 𝔼ψ(X_s)` for any integrable law.
* `forward_eq_weak_zeroRate` — `GyongyMimicry.marginal_flow_weak_equation_fn_constructed` at
  `β = 0`, drift term erased (the honest weak form of the (t, x) forward equation).
* **`dupire_weak`** (headline) — `d/dT ∫ψ(K)C(T, K)dK = ½·𝔼[ψ(X_T)·b̂²(T, X_T)]`.

Together, `dupire_weak` and `breedenLitzenberger_weak` say `∂_T C = ½·b̂²(T, ·)·∂²_K C` in
`D'(ℝ_K)`, `b̂² = 𝔼[δ_T² | X_T = ·]` the Gyöngy coefficient: Thm 9.5 ∘ Thm 9.7 in
distributional form, with no density, no Tanaka formula, and no regularity hypothesis.

## Not claimed here

* The pointwise ratio at a single strike without regularity hypotheses: the version proved
  in the second half of this file (`dupire_pointwise`) carries C²-in-`K` / C¹-in-`T`
  regularity of the call surface (with continuous `C_KK`, jointly continuous `C_T`) plus a
  continuous version of `b̂²` as hypotheses.
* Nonzero rates / lognormal `δ = σ_loc·S`: the process class is `BoundedItoProcess`
  (bounded drift and diffusion); the lognormal flat-vol check (Ex. 9.2) is therefore outside
  this module's bounded-coefficient class.
* Existence of the local-vol diffusion that reproduces `C` (`GyongyMimicry.gyongy_mimicry_gated`).
-/

@[expose] public section



open MeasureTheory ProbabilityTheory Filter Topology
open MathFin ItoIntegralL2 ItoIntegralProcessGeneral
open scoped NNReal Interval

-- the `C^∞` smoothness index of `ContDiff` (Mathlib's `ContDiff`-scoped `∞`, restated locally
-- because that scope also claims `ω`, the sample-point binder of this file)
local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

namespace MathFin.Dupire

/-- **The call-price surface** of an `ℝ≥0`-indexed price process `X` under the pricing
measure `μ` (zero rates): `C(s, K) = 𝔼[(X_{s⁺} − K)⁺]`. A *definition* — never a free
variable of any theorem below (every `C` in a statement below is this
defined surface; no theorem takes a call surface as a hypothesis). -/
noncomputable def callSurface {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (s K : ℝ) : ℝ :=
  ∫ ω, max (X (Real.toNNReal s) ω - K) 0 ∂μ

section Spanning

/-- A compactly supported function vanishes (off its topological support) on a whole left
half-line: there is `L` with `K ∉ tsupport ψ` for every `K ≤ L`. -/
theorem exists_le_notMem_tsupport {ψ : ℝ → ℝ} (hψc : HasCompactSupport ψ) :
    ∃ L : ℝ, ∀ K ≤ L, K ∉ tsupport ψ := by
  obtain ⟨m, hm⟩ := hψc.isCompact.bddBelow
  exact ⟨m - 1, fun K hK hKs => by linarith [hm hKs]⟩

/-- **Carr–Madan spanning on the whole line, for a payoff flat-zero at the left.** If
`f'' = φ` with `φ` continuous and zero on `(-∞, L]`, and `f L = f' L = 0`, then for *every*
spot `S`, `f S = ∫ K, φ K · (S − K)⁺ dK` — a static book of calls in density `φ`.
Engine: `MathFin.carrMadan_spanning` (compact strike range `[min L S, max L S]`, reference
level `κ = L`); the put leg vanishes because `φ = 0` left of `L`, and the call leg's interval
integral is the whole-line integral because its integrand vanishes off `(L, max L S]`. -/
theorem span_of_vanish_left {φ f f' : ℝ → ℝ} {L : ℝ} (hφ : Continuous φ)
    (hφL : ∀ K ≤ L, φ K = 0)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (φ x) x)
    (hfL : f L = 0) (hf'L : f' L = 0) (S : ℝ) :
    f S = ∫ K, φ K * max (S - K) 0 := by
  have cm := carrMadan_spanning (L := min L S) (U := max L S) (κ := L) (S := S)
    (min_le_left L S) (le_max_left L S) ⟨min_le_right L S, le_max_right L S⟩
    (fun t _ => hf t) (fun t _ => hf' t) hφ.continuousOn
  have hput : (∫ K in (min L S)..L, φ K * max (K - S) 0) = 0 := by
    have h0 : Set.EqOn (fun K => φ K * max (K - S) 0) (fun _ => (0 : ℝ))
        (Set.uIcc (min L S) L) := by
      intro K hK
      rw [Set.uIcc_of_le (min_le_left L S)] at hK
      simp [hφL K hK.2]
    rw [intervalIntegral.integral_congr h0]; simp
  have hcall : (∫ K in L..(max L S), φ K * max (S - K) 0) = ∫ K, φ K * max (S - K) 0 := by
    rw [intervalIntegral.integral_of_le (le_max_left L S)]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun K hK => ?_
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hK
    rcases hK with hK | hK
    · simp [hφL K hK]
    · have : S - K ≤ 0 := by linarith [le_max_right L S]
      simp [max_eq_right this]
  rw [cm, hfL, hf'L, hput, hcall]; ring

end Spanning

section Fubini

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Fubini for a strike-smeared call book.** For an integrable time-`s` marginal `X_{s⁺}`
and a continuous compactly supported strike density `ψ`, the expected payoff of the static
call book `∫ K, ψ K · (x − K)⁺ dK` is the `ψ`-pairing of the *defined* call surface:

  `𝔼[∫ ψ(K)(X_{s⁺} − K)⁺ dK] = ∫ ψ(K) · C(s, K) dK`.

Domination: `|ψ K · (X − K)⁺| ≤ |X|·|ψ K| + |ψ K|·|K|`, integrable on `μ ⊗ dK`
(`Integrable.mul_prod` twice). Then `integral_integral_swap`. -/
theorem integral_payoff_eq_integral_call [IsFiniteMeasure μ] {X : ℝ≥0 → Ω → ℝ} {s : ℝ}
    (hX : Integrable (X (Real.toNNReal s)) μ) {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ ω, (∫ K, ψ K * max (X (Real.toNNReal s) ω - K) 0) ∂μ
      = ∫ K, ψ K * callSurface μ X s K := by
  set Y := X (Real.toNNReal s)
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have hψKi : Integrable (fun K => |ψ K| * |K|) :=
    (hψ.abs.mul continuous_abs).integrable_of_hasCompactSupport
      (hψc.abs.mul_right)
  have hdom : Integrable (fun p : Ω × ℝ => |Y p.1| * |ψ p.2| + (1 : ℝ) * (|ψ p.2| * |p.2|))
      (μ.prod volume) :=
    (hX.abs.mul_prod hψi.abs).add ((integrable_const (1 : ℝ)).mul_prod hψKi)
  have hint : Integrable (Function.uncurry fun ω K => ψ K * max (Y ω - K) 0)
      (μ.prod volume) := by
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : AEStronglyMeasurable (fun p : Ω × ℝ => Y p.1) (μ.prod volume) :=
        hX.aestronglyMeasurable.comp_fst
      have h2 : AEStronglyMeasurable (fun p : Ω × ℝ => p.2) (μ.prod volume) :=
        measurable_snd.aestronglyMeasurable
      exact (hψ.comp_aestronglyMeasurable h2).mul ((h1.sub h2).sup aestronglyMeasurable_const)
    · obtain ⟨ω, K⟩ := p
      simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, one_mul, abs_mul]
      have hm0 : 0 ≤ max (Y ω - K) 0 := le_max_right _ _
      have hm : max (Y ω - K) 0 ≤ |Y ω| + |K| :=
        max_le (by linarith [le_abs_self (Y ω), neg_abs_le K]) (by positivity)
      rw [abs_of_nonneg hm0]
      nlinarith [abs_nonneg (ψ K)]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun K => ?_)
  simp only [callSurface]
  exact integral_const_mul (ψ K) _

end Fubini

section TestFunction

/-- **The test-function factory (Carr–Madan + double primitive).** For a smooth compactly
supported strike density `ψ`, the double primitive `f_ψ(x) = ∫_L^x ∫_L^y ψ` (from a level `L`
left of `supp ψ`) is a legitimate test function of the landed weak forward equation —
`f_ψ'' = ψ`, `C²`, bounded `f_ψ'`, `ψ`, `f_ψ''' = ψ'` — *and* it is the payoff of the static
call book with strike density `ψ`: `f_ψ S = ∫ K, ψ K · (S − K)⁺ dK` for every `S`
(`span_of_vanish_left`, i.e. `MathFin.carrMadan_spanning`). Note `f_ψ` itself is unbounded
(affine right of `supp ψ`); the weak equation needs no bound on `f`. -/
theorem call_spanning_compactSupport {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    ∃ f f' f''' : ℝ → ℝ, (∀ x, HasDerivAt f (f' x) x) ∧ (∀ x, HasDerivAt f' (ψ x) x) ∧
      ContDiff ℝ 2 f ∧ (∀ x, HasDerivAt ψ (f''' x) x) ∧
      (∃ C1, ∀ x, |f' x| ≤ C1) ∧ (∃ C2, ∀ x, |ψ x| ≤ C2) ∧ (∃ C3, ∀ x, |f''' x| ≤ C3) ∧
      ∀ S, f S = ∫ K, ψ K * max (S - K) 0 := by
  obtain ⟨L, hL⟩ := exists_le_notMem_tsupport hψc
  have hψcont : Continuous ψ := hψ.continuous
  set f' : ℝ → ℝ := fun x => ∫ K in L..x, ψ K with hf'def
  have hf' : ∀ x, HasDerivAt f' (ψ x) x := fun x =>
    (hψcont.integral_hasStrictDerivAt L x).hasDerivAt
  have hf'cont : Continuous f' :=
    continuous_iff_continuousAt.2 fun x => (hf' x).continuousAt
  set f : ℝ → ℝ := fun x => ∫ K in L..x, f' K with hfdef
  have hf : ∀ x, HasDerivAt f (f' x) x := fun x =>
    (hf'cont.integral_hasStrictDerivAt L x).hasDerivAt
  have hderivf : deriv f = f' := funext fun x => (hf x).deriv
  have hderivf' : deriv f' = ψ := funext fun x => (hf' x).deriv
  have h2 : ContDiff ℝ 2 f := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hf x).differentiableAt, by simp, ?_⟩
    rw [hderivf, contDiff_one_iff_deriv, hderivf']
    exact ⟨fun x => (hf' x).differentiableAt, hψcont⟩
  have hψd : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x =>
    ((hψ.differentiable (by simp)) x).hasDerivAt
  obtain ⟨C2, hC2⟩ := hψcont.bounded_above_of_compact_support hψc
  obtain ⟨C3, hC3⟩ := (hψ.continuous_deriv (by simp)).bounded_above_of_compact_support
    hψc.deriv
  refine ⟨f, f', deriv ψ, hf, hf', h2, hψd, ⟨∫ K, |ψ K|, fun x => ?_⟩, ⟨C2, hC2⟩, ⟨C3, hC3⟩,
    fun S => ?_⟩
  · have hψi : Integrable ψ := hψcont.integrable_of_hasCompactSupport hψc
    calc |f' x| = ‖∫ K in L..x, ψ K‖ := rfl
      _ ≤ ∫ K in Ι L x, ‖ψ K‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ K, ‖ψ K‖ :=
          setIntegral_le_integral hψi.norm (Eventually.of_forall fun _ => norm_nonneg _)
      _ = ∫ K, |ψ K| := rfl
  · exact span_of_vanish_left hψcont (fun K hK => image_eq_zero_of_notMem_tsupport (hL K hK))
      hf hf' (by simp [hfdef]) (by simp [hf'def]) S

end TestFunction

section BreedenLitzenberger

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Breeden–Litzenberger, weak form (any law).** For any integrable time-`s` marginal and
any smooth compactly supported `ψ`,

  `∫ ψ''(K) · C(s, K) dK = 𝔼[ψ(X_{s⁺})]`,

i.e. `∂²_K C(s, ·) = law(X_{s⁺})` *as distributions* — the general-law Breeden–Litzenberger
identity, with no density hypothesis. (Contrast `MathFin.breedenLitzenberger`, which is the
Black–Scholes closed-form identity only.) Proof: `ψ` is its own Carr–Madan spanning
(`span_of_vanish_left` with `φ = ψ''`), then Fubini (`integral_payoff_eq_integral_call`). -/
theorem breedenLitzenberger_weak [IsFiniteMeasure μ] {X : ℝ≥0 → Ω → ℝ} {s : ℝ}
    (hX : Integrable (X (Real.toNNReal s)) μ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ K, deriv (deriv ψ) K * callSurface μ X s K = ∫ ω, ψ (X (Real.toNNReal s) ω) ∂μ := by
  obtain ⟨L, hL⟩ := exists_le_notMem_tsupport hψc
  have hψ1 : ContDiff ℝ ∞ (deriv ψ) := contDiff_infty_iff_deriv.mp hψ |>.2
  have hψ2 : ContDiff ℝ ∞ (deriv (deriv ψ)) := contDiff_infty_iff_deriv.mp hψ1 |>.2
  have hL1 : ∀ K ≤ L, K ∉ tsupport (deriv ψ) := fun K hK h => hL K hK (tsupport_deriv_subset h)
  have hL2 : ∀ K ≤ L, K ∉ tsupport (deriv (deriv ψ)) := fun K hK h =>
    hL1 K hK (tsupport_deriv_subset h)
  rw [← integral_payoff_eq_integral_call hX hψ2.continuous hψc.deriv.deriv]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  exact (span_of_vanish_left hψ2.continuous
    (fun K hK => image_eq_zero_of_notMem_tsupport (hL2 K hK))
    (fun x => ((hψ.differentiable (by simp)) x).hasDerivAt)
    (fun x => ((hψ1.differentiable (by simp)) x).hasDerivAt)
    (image_eq_zero_of_notMem_tsupport (hL L le_rfl))
    (image_eq_zero_of_notMem_tsupport (hL1 L le_rfl)) _).symm

end BreedenLitzenberger

section Dupire

open MathFin.GyongyMimicry

/-- **The weak forward (Fokker–Planck) equation at zero rates** — in its
honest weak form: `GyongyMimicry.marginal_flow_weak_equation_fn_constructed`,
specialized to the driftless constructed process `X = c + M` (`β := 0`, `M` the Itô integral
of the bounded adapted `δ`), with the drift term erased. For every test function `f` of the
landed class (`C²`, bounded `f', f'', f'''`),

  `d/dt 𝔼[f(X_{t⁺})] = ½ · 𝔼[f''(X_{t⁺}) · b̂²(t, X_{t⁺})]`  on `(0, ↑T)`,

where `b̂²(t, ·)` is any Borel representation (`hbfn`) of the Gyöngy coefficient
`𝔼[δ_t² | X_t]`. The drift coefficient `𝔼[β_t | X_t] = 𝔼[0 | X_t]` is literally `0`
(`condExp_zero`), and `∫β = 0` (`AdaptedDrift.driftPath` of `0`), so the β-side
hypotheses of the general form are discharged here, not carried. -/
theorem forward_eq_weak_zeroRate
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + M t ω)
    {bfn : ℝ → ℝ → ℝ}
    (hbfn : ∀ s, Measurable (bfn s) ∧ ∀ ω, diffCoeffSq μ (reindexed X) (reindexed δ) s ω
      = bfn s (X (Real.toNNReal s) ω))
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (h2 : ContDiff ℝ 2 f)
    {f''' : ℝ → ℝ} (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C1 C2 C3 : ℝ} (hg1 : ∀ x, |f' x| ≤ C1) (hg2 : ∀ x, |f'' x| ≤ C2)
    (hg3 : ∀ x, |f''' x| ≤ C3)
    (t : ℝ) (ht : 0 < t) (htT : Real.toNNReal t < T) :
    HasDerivAt (fun s : ℝ => ∫ ω, f (X (Real.toNNReal s) ω) ∂μ)
      (1 / 2 * ∫ ω, f'' (X (Real.toNNReal t) ω) * bfn t (X (Real.toNNReal t) ω) ∂μ) t := by
  -- the zero drift, in the constructed process's `ℝ≥0`-indexed form
  set β0 : ℝ≥0 → Ω → ℝ := fun _ _ => 0 with hβ0
  have hXrel0 : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + AdaptedDrift.driftPath β0 t ω + M t ω := by
    intro t; rw [hXrel t]; funext ω; simp [hβ0, AdaptedDrift.driftPath]
  -- its Gyöngy coefficient `𝔼[0 | X_s]` is represented by the zero function, pointwise
  have hafn : ∀ s : ℝ, Measurable (fun _ : ℝ => (0 : ℝ)) ∧ ∀ ω,
      driftCoeff μ (reindexed X) (reindexed β0) s ω
        = (fun _ : ℝ => (0 : ℝ)) (X (Real.toNNReal s) ω) :=
    fun s => ⟨measurable_const, fun ω => by
      show μ[(0 : Ω → ℝ) | sigmaGen (reindexed X) s] ω = 0
      rw [condExp_zero]; rfl⟩
  have key := marginal_flow_weak_equation_fn_constructed (β := β0) (Db := 0)
    (afn := fun _ _ => 0)
    hB hBmeas (fun _ => stronglyMeasurable_const) (fun _ => continuous_const) (by simp [hβ0])
    hδadap hδcont hδbdd hMadap hMeq c hXcont hXrel0 hafn hbfn hf hf' h2 hf'' hg1 hg2 hg3
    t ht htT
  simpa using key

/-- **Dupire's formula, distributional form (Bagaria ch. 9 Thm 9.5 ∘ Thm 9.7, zero rates) —
the headline of the distributional half.** For the driftless constructed Itô process `X = c + ∫δ dB` (bounded
adapted `δ`) and every smooth compactly supported strike density `ψ`, the `ψ`-pairing of the
*defined* call surface `C(s, K) = 𝔼[(X_{s⁺} − K)⁺]` is differentiable in maturity on
`(0, ↑T)`, with

  `d/dT ∫ ψ(K) C(T, K) dK = ½ · 𝔼[ψ(X_T) · b̂²(T, X_T)]`,

`b̂²(T, ·)` the Gyöngy coefficient `𝔼[δ_T² | X_T = ·]`. Together with
`breedenLitzenberger_weak` (`∫ ψ'' C = 𝔼 ψ(X_T)`, i.e. `∂²_K C = law(X_T)`) this is exactly
`∂_T C = ½ · b̂²(T, ·) · ∂²_K C` **as an identity of distributions in `K`** — with no density,
no Tanaka formula and no regularity hypothesis on `C`: the call payoff `(x − K)⁺` (not `C²`) is
never tested directly; it is smeared against `ψ` first (`call_spanning_compactSupport`), and
the smeared payoff `f_ψ` is a legitimate test function of `forward_eq_weak_zeroRate`. The
pointwise ratio `σ²_loc = 2∂_T C / (K² ∂²_K C)` at a single strike is proved in the pointwise
half of this file (`dupire_pointwise`), under carried regularity hypotheses on the call
surface. -/
theorem dupire_weak
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + M t ω)
    {bfn : ℝ → ℝ → ℝ}
    (hbfn : ∀ s, Measurable (bfn s) ∧ ∀ ω, diffCoeffSq μ (reindexed X) (reindexed δ) s ω
      = bfn s (X (Real.toNNReal s) ω))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (t : ℝ) (ht : 0 < t) (htT : Real.toNNReal t < T) :
    HasDerivAt (fun s : ℝ => ∫ K, ψ K * callSurface μ X s K)
      ((1 / 2) * ∫ ω, ψ (X (Real.toNNReal t) ω) * bfn t (X (Real.toNNReal t) ω) ∂μ) t := by
  obtain ⟨f, f', f''', hf, hf', h2, hf'', ⟨C1, hg1⟩, ⟨C2, hg2⟩, ⟨C3, hg3⟩, hspan⟩ :=
    call_spanning_compactSupport hψ hψc
  -- every marginal is integrable: `X_s = c + M_s`, `M_s` an `L²(μ)` class
  have hXint : ∀ s : ℝ≥0, Integrable (X s) μ := fun s => by
    rw [hXrel s]
    exact (integrable_const c).add
      (((Lp.memLp (itoProcessCLM hB T s hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd))).integrable one_le_two).congr (hMeq s).symm)
  have hfun : (fun s : ℝ => ∫ K, ψ K * callSurface μ X s K)
      = fun s : ℝ => ∫ ω, f (X (Real.toNNReal s) ω) ∂μ := by
    funext s
    rw [← integral_payoff_eq_integral_call (hXint _) hψ.continuous hψc]
    exact integral_congr_ae (Eventually.of_forall fun ω => (hspan _).symm)
  rw [hfun]
  exact forward_eq_weak_zeroRate hB hBmeas hδadap hδcont hδbdd hMadap hMeq c hXcont hXrel
    hbfn hf hf' h2 hf'' hg1 hg2 hg3 t ht htT

end Dupire

end MathFin.Dupire


/-!
# Dupire's formula, pointwise form

The pointwise ratio `σ²_loc(T, K) = 2·∂_T C / (K²·∂²_K C)` at a single strike, under explicit
carried regularity hypotheses on the *defined* `callSurface`, derived on top of the
distributional half above.

## Hypotheses (carried, never derived)

On a strike window `Ioo a b` and a time window `Ioo (t − ε) (t + ε)`:

* `hCK`, `hCKK`, `hCKKc` — `K ↦ C(t, K)` is twice differentiable on the window with `C_KK`
  continuous there;
* `hCt`, `hCtc` — `s ↦ C(s, K)` is differentiable on the time window with `(s, K) ↦ C_T(s, K)`
  jointly continuous on the rectangle.

Each derivative (`CK`, `CKK`, `Ct`) is pinned to the defined `callSurface` by its own
`HasDerivAt` hypothesis. **No hypothesis relates `Ct` to `CKK`**: the relation
`2·C_T = b̂²·C_KK` is the conclusion, derived from `dupire_weak`, not hypothesized.
Non-vacuity: Bachelier (`δ ≡ δ₀ > 0`, `X = c + δ₀B`) satisfies all of them, with
`C_T = ½δ₀²φ_t(K)`, `C_KK = φ_t(K) > 0`, `b̂² ≡ δ₀²` (no Lean witness here).

## Proved

* `abs_call_payoff_sub_le`, `tendsto_call_spread` — imported from
  `MathFin.BlackScholes.CallSpreadDigital` (they live there; this module consumes them).
* `strikeDeriv_callSurface_eq_neg_tail` — converse Breeden–Litzenberger, first order:
  `∂_K C(s, K) = −P(X_s > K)` wherever the strike derivative exists.
* `strikeDeriv2_callSurface_nonneg` — `C_KK ≥ 0` on the window.
* `law_Ioc_eq_ofReal_integral`, `law_restrict_eq_withDensity` — on every `Ioc p q` inside the
  window, `law(X_t)` *is* `C_KK · Leb` (FTC + `Measure.ext_of_Ioc`).
* `continuous_callSurface` — `K ↦ C(s, K)` is 1-Lipschitz.
* `hasDerivAt_integral_mul_callSurface` — `d/ds ∫ψ C(s, ·) = ∫ψ C_T(t, ·)` (dominated
  differentiation under the integral).
* `dupire_ae_window`, **`dupire_ae`** — a.e. on `{X_t ∈ window}`,
  `b̂²(t, X_t) = 2·C_T(t, X_t) / C_KK(X_t)`: the Dupire ratio is a version of `𝔼[δ_t² | X_t]`.
* **`dupire_pointwise_coeff`**, **`dupire_pointwise`** (Thm 9.5 proper) — for any version of
  `b̂²(t, ·)` continuous on the window, the identity holds at *every* strike with `C_KK > 0`.
* **`dupire_localVol`** — Def 9.4's Markov case `δ_s = v(s, X_s)` (carried as `hδloc`;
  SDE existence is not proved): `v(t, K)² = 2·C_T / C_KK`.

Rather than push the continuous version through `law(X_t)` via `eqOn_open_of_ae_eq` (which
would need a measurable-set side condition), `dupire_pointwise_coeff` argues
by contradiction on a small strike interval, where `law(X_t)` has positive mass
`∫ C_KK > 0`.
-/

namespace MathFin.Dupire


section StrikeDerivatives

open Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : ℝ≥0 → Ω → ℝ} {s : ℝ}

/-- **Converse Breeden–Litzenberger, first order (any law).** Wherever the defined call surface
has a strike derivative `d` at `K`, it is minus the digital: `d = −P(X_s > K)`. The right
difference quotients of `C(s, ·)` tend to `d` (`HasDerivAt.tendsto_slope_zero_right`) and to
`−μ {X_s > K}` (`tendsto_call_spread`). -/
theorem strikeDeriv_callSurface_eq_neg_tail (hXm : Measurable (X (Real.toNNReal s)))
    (hX : Integrable (X (Real.toNNReal s)) μ) {K d : ℝ}
    (hd : HasDerivAt (callSurface μ X s) d K) :
    d = -μ.real {ω | K < X (Real.toNNReal s) ω} := by
  refine tendsto_nhds_unique hd.tendsto_slope_zero_right
    ((tendsto_call_spread hXm hX K).neg.congr' (Eventually.of_forall fun h => ?_))
  simp only [callSurface, smul_eq_mul]
  ring

/-- **`C_KK ≥ 0` on the window.** `C_K = −P(X_s > ·)` is monotone there
(`strikeDeriv_callSurface_eq_neg_tail`), so its right slopes are nonnegative. -/
theorem strikeDeriv2_callSurface_nonneg (hXm : Measurable (X (Real.toNNReal s)))
    (hX : Integrable (X (Real.toNNReal s)) μ) {a b : ℝ} {CK CKK : ℝ → ℝ}
    (hCK : ∀ K ∈ Ioo a b, HasDerivAt (callSurface μ X s) (CK K) K)
    (hCKK : ∀ K ∈ Ioo a b, HasDerivAt CK (CKK K) K) {K : ℝ} (hK : K ∈ Ioo a b) :
    0 ≤ CKK K := by
  refine ge_of_tendsto (hCKK K hK).tendsto_slope_zero_right ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hK.2)] with h hh
  have hKh : K + h ∈ Ioo a b := ⟨by linarith [hK.1, hh.1], by linarith [hh.2]⟩
  rw [strikeDeriv_callSurface_eq_neg_tail hXm hX (hCK _ hKh),
    strikeDeriv_callSurface_eq_neg_tail hXm hX (hCK _ hK), smul_eq_mul]
  refine mul_nonneg (inv_nonneg.2 hh.1.le) ?_
  have : μ.real {ω | K + h < X (Real.toNNReal s) ω} ≤ μ.real {ω | K < X (Real.toNNReal s) ω} :=
    measureReal_mono fun ω (hω : K + h < _) => show K < _ by linarith [hh.1]
  linarith

end StrikeDerivatives

end MathFin.Dupire

namespace MathFin.Dupire

section LawDensity

open Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : ℝ≥0 → Ω → ℝ} {s : ℝ}

/-- **The law of `X_s` on a strike interval is the integral of `C_KK`.** For `a < c ≤ d < b`,
`P(c < X_s ≤ d) = C_K(d) − C_K(c) = ∫_c^d C_KK` (`strikeDeriv_callSurface_eq_neg_tail` at both
ends, then FTC). -/
theorem law_Ioc_eq_ofReal_integral (hXm : Measurable (X (Real.toNNReal s)))
    (hX : Integrable (X (Real.toNNReal s)) μ) {a b : ℝ} {CK CKK : ℝ → ℝ}
    (hCK : ∀ K ∈ Ioo a b, HasDerivAt (callSurface μ X s) (CK K) K)
    (hCKK : ∀ K ∈ Ioo a b, HasDerivAt CK (CKK K) K) (hCKKc : ContinuousOn CKK (Ioo a b))
    {c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    μ.map (X (Real.toNNReal s)) (Ioc c d) = ENNReal.ofReal (∫ K in c..d, CKK K) := by
  set ν := μ.map (X (Real.toNNReal s))
  have hsub : uIcc c d ⊆ Ioo a b := by
    rw [uIcc_of_le hcd]; exact Icc_subset_Ioo hac hdb
  have hFTC : ∫ K in c..d, CKK K = CK d - CK c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun K hK => hCKK K (hsub hK))
      ((hCKKc.mono hsub).intervalIntegrable)
  have htail (k : ℝ) : ν.real (Ioi k) = μ.real {ω | k < X (Real.toNNReal s) ω} :=
    map_measureReal_apply hXm measurableSet_Ioi
  have hreal : ν.real (Ioc c d) = CK d - CK c := by
    rw [← Ioi_sdiff_Ioi, measureReal_sdiff (Ioi_subset_Ioi hcd) measurableSet_Ioi, htail, htail,
      strikeDeriv_callSurface_eq_neg_tail hXm hX (hCK c ⟨hac, by linarith⟩),
      strikeDeriv_callSurface_eq_neg_tail hXm hX (hCK d ⟨by linarith, hdb⟩)]
    ring
  rw [hFTC, ← hreal, ofReal_measureReal]

/-- **Converse Breeden–Litzenberger, second order: `law(X_s) = C_KK · Leb` on the window.** On
every `Ioc p q` with `a < p`, `q < b`, the restricted law of `X_s` is Lebesgue measure with
density `C_KK` (`Measure.ext_of_Ioc` against `law_Ioc_eq_ofReal_integral`; `C_KK ≥ 0` by
`strikeDeriv2_callSurface_nonneg`). No measurability of `CKK` off the window is needed. -/
theorem law_restrict_eq_withDensity (hXm : Measurable (X (Real.toNNReal s)))
    (hX : Integrable (X (Real.toNNReal s)) μ) {a b : ℝ} {CK CKK : ℝ → ℝ}
    (hCK : ∀ K ∈ Ioo a b, HasDerivAt (callSurface μ X s) (CK K) K)
    (hCKK : ∀ K ∈ Ioo a b, HasDerivAt CK (CKK K) K) (hCKKc : ContinuousOn CKK (Ioo a b))
    {p q : ℝ} (hap : a < p) (hqb : q < b) :
    (μ.map (X (Real.toNNReal s))).restrict (Ioc p q)
      = (volume.restrict (Ioc p q)).withDensity (fun K => ENNReal.ofReal (CKK K)) := by
  refine Measure.ext_of_Ioc _ _ fun c d hcd => ?_
  rw [Measure.restrict_apply measurableSet_Ioc, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc]
  rcases le_or_gt (min d q) (max c p) with h | h
  · rw [Ioc_eq_empty (not_lt.2 h)]; simp
  have hac : a < max c p := lt_of_lt_of_le hap (le_max_right _ _)
  have hdb : min d q < b := lt_of_le_of_lt (min_le_right _ _) hqb
  have hsub : Icc (max c p) (min d q) ⊆ Ioo a b := Icc_subset_Ioo hac hdb
  rw [law_Ioc_eq_ofReal_integral hXm hX hCK hCKK hCKKc hac h.le hdb,
    intervalIntegral.integral_of_le h.le, ofReal_integral_eq_lintegral_ofReal]
  · exact ((hCKKc.mono hsub).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  · exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun K hK =>
      strikeDeriv2_callSurface_nonneg hXm hX hCK hCKK (hsub (Ioc_subset_Icc_self hK)))

end LawDensity

section TimeDerivative

open Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℝ≥0 → Ω → ℝ}

/-- `K ↦ C(s, K)` is `1`-Lipschitz (the payoff is, `abs_call_payoff_sub_le`), hence continuous. -/
theorem continuous_callSurface {s : ℝ} (hX : Integrable (X (Real.toNNReal s)) μ) :
    Continuous (callSurface μ X s) := by
  have hcall (k : ℝ) : Integrable (fun ω => max (X (Real.toNNReal s) ω - k) 0) μ :=
    (hX.sub (integrable_const k)).pos_part
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun K₁ K₂ => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, callSurface, callSurface, ← integral_sub (hcall K₁) (hcall K₂)]
  have h := norm_integral_le_of_norm_le_const (μ := μ) (C := |K₁ - K₂|)
    (f := fun ω => max (X (Real.toNNReal s) ω - K₁) 0 - max (X (Real.toNNReal s) ω - K₂) 0)
    (ae_of_all _ fun ω => abs_call_payoff_sub_le (X (Real.toNNReal s) ω) K₁ K₂)
  simpa using h

/-- **Maturity derivative under the strike integral.** If `s ↦ C(s, K)` has derivative
`C_T(s, K)` on the rectangle `Ioo (t − ε) (t + ε) × Ioo a b`, jointly continuous there, and
every time-`s` marginal integrable (`hXint : ∀ s : ℝ≥0, Integrable (X s) μ` — used for
`continuous_callSurface` at each `s` and for the integrand's measurability and integrability),
then for a continuous `ψ`
compactly supported in `Ioo a b`,
`d/ds ∫ ψ(K) C(s, K) dK = ∫ ψ(K) C_T(t, K) dK` at `s = t`
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`; the bound is `sup |C_T| · |ψ|` on a compact
sub-rectangle). -/
theorem hasDerivAt_integral_mul_callSurface (hXint : ∀ s : ℝ≥0, Integrable (X s) μ)
    {t a b ε : ℝ} (hε : 0 < ε) {Ct : ℝ → ℝ → ℝ}
    (hCt : ∀ s ∈ Ioo (t - ε) (t + ε), ∀ K ∈ Ioo a b,
      HasDerivAt (fun s' => callSurface μ X s' K) (Ct s K) s)
    (hCtc : ContinuousOn (Function.uncurry Ct) (Ioo (t - ε) (t + ε) ×ˢ Ioo a b))
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ Ioo a b) :
    HasDerivAt (fun s => ∫ K, ψ K * callSurface μ X s K) (∫ K, ψ K * Ct t K) t := by
  have hIcc : Icc (t - ε / 2) (t + ε / 2) ⊆ Ioo (t - ε) (t + ε) :=
    Icc_subset_Ioo (by linarith) (by linarith)
  obtain ⟨Mb, hMb⟩ := (isCompact_Icc.prod hψc).exists_bound_of_continuousOn
    (hCtc.mono (prod_mono hIcc hψU))
  have hψ0 : ∀ K ∉ tsupport ψ, ψ K = 0 := fun K hK => image_eq_zero_of_notMem_tsupport hK
  have hCtK : ContinuousOn (Ct t) (Ioo a b) :=
    hCtc.comp (continuous_const.prodMk continuous_id).continuousOn
      fun K hK => ⟨⟨by linarith, by linarith⟩, hK⟩
  have hF' : Continuous fun K => ψ K * Ct t K :=
    (hψ.continuousOn.mul hCtK).continuous_of_tsupport_subset isOpen_Ioo
      ((tsupport_mul_subset_left).trans hψU)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s K => ψ K * callSurface μ X s K) (F' := fun s K => ψ K * Ct s K)
    (bound := fun K => Mb * |ψ K|) (Ioo_mem_nhds (by linarith : t - ε / 2 < t)
      (by linarith : t < t + ε / 2))
    (Eventually.of_forall fun s =>
      (hψ.mul (continuous_callSurface (hXint _))).aestronglyMeasurable)
    ((hψ.mul (continuous_callSurface (hXint _))).integrable_of_hasCompactSupport hψc.mul_right)
    hF'.aestronglyMeasurable (ae_of_all _ fun K s hs => ?_)
    ((hψ.integrable_of_hasCompactSupport hψc).abs.const_mul Mb)
    (ae_of_all _ fun K s hs => ?_)).2
  · by_cases hK : K ∈ tsupport ψ
    · have := hMb (s, K) ⟨Ioo_subset_Icc_self hs, hK⟩
      rw [norm_mul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    · simp [hψ0 K hK]
  · by_cases hK : K ∈ Ioo a b
    · exact (hCt s (hIcc (Ioo_subset_Icc_self hs)) K hK).const_mul (ψ K)
    · simp only [hψ0 K (fun h => hK (hψU h)), zero_mul]
      exact hasDerivAt_const _ _

end TimeDerivative

end MathFin.Dupire

namespace MathFin.Dupire

section Pointwise

open Set MathFin.GyongyMimicry
open scoped ENNReal

/-- **On a sub-window (the analytic core of `dupire_ae`).** For `a < p ≤ q < b`, a.e. on
`{X_t ∈ Ioo p q}` the Borel version `b̂²(t, ·) = bfn t` of the Gyöngy coefficient equals the
Dupire ratio `2·C_T(t, ·)/C_KK` at `X_t`. Proof (steps a–d):
(a) `law(X_t) = C_KK · Leb` on `Ioc p q` (`law_restrict_eq_withDensity`);
(b) for every test `ψ` supported in `Ioo p q`, `∫ψ C_T(t, ·) = ½𝔼[ψ(X_t) b̂²(t, X_t)]` by
`HasDerivAt.unique` between `hasDerivAt_integral_mul_callSurface` and `dupire_weak`;
(c) hence `2C_T − C_KK·b̂² = 0` Lebesgue-a.e. on `Ioo p q`
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`);
(d) transfer to `law(X_t)` (`withDensity_absolutelyContinuous`), which charges only
`{C_KK > 0}` (`ae_withDensity_iff`), and divide. -/
theorem dupire_ae_window
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + M t ω)
    {bfn : ℝ → ℝ → ℝ}
    (hbfn : ∀ s, Measurable (bfn s) ∧ ∀ ω, diffCoeffSq μ (reindexed X) (reindexed δ) s ω
      = bfn s (X (Real.toNNReal s) ω))
    (t : ℝ) (ht : 0 < t) (htT : Real.toNNReal t < T)
    {a b ε : ℝ} (hε : 0 < ε) {CK CKK : ℝ → ℝ} {Ct : ℝ → ℝ → ℝ}
    (hCK : ∀ K ∈ Ioo a b, HasDerivAt (callSurface μ X t) (CK K) K)
    (hCKK : ∀ K ∈ Ioo a b, HasDerivAt CK (CKK K) K)
    (hCKKc : ContinuousOn CKK (Ioo a b))
    (hCt : ∀ s ∈ Ioo (t - ε) (t + ε), ∀ K ∈ Ioo a b,
      HasDerivAt (fun s' => callSurface μ X s' K) (Ct s K) s)
    (hCtc : ContinuousOn (Function.uncurry Ct) (Ioo (t - ε) (t + ε) ×ˢ Ioo a b))
    {p q : ℝ} (hap : a < p) (hpq : p ≤ q) (hqb : q < b) :
    ∀ᵐ ω ∂μ, X (Real.toNNReal t) ω ∈ Ioo p q →
      bfn t (X (Real.toNNReal t) ω)
        = 2 * Ct t (X (Real.toNNReal t) ω) / CKK (X (Real.toNNReal t) ω) := by
  have hXint : ∀ s : ℝ≥0, Integrable (X s) μ := fun s => by
    rw [hXrel s]
    exact (integrable_const c).add
      (((Lp.memLp (itoProcessCLM hB T s hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd))).integrable one_le_two).congr (hMeq s).symm)
  have hXm : Measurable (X (Real.toNNReal t)) := by
    rw [hXrel]
    exact ((hMadap _).measurable.mono ((natFiltration hBmeas).le _) le_rfl).const_add c
  set Xt := X (Real.toNNReal t) with hXt
  set ν := μ.map Xt with hν
  set bt := bfn t with hbdef
  have hbm : Measurable bt := (hbfn t).1
  -- the density `C_KK`, made globally continuous (hence measurable) by clamping to `[p, q]`
  have hIccU : Icc p q ⊆ Ioo a b := Icc_subset_Ioo hap hqb
  set ρ : ℝ → ℝ≥0 := fun K => (CKK (projIcc p q hpq K)).toNNReal with hρ
  have hρm : Measurable ρ := (continuous_real_toNNReal.comp
    (hCKKc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun K => hIccU (projIcc p q hpq K).2)).measurable
  have hρeq : ∀ K ∈ Icc p q, (ρ K : ℝ) = CKK K := fun K hK => by
    simp only [hρ, projIcc_of_mem hpq hK]
    exact Real.coe_toNNReal _ (strikeDeriv2_callSurface_nonneg hXm (hXint _) hCK hCKK (hIccU hK))
  have hlaw : ν.restrict (Ioc p q)
      = (volume.restrict (Ioc p q)).withDensity (fun K => (ρ K : ℝ≥0∞)) := by
    rw [hν, law_restrict_eq_withDensity hXm (hXint _) hCK hCKK hCKKc hap hqb]
    refine withDensity_congr_ae ((ae_restrict_iff' measurableSet_Ioc).2
      (ae_of_all _ fun K hK => ?_))
    show ENNReal.ofReal (CKK K) = (ρ K : ℝ≥0∞)
    rw [← ENNReal.ofReal_coe_nnreal, hρeq K (Ioc_subset_Icc_self hK)]
  -- `b̂²(t, ·)` is `law(X_t)`-integrable (it represents a conditional expectation)
  have hbint : Integrable bt ν := by
    refine (integrable_map_measure hbm.aestronglyMeasurable hXm.aemeasurable).2 ?_
    have : bt ∘ Xt = diffCoeffSq μ (reindexed X) (reindexed δ) t :=
      funext fun ω => ((hbfn t).2 ω).symm
    rw [this]; exact integrable_condExp
  have hρb : Integrable (fun K => (ρ K : ℝ) * bt K) (volume.restrict (Ioc p q)) := by
    have h := (integrable_withDensity_iff_integrable_smul hρm).1
      (by rw [← hlaw]; exact hbint.restrict)
    simpa [NNReal.smul_def, smul_eq_mul] using h
  have hCtK : ContinuousOn (Ct t) (Icc p q) :=
    hCtc.comp (continuous_const.prodMk continuous_id).continuousOn
      fun K hK => ⟨⟨by linarith, by linarith⟩, hIccU hK⟩
  have hCtint : Integrable (Ct t) (volume.restrict (Ioc p q)) :=
    (hCtK.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  set f : ℝ → ℝ := fun K => 2 * Ct t K - (ρ K : ℝ) * bt K with hf
  have hfint : Integrable f (volume.restrict (Ioc p q)) := (hCtint.const_mul 2).sub hρb
  -- (c) localization: `f` vanishes Lebesgue-a.e. on `Ioo p q`
  have h0 : ∀ᵐ K ∂(volume.restrict (Ioc p q)), K ∈ Ioo p q → f K = 0 := by
    refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      hfint.integrableOn.locallyIntegrableOn fun ψ hψ hψc hψU => ?_
    have hψ0 : ∀ K ∉ Ioc p q, ψ K = 0 := fun K hK =>
      image_eq_zero_of_notMem_tsupport fun h => hK (Ioo_subset_Ioc_self (hψU h))
    obtain ⟨Cψ, hCψ⟩ := hψ.continuous.bounded_above_of_compact_support hψc
    have hψm : AEStronglyMeasurable ψ (volume.restrict (Ioc p q)) :=
      hψ.continuous.aestronglyMeasurable
    have hψb : ∀ᵐ K ∂(volume.restrict (Ioc p q)), ‖ψ K‖ ≤ Cψ := ae_of_all _ hCψ
    -- (b) the maturity derivative of the `ψ`-pairing, computed two ways
    have huniq := (hasDerivAt_integral_mul_callSurface hXint hε hCt hCtc hψ.continuous hψc
      (hψU.trans (Ioo_subset_Ioo hap.le hqb.le))).unique
      (dupire_weak hB hBmeas hδadap hδcont hδbdd hMadap hMeq c hXcont hXrel hbfn hψ hψc
        t ht htT)
    -- (a) its right side, through `law(X_t) = C_KK · Leb` on the window
    have hlawint : ∫ ω, ψ (Xt ω) * bt (Xt ω) ∂μ = ∫ K in Ioc p q, ψ K * ((ρ K : ℝ) * bt K) := by
      rw [← integral_map (f := fun K => ψ K * bt K) hXm.aemeasurable
          (hψ.continuous.aestronglyMeasurable.mul hbm.aestronglyMeasurable),
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc p q)
          (fun K hK => by simp [hψ0 K hK]),
        hlaw, integral_withDensity_eq_integral_smul hρm]
      refine integral_congr_ae (ae_of_all _ fun K => ?_)
      simp only [NNReal.smul_def, smul_eq_mul]; ring
    have hleft : ∫ K, ψ K * Ct t K = ∫ K in Ioc p q, ψ K * Ct t K :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun K hK => by simp [hψ0 K hK]).symm
    have hsplit : ∫ K in Ioc p q, ψ K • f K
        = 2 * (∫ K in Ioc p q, ψ K * Ct t K) - ∫ K in Ioc p q, ψ K * ((ρ K : ℝ) * bt K) := by
      have hpt : (fun K => ψ K • f K)
          = fun K => 2 * (ψ K * Ct t K) - ψ K * ((ρ K : ℝ) * bt K) := by
        funext K; simp only [hf, smul_eq_mul]; ring
      rw [hpt, integral_sub ((hCtint.bdd_mul hψm hψb).const_mul 2) (hρb.bdd_mul hψm hψb),
        integral_const_mul]
    have huniq' : ∫ K, ψ K * Ct t K = 1 / 2 * ∫ ω, ψ (Xt ω) * bt (Xt ω) ∂μ := huniq
    rw [hsplit]; linarith [hleft, hlawint, huniq']
  -- (d) transfer to `law(X_t)` (`≪ Leb` on the window), which charges only `{C_KK > 0}`
  have h1 : ∀ᵐ K ∂(ν.restrict (Ioc p q)), K ∈ Ioo p q → f K = 0 := by
    rw [hlaw]; exact (withDensity_absolutelyContinuous _ _).ae_le h0
  have h2 : ∀ᵐ K ∂(ν.restrict (Ioc p q)), (ρ K : ℝ≥0∞) ≠ 0 := by
    rw [hlaw]; exact (ae_withDensity_iff hρm.coe_nnreal_ennreal).2 (ae_of_all _ fun _ h => h)
  have h3 : ∀ᵐ K ∂ν, K ∈ Ioc p q → K ∈ Ioo p q → bt K = 2 * Ct t K / CKK K := by
    refine (ae_restrict_iff' measurableSet_Ioc).1 ?_
    filter_upwards [h1, h2] with K hK1 hK2 hK
    have hρK := hρeq K (Ioo_subset_Icc_self hK)
    have hpos : CKK K ≠ 0 := by
      rw [← hρK]; exact_mod_cast ENNReal.coe_ne_zero.1 hK2
    rw [eq_div_iff hpos]
    have := hK1 hK
    simp only [hf, hρK] at this
    linarith
  filter_upwards [ae_of_ae_map hXm.aemeasurable h3] with ω hω hmem
  exact hω (Ioo_subset_Ioc_self hmem) hmem

end Pointwise

end MathFin.Dupire

namespace MathFin.Dupire

section Pointwise

open Set MathFin.GyongyMimicry

/-- **`dupire_ae`: the Dupire ratio is a version of `𝔼[δ_t² | X_t]` on the window**
(Bagaria ch. 9 Thm 9.5 ∘ Thm 9.7, pointwise modulo a null set, zero rates). For the driftless
constructed Itô process and a call surface carrying the regularity hypotheses `hCK`, `hCKK`,
`hCKKc`, `hCt`, `hCtc` on `Ioo a b` (each derivative pinned to the *defined* `callSurface` on its
own; none relates `Ct` to `CKK`),

  `𝔼[δ_t² | X_t](ω) = 2·C_T(t, X_t(ω)) / C_KK(X_t(ω))`  for a.e. `ω` with `X_t(ω) ∈ Ioo a b`.

With `σ²_loc(t, K) := b̂²(t, K)/K²` this is eq. 9.4 at `r = q = 0`. The conclusion is about the
conditional expectation `diffCoeffSq` itself, not a free `b̂²`: a Borel version is chosen
internally (Doob–Dynkin, `StronglyMeasurable.exists_eq_measurable_comp`), and the windows
`Ioo p q` (`p, q` rational) of `dupire_ae_window` exhaust `Ioo a b`. -/
theorem dupire_ae
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + M t ω)
    (t : ℝ) (ht : 0 < t) (htT : Real.toNNReal t < T)
    {a b ε : ℝ} (hε : 0 < ε) {CK CKK : ℝ → ℝ} {Ct : ℝ → ℝ → ℝ}
    (hCK : ∀ K ∈ Ioo a b, HasDerivAt (callSurface μ X t) (CK K) K)
    (hCKK : ∀ K ∈ Ioo a b, HasDerivAt CK (CKK K) K)
    (hCKKc : ContinuousOn CKK (Ioo a b))
    (hCt : ∀ s ∈ Ioo (t - ε) (t + ε), ∀ K ∈ Ioo a b,
      HasDerivAt (fun s' => callSurface μ X s' K) (Ct s K) s)
    (hCtc : ContinuousOn (Function.uncurry Ct) (Ioo (t - ε) (t + ε) ×ˢ Ioo a b)) :
    ∀ᵐ ω ∂μ, X (Real.toNNReal t) ω ∈ Ioo a b →
      diffCoeffSq μ (reindexed X) (reindexed δ) t ω
        = 2 * Ct t (X (Real.toNNReal t) ω) / CKK (X (Real.toNNReal t) ω) := by
  -- a Borel version `b̂²(s, ·)` of the Gyöngy coefficient at every time (Doob–Dynkin)
  have hex : ∀ s : ℝ, ∃ g : ℝ → ℝ, Measurable g ∧ ∀ ω,
      diffCoeffSq μ (reindexed X) (reindexed δ) s ω = g (X (Real.toNNReal s) ω) := fun s => by
    obtain ⟨g, hg, hgeq⟩ := (stronglyMeasurable_condExp (m := sigmaGen (reindexed X) s)
      (μ := μ) (f := fun ω => reindexed δ s ω * reindexed δ s ω)).exists_eq_measurable_comp
    exact ⟨g, hg.measurable, fun ω => congrFun hgeq ω⟩
  choose bfn hbfm hbfeq using hex
  have hwin : ∀ pq : ℚ × ℚ, ∀ᵐ ω ∂μ, (a < pq.1 ∧ (pq.1 : ℝ) ≤ pq.2 ∧ (pq.2 : ℝ) < b) →
      X (Real.toNNReal t) ω ∈ Ioo (pq.1 : ℝ) pq.2 →
      bfn t (X (Real.toNNReal t) ω)
        = 2 * Ct t (X (Real.toNNReal t) ω) / CKK (X (Real.toNNReal t) ω) := fun pq => by
    by_cases h : a < (pq.1 : ℝ) ∧ (pq.1 : ℝ) ≤ pq.2 ∧ (pq.2 : ℝ) < b
    · filter_upwards [dupire_ae_window hB hBmeas hδadap hδcont hδbdd hMadap hMeq c hXcont hXrel
        (fun s => ⟨hbfm s, hbfeq s⟩) t ht htT hε hCK hCKK hCKKc hCt hCtc h.1 h.2.1 h.2.2]
        with ω hω _ using hω
    · exact ae_of_all _ fun ω h' => absurd h' h
  filter_upwards [ae_all_iff.2 hwin] with ω hω hmem
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hmem.1
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hmem.2
  rw [hbfeq t ω]
  exact hω (p, q) ⟨hp1, (hp2.trans hq1).le, hq2⟩ ⟨hp2, hq1⟩

/-- **Continuous-version uniqueness, coefficient form.** If `v2` is a version of
`b̂²(t, ·) = 𝔼[δ_t² | X_t = ·]` on the window (`hv2rep`) that is continuous there (`hv2c`), then
at *every* strike of the window with `C_KK > 0`,

  `v2(K) = 2·C_T(t, K) / C_KK(K)`.

Proof by contradiction: if the two continuous sides differed at `K₀`, they would differ on a
small interval `(c, d]` around `K₀` where `C_KK > 0`; that interval has `law(X_t)`-mass
`∫_c^d C_KK > 0` (`law_Ioc_eq_ofReal_integral`), contradicting `dupire_ae` + `hv2rep`, which make
them agree a.e. on `{X_t ∈ window}`. -/
theorem dupire_pointwise_coeff
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + M t ω)
    (t : ℝ) (ht : 0 < t) (htT : Real.toNNReal t < T)
    {a b ε : ℝ} (hε : 0 < ε) {CK CKK : ℝ → ℝ} {Ct : ℝ → ℝ → ℝ}
    (hCK : ∀ K ∈ Ioo a b, HasDerivAt (callSurface μ X t) (CK K) K)
    (hCKK : ∀ K ∈ Ioo a b, HasDerivAt CK (CKK K) K)
    (hCKKc : ContinuousOn CKK (Ioo a b))
    (hCt : ∀ s ∈ Ioo (t - ε) (t + ε), ∀ K ∈ Ioo a b,
      HasDerivAt (fun s' => callSurface μ X s' K) (Ct s K) s)
    (hCtc : ContinuousOn (Function.uncurry Ct) (Ioo (t - ε) (t + ε) ×ˢ Ioo a b))
    {v2 : ℝ → ℝ} (hv2c : ContinuousOn v2 (Ioo a b))
    (hv2rep : ∀ᵐ ω ∂μ, X (Real.toNNReal t) ω ∈ Ioo a b →
      diffCoeffSq μ (reindexed X) (reindexed δ) t ω = v2 (X (Real.toNNReal t) ω)) :
    ∀ K ∈ Ioo a b, 0 < CKK K → v2 K = 2 * Ct t K / CKK K := by
  intro K₀ hK₀ hpos
  by_contra hne
  have hXint : Integrable (X (Real.toNNReal t)) μ := by
    rw [hXrel]
    exact (integrable_const c).add
      (((Lp.memLp (itoProcessCLM hB T _ hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd))).integrable one_le_two).congr (hMeq _).symm)
  have hXm : Measurable (X (Real.toNNReal t)) := by
    rw [hXrel]
    exact ((hMadap _).measurable.mono ((natFiltration hBmeas).le _) le_rfl).const_add c
  set Xt := X (Real.toNNReal t)
  have hae : ∀ᵐ ω ∂μ, Xt ω ∈ Ioo a b → v2 (Xt ω) = 2 * Ct t (Xt ω) / CKK (Xt ω) := by
    filter_upwards [dupire_ae hB hBmeas hδadap hδcont hδbdd hMadap hMeq c hXcont hXrel t ht htT
      hε hCK hCKK hCKKc hCt hCtc, hv2rep] with ω h1 h2 hmem
    rw [← h2 hmem, h1 hmem]
  -- the two sides differ, and `C_KK > 0`, on a whole neighbourhood of `K₀`
  have hU : Ioo a b ∈ 𝓝 K₀ := Ioo_mem_nhds hK₀.1 hK₀.2
  have hCtK : ContinuousAt (Ct t) K₀ :=
    (hCtc.continuousAt (prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) hU)).comp
      (continuous_const.prodMk continuous_id).continuousAt (x := K₀)
  have hR : ContinuousAt (fun K => v2 K - 2 * Ct t K / CKK K) K₀ :=
    (hv2c.continuousAt hU).sub
      ((continuousAt_const.mul hCtK).div (hCKKc.continuousAt hU) hpos.ne')
  have hev : ∀ᶠ K in 𝓝 K₀, (v2 K - 2 * Ct t K / CKK K ≠ 0 ∧ K ∈ Ioo a b) ∧ 0 < CKK K :=
    ((hR.eventually_ne (sub_ne_zero.2 hne)).and hU).and
      ((hCKKc.continuousAt hU).eventually (lt_mem_nhds hpos))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hIcc : ∀ K ∈ Icc (K₀ - r / 2) (K₀ + r / 2),
      (v2 K - 2 * Ct t K / CKK K ≠ 0 ∧ K ∈ Ioo a b) ∧ 0 < CKK K := fun K hK =>
    hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hK.1, hK.2])
  have hc := (hIcc (K₀ - r / 2) ⟨le_rfl, by linarith⟩).1.2
  have hd := (hIcc (K₀ + r / 2) ⟨by linarith, le_rfl⟩).1.2
  -- that interval carries positive `law(X_t)`-mass ...
  have hmass := law_Ioc_eq_ofReal_integral hXm hXint hCK hCKK hCKKc hc.1 (by linarith) hd.2
  have hint_pos : 0 < ∫ K in (K₀ - r / 2)..(K₀ + r / 2), CKK K :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hCKKc.mono (by rw [uIcc_of_le (by linarith)]; exact Icc_subset_Ioo hc.1 hd.2)).intervalIntegrable)
      (fun K hK => (hIcc K (Ioo_subset_Icc_self hK)).2) (by linarith)
  -- ... yet `X_t` a.s. avoids it
  have hnull : μ (Xt ⁻¹' Ioc (K₀ - r / 2) (K₀ + r / 2)) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hae] with ω h hmem
    have hP := hIcc (Xt ω) (Ioc_subset_Icc_self hmem)
    exact hP.1.1 (sub_eq_zero.2 (h hP.1.2))
  rw [Measure.map_apply hXm measurableSet_Ioc, hnull] at hmass
  exact (ENNReal.ofReal_pos.2 hint_pos).ne' hmass.symm

/-- **`dupire_pointwise` (Bagaria ch. 9 Thm 9.5 proper, zero rates).** If `σloc` is a local
volatility in the lognormal convention, i.e. `σloc(K)²·K²` is a version of `𝔼[δ_t² | X_t = K]`
on the window (`hσrep`), continuous there (`hσc`), and the window lies in `K > 0` (`ha`), then at
every strike of the window with `C_KK > 0`

  `σloc(K)² = 2·∂_T C(t, K) / (K²·∂²_K C(t, K))`.

`σloc` enters only through `hσc` and `hσrep`; `C_T`, `C_KK` are pinned to the defined
`callSurface` separately. Corollary of `dupire_pointwise_coeff` at `v2 = σloc²·K²`. -/
theorem dupire_pointwise
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + M t ω)
    (t : ℝ) (ht : 0 < t) (htT : Real.toNNReal t < T)
    {a b ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) {CK CKK : ℝ → ℝ} {Ct : ℝ → ℝ → ℝ}
    (hCK : ∀ K ∈ Ioo a b, HasDerivAt (callSurface μ X t) (CK K) K)
    (hCKK : ∀ K ∈ Ioo a b, HasDerivAt CK (CKK K) K)
    (hCKKc : ContinuousOn CKK (Ioo a b))
    (hCt : ∀ s ∈ Ioo (t - ε) (t + ε), ∀ K ∈ Ioo a b,
      HasDerivAt (fun s' => callSurface μ X s' K) (Ct s K) s)
    (hCtc : ContinuousOn (Function.uncurry Ct) (Ioo (t - ε) (t + ε) ×ˢ Ioo a b))
    {σloc : ℝ → ℝ} (hσc : ContinuousOn σloc (Ioo a b))
    (hσrep : ∀ᵐ ω ∂μ, X (Real.toNNReal t) ω ∈ Ioo a b →
      diffCoeffSq μ (reindexed X) (reindexed δ) t ω
        = σloc (X (Real.toNNReal t) ω) ^ 2 * X (Real.toNNReal t) ω ^ 2) :
    ∀ K ∈ Ioo a b, 0 < CKK K → σloc K ^ 2 = 2 * Ct t K / (K ^ 2 * CKK K) := by
  intro K hK hpos
  have h := dupire_pointwise_coeff hB hBmeas hδadap hδcont hδbdd hMadap hMeq c hXcont hXrel t ht
    htT hε hCK hCKK hCKKc hCt hCtc (v2 := fun K => σloc K ^ 2 * K ^ 2)
    ((hσc.pow 2).mul (continuousOn_id.pow 2)) hσrep K hK hpos
  have hK2 : K ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [hK.1])
  rw [mul_comm (K ^ 2), ← div_div, ← h, mul_div_assoc, div_self hK2, mul_one]

/-- **`dupire_localVol` (Def 9.4, the Markov case).** If the diffusion coefficient of the
constructed process is a function of the state, `δ_s = v(s, X_s)` (`hδloc`: the local-vol SDE's
fixed point, *carried* — SDE existence is not proved here), with `v(t, ·)` Borel and continuous
on the window, then at every strike of the window with `C_KK > 0`

  `v(t, K)² = 2·∂_T C(t, K) / ∂²_K C(t, K)`

— Thm 9.5 verbatim for the (arithmetic) local-vol model; with `v = σ_loc·x` it is the textbook
`σ_loc² = 2C_T/(K²C_KK)`. Here `𝔼[δ_t² | X_t] = v(t, X_t)²` exactly
(`condExp_of_stronglyMeasurable`, `GyongyMimicry.stronglyMeasurable_test`), so `v(t, ·)²` is a continuous
version and `dupire_pointwise_coeff` applies. -/
theorem dupire_localVol
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + M t ω)
    (t : ℝ) (ht : 0 < t) (htT : Real.toNNReal t < T)
    {a b ε : ℝ} (hε : 0 < ε) {CK CKK : ℝ → ℝ} {Ct : ℝ → ℝ → ℝ}
    (hCK : ∀ K ∈ Ioo a b, HasDerivAt (callSurface μ X t) (CK K) K)
    (hCKK : ∀ K ∈ Ioo a b, HasDerivAt CK (CKK K) K)
    (hCKKc : ContinuousOn CKK (Ioo a b))
    (hCt : ∀ s ∈ Ioo (t - ε) (t + ε), ∀ K ∈ Ioo a b,
      HasDerivAt (fun s' => callSurface μ X s' K) (Ct s K) s)
    (hCtc : ContinuousOn (Function.uncurry Ct) (Ioo (t - ε) (t + ε) ×ˢ Ioo a b))
    {v : ℝ → ℝ → ℝ} (hvm : Measurable (v t)) (hvc : ContinuousOn (v t) (Ioo a b))
    (hδloc : ∀ (s : ℝ≥0) ω, δ s ω = v s (X s ω)) :
    ∀ K ∈ Ioo a b, 0 < CKK K → v t K ^ 2 = 2 * Ct t K / CKK K := by
  have hXm : Measurable (X (Real.toNNReal t)) := by
    rw [hXrel]
    exact ((hMadap _).measurable.mono ((natFiltration hBmeas).le _) le_rfl).const_add c
  refine dupire_pointwise_coeff hB hBmeas hδadap hδcont hδbdd hMadap hMeq c hXcont hXrel t ht
    htT hε hCK hCKK hCKKc hCt hCtc (v2 := fun K => v t K ^ 2) (hvc.pow 2)
    (ae_of_all _ fun ω _ => ?_)
  -- `δ_t² = v(t, X_t)²` is `σ(X_t)`-measurable, so it is its own conditional expectation
  have hsq : (fun ω => reindexed δ t ω * reindexed δ t ω)
      = fun ω => (fun x => v t x * v t x) (reindexed X t ω) := by
    funext ω; simp only [reindexed, hδloc, Real.coe_toNNReal t ht.le]
  have hsm : StronglyMeasurable[sigmaGen (reindexed X) t]
      (fun ω => reindexed δ t ω * reindexed δ t ω) := by
    rw [hsq]; exact stronglyMeasurable_test (reindexed X) t (hvm.mul hvm)
  have hI : Integrable (fun ω => reindexed δ t ω * reindexed δ t ω) μ :=
    Integrable.of_bound (hsm.mono (sigmaGen_le _ _ hXm)).aestronglyMeasurable (Dd * Dd)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hδbdd _ _) (hδbdd _ _) (abs_nonneg _)
          ((abs_nonneg _).trans (hδbdd (Real.toNNReal t) ω)))
  show μ[_ | _] ω = _
  rw [condExp_of_stronglyMeasurable (sigmaGen_le _ _ hXm) hsm hI]
  simp only [reindexed, hδloc, Real.coe_toNNReal t ht.le]
  ring

end Pointwise

end MathFin.Dupire

