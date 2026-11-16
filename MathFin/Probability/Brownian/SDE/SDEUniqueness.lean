/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz
public import MathFin.Probability.Brownian.SDE.SDEExistence
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Pathwise uniqueness for SDEs via Grönwall

Uniqueness half of the strong-solution theorem for `dX = μ(X)dt + σ(X)dB`, `X₀ = η`:
two solutions agree almost surely at every time. The argument is the classical
`L²`-energy / Grönwall one, carried out on the pathwise processes `X, Y : ℝ → Ω → ℝ`.

Let `g t := 𝔼[(Xₜ − Yₜ)²] = ∫_Ω (X t ω − Y t ω)² dμ` be the `L²` error. Subtracting the two
integral equations (the initial condition `η` cancels) and taking `L²` norms,
`(a+b)² ≤ 2a² + 2b²` splits the error into a drift and a diffusion contribution:
* the **drift** term is controlled by Cauchy–Schwarz in time and the Lipschitz bound on `μ`,
  giving `≤ 2t·Lμ² ∫₀ᵗ g`;
* the **diffusion** term is controlled by the **Itô isometry** — supplied here as the honest
  hypothesis `hIso` (an equality/inequality that the genuine Itô integral satisfies; in this
  library it is `MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_sq` /
  `variance_itoIntegralCLM`) — and the Lipschitz bound on `σ`, giving `≤ 2Lσ² ∫₀ᵗ g`.

Together `g t ≤ K ∫₀ᵗ g` with `K = 2(t·Lμ² + Lσ²)`, and Grönwall (in the `a = 0` form
`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`, fed the primitive `G t = ∫₀ᵗ g`)
forces `g ≡ 0`, i.e. `Xₜ = Yₜ` a.s. for every `t` of the horizon `[0,T]`.

**Honest scope.** This is the *uniqueness* half only; existence of a strong solution is
delivered separately (and, at the current toolchain, conditionally in the `L²` space `E`) by
`MathFin.SDEExistence.picardMap_exists_unique_fixedPoint`. The diffusion operator enters through
an abstract `Iσ` whose only assumed property is the isometric energy bound `hIso` — a genuine
theorem about the Itô integral, not the uniqueness conclusion in disguise. For the actual Itô
integral of `σ ∘ X` that bound is derived (`IsL2SolutionPair.uniqueness_ito`) from the Itô
isometry on bands, on a finite horizon `[0,T]`, the horizon of the library's Itô integral.

## Main definitions

* `IsL2SolutionPair`: two `L²` strong solutions of `dZ = μ(Z)dt + σ(Z)dB`, `Z₀ = η` with a shared
  driver, packaged with the regularity the energy argument uses.

## Main results

* `gronwall_zero_of_le_const_mul_integral`: Grönwall in integral form with `a = 0`: a nonnegative
  `g`, continuous on `[0,b]`, with `g t ≤ K · ∫₀ᵗ g` on `[0, b]` vanishes there.
* `sde_pathwise_uniqueness`: the `L²`-energy Grönwall argument showing two solutions agree almost
  surely at every time of `[0,T]`, under the drift and diffusion bounds taken as hypotheses.
* `IsL2SolutionPair.uniqueness`: two `L²` strong solutions sharing a driver agree almost surely
  at every time of `[0,T]`, given the Itô-isometry bound on the diffusion difference.
* `IsL2SolutionPair.uniqueness_ito`: the same when the diffusion terms are the Itô integrals
  (`itoProcessCLM`) of `σ ∘ X` and `σ ∘ Y` for a Lipschitz `σ`; the isometry bound is derived.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 8.2.5

## Tags

pathwise uniqueness, Grönwall inequality, stochastic differential equation, Itô isometry,
Lipschitz coefficients, strong solution, MSC 60H10, MSC 60H05
-/

@[expose] public section

open MeasureTheory intervalIntegral Set Topology
open scoped NNReal ENNReal

namespace MathFin

/-- **Grönwall, integral form, `a = 0`.** A nonnegative `g`, continuous on `[0,b]`, with
`g t ≤ K · ∫₀ᵗ g` for every `t ∈ [0,b]`, vanishes on `[0,b]`. The primitive `G t = ∫₀ᵗ g` has
`G' = g` from the right on `[0,t)` (FTC, `g` continuous), `G 0 = 0`, and
`‖G' x‖ = g x ≤ K·G x = K‖G x‖`, so `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` gives
`G ≡ 0`; then `g t ≤ K·G t = 0` with `g ≥ 0` gives `g t = 0`. -/
theorem gronwall_zero_of_le_const_mul_integral {g : ℝ → ℝ} {K b : ℝ}
    (hg0 : ∀ t, 0 ≤ g t) (hgc : ContinuousOn g (Set.Icc 0 b))
    (hle : ∀ t ∈ Set.Icc 0 b, g t ≤ K * ∫ s in (0 : ℝ)..t, g s) :
    ∀ t ∈ Set.Icc 0 b, g t = 0 := by
  intro t ⟨ht0, htb⟩
  set G : ℝ → ℝ := fun u ↦ ∫ s in (0:ℝ)..u, g s with hGdef
  have hgii (u : ℝ) (hu : u ∈ Set.Icc 0 b) : IntervalIntegrable g volume 0 u := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hu.1]
    exact hgc.mono (Set.Icc_subset_Icc_right hu.2)
  have hGcont : ContinuousOn G (Set.Icc 0 t) := by
    have hInt : IntegrableOn g (Set.uIcc 0 t) volume := by
      apply ContinuousOn.integrableOn_uIcc
      rw [Set.uIcc_of_le ht0]
      exact hgc.mono (Set.Icc_subset_Icc_right htb)
    have hc := intervalIntegral.continuousOn_primitive_interval hInt
    rwa [Set.uIcc_of_le ht0] at hc
  have hGderiv (x : ℝ) (hx : x ∈ Set.Ico 0 t) : HasDerivWithinAt G (g x) (Set.Ici x) x := by
    have hxb : x ∈ Set.Ico 0 b := ⟨hx.1, hx.2.trans_le htb⟩
    have hmem : Set.Icc 0 b ∈ 𝓝[>] x := Icc_mem_nhdsGT_of_mem hxb
    have hcont : ContinuousWithinAt g (Set.Ioi x) x :=
      (hgc x (Set.Ico_subset_Icc_self hxb)).mono_of_mem_nhdsWithin hmem
    have hmeas : StronglyMeasurableAtFilter g (𝓝[Set.Ioi x] x) volume :=
      (hgc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x).filter_mono
        (nhdsWithin_le_of_mem hmem)
    exact intervalIntegral.integral_hasDerivWithinAt_right
      (hgii x (Set.Ico_subset_Icc_self hxb)) hmeas hcont
  have hbound (x : ℝ) (hx : x ∈ Set.Ico 0 t) : ‖g x‖ ≤ K * ‖G x‖ := by
    rw [Real.norm_of_nonneg (hg0 x),
      Real.norm_of_nonneg (intervalIntegral.integral_nonneg hx.1 fun s _ ↦ hg0 s : 0 ≤ G x)]
    exact hle x ⟨hx.1, hx.2.le.trans htb⟩
  have hGt : G t = 0 := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hGcont hGderiv
    (by simp [hGdef]) hbound t (Set.right_mem_Icc.mpr ht0)
  have hlt := hle t ⟨ht0, htb⟩
  rw [show (∫ s in (0:ℝ)..t, g s) = 0 from hGt, mul_zero] at hlt
  exact le_antisymm hlt (hg0 t)

/-- **Cauchy–Schwarz in time** (interval-integral form): `(∫₀ˢ f)² ≤ s·∫₀ˢ f²` for `0 ≤ s`,
given `f ∈ L²` on `(0,s]`. -/
lemma sq_intervalIntegral_le {f : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 s))) :
    (∫ u in (0:ℝ)..s, f u) ^ 2 ≤ s * ∫ u in (0:ℝ)..s, (f u) ^ 2 := by
  have hcs := sq_integral_le_measureReal_mul hf
  rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hs] at hcs
  rw [intervalIntegral.integral_of_le hs, intervalIntegral.integral_of_le hs]
  exact hcs

/-- **Drift energy bound** (Cauchy–Schwarz in time + Lipschitz `μ` + Tonelli). With `μ_coef`
`Lμ`-Lipschitz, the `L²` energy of the drift-difference `∫₀ˢ (μ(Xᵤ)−μ(Yᵤ)) du` is controlled by
the time-integrated state energy:
`𝔼[(∫₀ˢ(μ(Xᵤ)−μ(Yᵤ)))²] ≤ Lμ²·s·∫₀ˢ 𝔼[(Xᵤ−Yᵤ)²]`. This *derives* the drift hypothesis of
`sde_pathwise_uniqueness` (with `Cdrift = Lμ²`), so the drift term is not assumed but proven. -/
lemma drift_energy_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {μ_coef : ℝ → ℝ} {Lμ : ℝ≥0} (hμ : LipschitzWith Lμ μ_coef)
    {X Y : ℝ → Ω → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hfL2 : ∀ᵐ ω ∂μ,
      MemLp (fun u ↦ μ_coef (X u ω) - μ_coef (Y u ω)) 2 (volume.restrict (Set.Ioc 0 s)))
    (hLHSint : Integrable (fun ω ↦ (∫ u in (0 : ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2) μ)
    (hprodXY : Integrable (Function.uncurry fun u ω ↦ (X u ω - Y u ω) ^ 2)
      ((volume.restrict (Set.uIoc 0 s)).prod μ)) :
    (∫ ω, (∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2 ∂μ)
      ≤ (Lμ : ℝ) ^ 2 * s * ∫ u in (0:ℝ)..s, (∫ ω, (X u ω - Y u ω) ^ 2 ∂μ) := by
  -- the state-error interval- and time-integrability come from product-integrability (Fubini)
  have hXYii : ∀ᵐ ω ∂μ, IntervalIntegrable (fun u ↦ (X u ω - Y u ω) ^ 2) volume 0 s := by
    filter_upwards [hprodXY.prod_left_ae] with ω hω
    simp only [Function.uncurry] at hω
    rw [Set.uIoc_of_le hs] at hω
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hs).mpr hω
  have hRHSint : Integrable (fun ω ↦ ∫ u in (0:ℝ)..s, (X u ω - Y u ω) ^ 2) μ := by
    refine (hprodXY.integral_prod_right).congr (ae_of_all _ fun ω ↦ ?_)
    simp only [Function.uncurry]
    rw [intervalIntegral.integral_of_le hs, Set.uIoc_of_le hs]
  -- a.e. pointwise:  (∫₀ˢ (μ(Xᵤ)−μ(Yᵤ)))² ≤ s·(Lμ²·∫₀ˢ (Xᵤ−Yᵤ)²)
  have hptw : ∀ᵐ ω ∂μ, (∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2
      ≤ s * ((Lμ : ℝ) ^ 2 * ∫ u in (0:ℝ)..s, (X u ω - Y u ω) ^ 2) := by
    filter_upwards [hfL2, hXYii] with ω hL2 hii
    have hCS := sq_intervalIntegral_le hs hL2
    have hLip : ∀ u, (μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2
        ≤ (Lμ : ℝ) ^ 2 * (X u ω - Y u ω) ^ 2 := by
      intro u
      have hd := hμ.dist_le_mul (X u ω) (Y u ω)
      rw [Real.dist_eq, Real.dist_eq] at hd
      have h1 : (μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2
          = |μ_coef (X u ω) - μ_coef (Y u ω)| ^ 2 := (sq_abs _).symm
      have h2 : (Lμ : ℝ) ^ 2 * (X u ω - Y u ω) ^ 2 = ((Lμ : ℝ) * |X u ω - Y u ω|) ^ 2 := by
        rw [mul_pow, sq_abs]
      rw [h1, h2]
      exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    have hLHS_ii : IntervalIntegrable (fun u ↦ (μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2) volume 0 s :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hs).mpr hL2.integrable_sq
    have hmono : (∫ u in (0:ℝ)..s, (μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2)
        ≤ ∫ u in (0:ℝ)..s, (Lμ : ℝ) ^ 2 * (X u ω - Y u ω) ^ 2 :=
      intervalIntegral.integral_mono_on hs hLHS_ii (hii.const_mul _) (fun u _ ↦ hLip u)
    calc (∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2
        ≤ s * ∫ u in (0:ℝ)..s, (μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2 := hCS
      _ ≤ s * ∫ u in (0:ℝ)..s, (Lμ : ℝ) ^ 2 * (X u ω - Y u ω) ^ 2 :=
          mul_le_mul_of_nonneg_left hmono hs
      _ = s * ((Lμ : ℝ) ^ 2 * ∫ u in (0:ℝ)..s, (X u ω - Y u ω) ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
  calc (∫ ω, (∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2 ∂μ)
      ≤ ∫ ω, s * ((Lμ : ℝ) ^ 2 * ∫ u in (0:ℝ)..s, (X u ω - Y u ω) ^ 2) ∂μ :=
        integral_mono_ae hLHSint ((hRHSint.const_mul _).const_mul _) hptw
    _ = s * (Lμ : ℝ) ^ 2 * ∫ ω, (∫ u in (0:ℝ)..s, (X u ω - Y u ω) ^ 2) ∂μ := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]; ring
    _ = s * (Lμ : ℝ) ^ 2 * ∫ u in (0:ℝ)..s, ∫ ω, (X u ω - Y u ω) ^ 2 ∂μ := by
        rw [← MeasureTheory.intervalIntegral_integral_swap
          (f := fun u ω ↦ (X u ω - Y u ω) ^ 2) hprodXY]
    _ = (Lμ : ℝ) ^ 2 * s * ∫ u in (0:ℝ)..s, ∫ ω, (X u ω - Y u ω) ^ 2 ∂μ := by ring

/-- **Pathwise SDE uniqueness via the `L²`-energy Grönwall argument.** Let `X, Y : ℝ → Ω → ℝ`
both solve `Z t = η + ∫₀ᵗ μ(Zₛ)ds + (Iσ Z)ₜ` (the initial condition `η` is common and cancels in
the difference `hdecomp`). Given the two standard `L²` energy estimates — the **drift bound**
`hdrift` (Cauchy–Schwarz in time + Lipschitz `μ`, contributing the factor `s`) and the
**diffusion bound** `hIso` (the **Itô isometry** + Lipschitz `σ`) — together with the regularity
that the state error is square-integrable per time (`hXYint`), its two pieces are square-integrable
(`hDint`, `hJint`), and the energy `s ↦ 𝔼[(Xₛ−Yₛ)²]` is continuous (`hEcont`), the two solutions
agree almost surely at every time.

The energy `E s = 𝔼[(Xₛ−Yₛ)²]` satisfies `E s ≤ (2·Cdrift·s + 2·Cdiff)·∫₀ˢ E`; on `[0,t]` the
prefactor is dominated by the constant `K = 2·Cdrift·t + 2·Cdiff`, and
`gronwall_zero_of_le_const_mul_integral` forces `E ≡ 0`, i.e. `Xₜ = Yₜ` a.s. -/
theorem sde_pathwise_uniqueness
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {μ_coef : ℝ → ℝ} {X Y : ℝ → Ω → ℝ} {Iσ : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ}
    {Cdrift Cdiff T : ℝ} (hCd : 0 ≤ Cdrift)
    (hXYint : ∀ s ∈ Set.Icc 0 T, Integrable (fun ω ↦ (X s ω - Y s ω) ^ 2) μ)
    (hDint : ∀ s ∈ Set.Icc 0 T,
      Integrable (fun ω ↦ (∫ u in (0 : ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2) μ)
    (hJint : ∀ s ∈ Set.Icc 0 T, Integrable (fun ω ↦ ((Iσ X) s ω - (Iσ Y) s ω) ^ 2) μ)
    (hEcont : ContinuousOn (fun s ↦ ∫ ω, (X s ω - Y s ω) ^ 2 ∂μ) (Set.Icc 0 T))
    (hdecomp : ∀ s ∈ Set.Icc 0 T, ∀ᵐ ω ∂μ, X s ω - Y s ω
      = (∫ u in (0 : ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) + ((Iσ X) s ω - (Iσ Y) s ω))
    (hdrift : ∀ s ∈ Set.Icc 0 T,
      (∫ ω, (∫ u in (0 : ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2 ∂μ)
        ≤ Cdrift * s * ∫ u in (0 : ℝ)..s, (∫ ω, (X u ω - Y u ω) ^ 2 ∂μ))
    (hIso : ∀ s ∈ Set.Icc 0 T,
      (∫ ω, ((Iσ X) s ω - (Iσ Y) s ω) ^ 2 ∂μ)
        ≤ Cdiff * ∫ u in (0 : ℝ)..s, (∫ ω, (X u ω - Y u ω) ^ 2 ∂μ)) :
    ∀ t ∈ Set.Icc 0 T, ∀ᵐ ω ∂μ, X t ω = Y t ω := by
  -- the L² energy of the state error
  set E : ℝ → ℝ := fun s ↦ ∫ ω, (X s ω - Y s ω) ^ 2 ∂μ
  have hE0 : ∀ s, 0 ≤ E s := fun s ↦ integral_nonneg fun ω ↦ sq_nonneg _
  have hAnn : ∀ s, 0 ≤ s → 0 ≤ ∫ u in (0:ℝ)..s, E u := fun s hs ↦
    intervalIntegral.integral_nonneg hs fun u _ ↦ hE0 u
  -- per-time energy inequality:  E s ≤ 2·Cdrift·s·(∫₀ˢ E) + 2·Cdiff·(∫₀ˢ E)
  have hEbound : ∀ s ∈ Set.Icc 0 T,
      E s ≤ 2 * Cdrift * s * (∫ u in (0:ℝ)..s, E u) + 2 * Cdiff * (∫ u in (0:ℝ)..s, E u) := by
    intro s hs
    have hEeq : E s = ∫ ω, ((∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω))
        + ((Iσ X) s ω - (Iσ Y) s ω)) ^ 2 ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hdecomp s hs] with ω hω
      rw [hω]
    have hptw : ∀ ω, ((∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω))
          + ((Iσ X) s ω - (Iσ Y) s ω)) ^ 2
        ≤ 2 * (∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2
          + 2 * ((Iσ X) s ω - (Iσ Y) s ω) ^ 2 := fun ω ↦ by
      nlinarith [sq_nonneg ((∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω))
        - ((Iσ X) s ω - (Iσ Y) s ω))]
    have hLint : Integrable (fun ω ↦ ((∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω))
        + ((Iσ X) s ω - (Iσ Y) s ω)) ^ 2) μ := by
      apply (hXYint s hs).congr
      filter_upwards [hdecomp s hs] with ω hω
      rw [hω]
    have hRint : Integrable (fun ω ↦ 2 * (∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2
        + 2 * ((Iσ X) s ω - (Iσ Y) s ω) ^ 2) μ :=
      ((hDint s hs).const_mul 2).add ((hJint s hs).const_mul 2)
    rw [hEeq]
    calc ∫ ω, ((∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω))
              + ((Iσ X) s ω - (Iσ Y) s ω)) ^ 2 ∂μ
        ≤ ∫ ω, (2 * (∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2
              + 2 * ((Iσ X) s ω - (Iσ Y) s ω) ^ 2) ∂μ := integral_mono hLint hRint hptw
      _ = 2 * (∫ ω, (∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2 ∂μ)
            + 2 * (∫ ω, ((Iσ X) s ω - (Iσ Y) s ω) ^ 2 ∂μ) := by
          rw [integral_add ((hDint s hs).const_mul 2) ((hJint s hs).const_mul 2),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ ≤ 2 * (Cdrift * s * ∫ u in (0:ℝ)..s, E u) + 2 * (Cdiff * ∫ u in (0:ℝ)..s, E u) :=
          add_le_add (by have := hdrift s hs; linarith)
            (by have := hIso s hs; linarith)
      _ = 2 * Cdrift * s * (∫ u in (0:ℝ)..s, E u) + 2 * Cdiff * (∫ u in (0:ℝ)..s, E u) := by ring
  -- conclude via Grönwall on each [0,t]
  intro t ht
  have hEt : E t = 0 := by
    refine gronwall_zero_of_le_const_mul_integral hE0
      (hEcont.mono (Set.Icc_subset_Icc_right ht.2)) (K := 2 * Cdrift * t + 2 * Cdiff)
      (b := t) ?_ t ⟨ht.1, le_rfl⟩
    intro s hs
    obtain ⟨hs0, hst⟩ := hs
    have hAs : 0 ≤ ∫ u in (0:ℝ)..s, E u := hAnn s hs0
    calc E s ≤ 2 * Cdrift * s * (∫ u in (0:ℝ)..s, E u) + 2 * Cdiff * (∫ u in (0:ℝ)..s, E u) :=
          hEbound s ⟨hs0, hst.trans ht.2⟩
      _ ≤ (2 * Cdrift * t + 2 * Cdiff) * ∫ u in (0:ℝ)..s, E u := by
          have hmono : 2 * Cdrift * s ≤ 2 * Cdrift * t :=
            mul_le_mul_of_nonneg_left hst (mul_nonneg (by norm_num) hCd)
          rw [add_mul]
          linarith [mul_le_mul_of_nonneg_right hmono hAs]
  -- E t = 0 with a nonnegative integrand ⇒ Xₜ = Yₜ a.s.
  have hsq0 : (fun ω ↦ (X t ω - Y t ω) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω ↦ sq_nonneg _) (hXYint t ht)).mp hEt
  filter_upwards [hsq0] with ω hω
  simp only [Pi.zero_apply] at hω
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hω)

/-- **A pair of `L²` strong solutions on `[0,T]`** of `dZ = μ(Z)dt + σ(Z)dB`, `Z₀ = η`, sharing
the driver, packaged with the regularity the `L²`-energy Grönwall uniqueness argument consumes.
Uniqueness is **not** a field but a *theorem* (`IsL2SolutionPair.uniqueness`) derived from these
hypotheses. The diffusion enters through the operator `Iσ` (read `Iσ Z ≈ ∫₀ᵗ σ(Zₛ)dB`); its
energy bound, the **Itô isometry** estimate, is the extra hypothesis of `uniqueness`, discharged
for the genuine Itô integral by `IsL2SolutionPair.uniqueness_ito`. The drift is **not** assumed
controlled: `lipschitz` (plus the drift regularity) *derives* its energy bound via
`drift_energy_le`. -/
structure IsL2SolutionPair {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (μ_coef : ℝ → ℝ) (Lμ : ℝ≥0) (T : ℝ)
    (X Y : ℝ → Ω → ℝ) (Iσ : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ) : Prop where
  /-- The drift coefficient is `Lμ`-Lipschitz (Theorem 8.2.5 hypothesis). -/
  lipschitz : LipschitzWith Lμ μ_coef
  /-- Both processes solve the SDE integral equation on `[0,T]`; the common initial condition `η`
  cancels in the difference. -/
  solvesDiff : ∀ s ∈ Icc 0 T, ∀ᵐ ω ∂μ, X s ω - Y s ω
    = (∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) + ((Iσ X) s ω - (Iσ Y) s ω)
  /-- The `L²` error `s ↦ 𝔼[(Xₛ−Yₛ)²]` is continuous on `[0,T]` (continuous `L²` solution
  paths). -/
  energyCont : ContinuousOn (fun s ↦ ∫ ω, (X s ω - Y s ω) ^ 2 ∂μ) (Icc 0 T)
  /-- The state error is square-integrable at each time. -/
  stateSq : ∀ s ∈ Icc 0 T, Integrable (fun ω ↦ (X s ω - Y s ω) ^ 2) μ
  /-- The drift-difference integrand is `L²` in time, a.e. `ω`. -/
  driftMemL2 : ∀ s ∈ Icc 0 T, ∀ᵐ ω ∂μ,
    MemLp (fun u ↦ μ_coef (X u ω) - μ_coef (Y u ω)) 2 (volume.restrict (Ioc 0 s))
  /-- The drift term is square-integrable. -/
  driftSq : ∀ s ∈ Icc 0 T,
    Integrable (fun ω ↦ (∫ u in (0:ℝ)..s, μ_coef (X u ω) - μ_coef (Y u ω)) ^ 2) μ
  /-- The diffusion term is square-integrable. -/
  diffSq : ∀ s ∈ Icc 0 T, Integrable (fun ω ↦ ((Iσ X) s ω - (Iσ Y) s ω) ^ 2) μ
  /-- The squared state error is jointly integrable on `(0,s] × Ω` (for Tonelli). Its two
  marginals — interval-integrability in time and integrability of the time-integral — are Fubini
  consequences, derived inside `drift_energy_le` rather than carried as separate fields. -/
  stateSqProdInt : ∀ s ∈ Icc 0 T, Integrable (Function.uncurry fun u ω ↦ (X u ω - Y u ω) ^ 2)
    ((volume.restrict (uIoc 0 s)).prod μ)

/-- **Theorem 8.2.5 (uniqueness), pathwise `L²` form on `[0,T]`.** Two `L²` strong solutions
sharing a driver agree almost surely at every time of `[0,T]`, provided the diffusion differences
satisfy the Itô-isometry energy bound `hIso` with some constant `Cdiff`. The drift energy bound is
derived from Lipschitz `μ` (`drift_energy_le`) and the `L²`-energy Grönwall argument
(`sde_pathwise_uniqueness`) closes it. -/
theorem IsL2SolutionPair.uniqueness {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {μ_coef : ℝ → ℝ} {Lμ : ℝ≥0} {T Cdiff : ℝ}
    {X Y : ℝ → Ω → ℝ} {Iσ : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ}
    (h : IsL2SolutionPair μ μ_coef Lμ T X Y Iσ)
    (hIso : ∀ s ∈ Icc 0 T, (∫ ω, ((Iσ X) s ω - (Iσ Y) s ω) ^ 2 ∂μ)
      ≤ Cdiff * ∫ u in (0:ℝ)..s, (∫ ω, (X u ω - Y u ω) ^ 2 ∂μ)) :
    ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂μ, X t ω = Y t ω :=
  sde_pathwise_uniqueness (Cdrift := (Lμ : ℝ) ^ 2) (sq_nonneg _)
    h.stateSq h.driftSq h.diffSq h.energyCont h.solvesDiff
    (fun s hs ↦ drift_energy_le h.lipschitz hs.1 (h.driftMemL2 s hs) (h.driftSq s hs)
      (h.stateSqProdInt s hs))
    hIso

open ProbabilityTheory ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral SDEExistence in
/-- **Pathwise uniqueness for Itô SDEs with Lipschitz coefficients on `[0,T]`.** Let `X, Y` be two
`L²` solutions of `dZ = μ(Z)dt + σ(Z)dB`, `σ` being `Lσ`-Lipschitz, whose diffusion terms are the
Itô integrals of `σ ∘ X` and `σ ∘ Y`: `φX, φY` are predictable `L²` classes (elements of
`Lp ℝ 2 (trimMeasure T)`), the difference `φX − φY` is the class of the pointwise difference
`X − Y` (`hrep`), and for each `s ∈ [0,T]` the diffusion difference `Iσ X s − Iσ Y s` is almost
surely the difference of the Itô integrals at time `s` of `σ ∘ φX` and `σ ∘ φY`
(`itoProcessCLM … (lipComp σ φX)`, `hIσ`). Then `X t = Y t` almost surely for every `t ∈ [0,T]`.
The isometry bound `hIso` of `IsL2SolutionPair.uniqueness`, with `Cdiff = Lσ²`, is derived from
the Itô isometry on bands (`norm_sq_itoProcessCLM_lipComp_sub_le`), the representation of the band
energy as a time integral (`bandEnergy_toLp`) and the passage from `timeMeasure` on `ℝ≥0` to the
interval integral over `ℝ` (`timeMeasure_Ioc_eq_interval`). -/
theorem IsL2SolutionPair.uniqueness_ito {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) {μ_coef σ : ℝ → ℝ} {Lμ Lσ : ℝ≥0}
    (hσ : LipschitzWith Lσ σ) {X Y : ℝ → Ω → ℝ} {Iσ : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ}
    (h : IsL2SolutionPair μ μ_coef Lμ (T : ℝ) X Y Iσ)
    (φX φY : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hg : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      (Function.uncurry fun (t : ℝ≥0) ω ↦ X t ω - Y t ω))
    (hmem : MemLp (Function.uncurry fun (t : ℝ≥0) ω ↦ X t ω - Y t ω) 2
      (trimMeasure (μ := μ) T hBmeas))
    (hrep : φX - φY = hmem.toLp _)
    (hIσ : ∀ s ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂μ, (Iσ X) s ω - (Iσ Y) s ω
      = ((itoProcessCLM hB T s.toNNReal hBmeas (lipComp T hBmeas σ Lσ hσ φX)
          - itoProcessCLM hB T s.toNNReal hBmeas (lipComp T hBmeas σ Lσ hσ φY) : Lp ℝ 2 μ) :
            Ω → ℝ) ω) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂μ, X t ω = Y t ω := by
  refine h.uniqueness (Cdiff := (Lσ : ℝ) ^ 2) fun s hs ↦ ?_
  have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
  have hc : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs.1
  have h1 : ∫ ω, ((Iσ X) s ω - (Iσ Y) s ω) ^ 2 ∂μ
      = ‖itoProcessCLM hB T s.toNNReal hBmeas (lipComp T hBmeas σ Lσ hσ φX)
        - itoProcessCLM hB T s.toNNReal hBmeas (lipComp T hBmeas σ Lσ hσ φY)‖ ^ 2 :=
    (MeasureTheory.integral_congr_ae (by filter_upwards [hIσ s hs] with ω hω; simp only [hω])).trans
      (lp_two_norm_sq _).symm
  have h3 : bandEnergy T s.toNNReal hBmeas (φX - φY)
      = ∫ t in Set.Ioc (0 : ℝ≥0) s.toNNReal, ∫ ω, (X t ω - Y t ω) ^ 2 ∂μ ∂timeMeasure := by
    rw [hrep]
    exact bandEnergy_toLp T hBmeas (g := fun t ω ↦ X t ω - Y t ω) hg hmem hsT
  have h4 : ∫ t in Set.Ioc (0 : ℝ≥0) s.toNNReal, ∫ ω, (X t ω - Y t ω) ^ 2 ∂μ ∂timeMeasure
      = ∫ u in (0 : ℝ)..s, ∫ ω, (X u ω - Y u ω) ^ 2 ∂μ := by
    refine (timeMeasure_Ioc_eq_interval
      (g := fun t : ℝ≥0 ↦ ∫ ω, (X t ω - Y t ω) ^ 2 ∂μ) s.toNNReal).trans ?_
    rw [hc]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [Set.uIcc_of_le hs.1] at hx
    simp only [Real.coe_toNNReal x hx.1]
  rw [h1]
  exact (norm_sq_itoProcessCLM_lipComp_sub_le hB T hBmeas hσ φX φY hsT).trans_eq
    (by rw [h3, h4])

/-- **Non-vacuity guard**: the hypothesis bundle is satisfiable — the zero solution on any
probability space is an `IsL2SolutionPair`. So `IsL2SolutionPair.uniqueness` is not vacuously
true of a contradictory hypothesis set. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ) :
    IsL2SolutionPair μ (μ_coef := fun _ ↦ 0) (Lμ := 0) (T := T)
      (X := fun _ _ ↦ 0) (Y := fun _ _ ↦ 0) (Iσ := fun _ _ _ ↦ 0) where
  lipschitz := (LipschitzWith.const (0 : ℝ)).weaken (le_refl 0)
  solvesDiff := fun s _ ↦ ae_of_all _ fun ω ↦ by simp
  energyCont := by simpa using continuousOn_const
  stateSq := fun s _ ↦ by simp
  driftMemL2 := fun s _ ↦ ae_of_all _ fun ω ↦ by simp
  driftSq := fun s _ ↦ by simp
  diffSq := fun s _ ↦ by simp
  stateSqProdInt := fun s _ ↦ by
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact integrable_zero _ _ _

end MathFin
