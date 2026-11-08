/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Choice.Portfolio.Equicorrelation
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The Marchenko-Pastur support edges

For an `N × T` matrix of independent entries with mean `0` and variance `σ²`, the sample
covariance `S = X Xᵀ / T` has, as `N, T → ∞` with aspect ratio `c = N/T` held fixed, an
eigenvalue distribution converging to the Marchenko-Pastur law, supported on the interval
with endpoints `λ₊, λ₋ = σ²(1 ± √c)²` (with an atom of mass `1 − 1/c` at `0` when `c > 1`)
— Marchenko & Pastur (1967); Bai & Silverstein (2010), ch. 3. López de Prado
(*Machine Learning for Asset Managers*, ch. 2, Snippet 2.1) uses exactly these endpoints,
in the reciprocal parameter `q = T/N`, as the cut `eMax = σ²(1 + 1/√q)²` separating noise
eigenvalues from signal when denoising a correlation matrix.

This file defines the two edges as functions `mpUpperEdge σ c = σ²(1 + √c)²` and
`mpLowerEdge σ c = σ²(1 − √c)²` and proves the algebraic, ordering, scaling and limiting
facts about the closed forms that the denoising cut uses: the support width `4σ²√c`, the
sandwich `λ₋ ≤ σ² ≤ λ₊` (for `c ≤ 1` on the left), strict monotonicity of the upper edge
in `c`, homogeneity `λ±(kσ, c) = k²λ±(σ, c)`, the limits `λ±(σ, c) → σ²` as `c → 0⁺`
(the bulk collapses to the variance when `T ≫ N`), `λ₋(σ, c) → 0` as `c → 1` (the bulk
reaches zero at the rank boundary `N = T`), `λ₊(σ, c) → ∞`, and the de Prado
parameterization `λ₊(σ, 1/q) = σ²(1 + 1/√q)²`.

A bridge to the portfolio layer ties the edges to the objects the denoising cut is applied
to: the trace of an equicorrelation matrix is the number of assets, so its average
eigenvalue is exactly `1` — the entry variance `σ² = 1` of a correlation matrix, which
sits inside the `[mpLowerEdge 1 c, mpUpperEdge 1 c]` support interval for every aspect
ratio `c ≤ 1` and is the point both edges collapse to as `c → 0⁺`.

Nothing here is probabilistic: the convergence of the empirical spectrum to the
Marchenko-Pastur law (the theorem the endpoints are the support of) is not proved, and no
random matrix, sample covariance matrix or eigenvalue appears. The aspect ratio `c` is
`N/T`; `Real.sqrt` is total (zero on negatives), so the functions are defined on all of `ℝ`
and the statements that read "for `c ≤ 1`" are about the model's regime, not a domain
restriction.

## Main definitions

* `mpUpperEdge`: the upper support edge `σ²(1 + √c)²`.
* `mpLowerEdge`: the lower support edge `σ²(1 − √c)²`.

## Main results

* `mpUpperEdge_sub_mpLowerEdge`: the support width `λ₊ − λ₋ = 4σ²√c`.
* `mpLowerEdge_le_mpUpperEdge`: `λ₋ ≤ λ₊` for every `σ`, `c`.
* `le_mpUpperEdge`: `σ² ≤ λ₊` for every `σ`, `c`.
* `mpUpperEdge_eq_variance_iff`: for `c ≥ 0`, `λ₊ = σ²` iff `σ = 0` or `c = 0`.
* `mpLowerEdge_le_variance_of_le_one`: for `c ≤ 1`, `λ₋ ≤ σ²` (with `le_mpUpperEdge`, the
  sandwich `λ₋ ≤ σ² ≤ λ₊` of the `N ≤ T` regime).
* `mpLowerEdge_eq_zero_iff`: for `σ ≠ 0`, `λ₋ = 0` iff `c = 1`, the rank boundary.
* `mpUpperEdge_mul_mpLowerEdge`: `λ₊λ₋ = σ⁴(1 − c)²` for `c ≥ 0`.
* `mpUpperEdge_lt_of_lt`: the upper edge is strictly increasing in `c` for `σ ≠ 0`.
* `continuous_mpUpperEdge`, `continuous_mpLowerEdge`: both edge maps are continuous
  (`Real.sqrt` is total).
* `tendsto_mpUpperEdge_zero`, `tendsto_mpLowerEdge_zero`: both edges tend to `σ²` as
  `c → 0⁺`.
* `tendsto_mpLowerEdge_one`: the lower edge tends to `0` as `c → 1`.
* `tendsto_mpUpperEdge_atTop`: the upper edge diverges for `σ ≠ 0`.
* `mpUpperEdge_inv`, `mpLowerEdge_inv`: the de Prado form `λ±(σ, q⁻¹) = σ²(1 ± (√q)⁻¹)²`.
* `mpUpperEdge_const_mul`, `mpLowerEdge_const_mul`: `λ±(kσ, c) = k²λ±(σ, c)`.
* `trace_equicorrelationMatrix_eq_card`: an equicorrelation matrix's trace is its dimension,
  so its average eigenvalue is `1 = σ²` for a correlation matrix — the bridge to
  `Choice/Portfolio/Equicorrelation.lean`.

## References

* [Marchenko and Pastur, *Distribution of eigenvalues for some sets of random
matrices*][MarchenkoPastur1967]
* [Bai and Silverstein, *Spectral Analysis of Large Dimensional Random
Matrices*][BaiSilverstein2010], ch. 3
* [López de Prado, *Machine Learning for Asset Managers*][LopezDePrado2020], ch. 2, Snippet 2.1

## Tags

Marchenko-Pastur, random matrix, sample covariance, eigenvalue, denoising, aspect ratio,
MSC 60B20, MSC 91G10, JEL C58, JEL G11
-/

@[expose] public section

namespace MathFin

open scoped Topology
open Filter

/-- The upper support edge of the Marchenko-Pastur law: `λ₊ = σ²(1 + √c)²`, where `σ²` is the
entry variance and `c` the aspect ratio `N/T`. This is the closed form of the support
endpoint; the convergence of the empirical spectrum to the law is not proved here. -/
noncomputable def mpUpperEdge (σ c : ℝ) : ℝ := σ ^ 2 * (1 + √c) ^ 2

/-- The lower support edge of the Marchenko-Pastur law: `λ₋ = σ²(1 − √c)²`, where `σ²` is
the entry variance and `c` the aspect ratio `N/T`. -/
noncomputable def mpLowerEdge (σ c : ℝ) : ℝ := σ ^ 2 * (1 - √c) ^ 2

/-! ### The support interval -/

/-- The Marchenko-Pastur support width: `λ₊ − λ₋ = 4σ²√c`. -/
theorem mpUpperEdge_sub_mpLowerEdge (σ c : ℝ) :
    mpUpperEdge σ c - mpLowerEdge σ c = 4 * σ ^ 2 * √c := by
  have h : (1 + √c) ^ 2 - (1 - √c) ^ 2 = 4 * √c := by ring
  rw [mpUpperEdge, mpLowerEdge, ← mul_sub, h]
  ring

/-- The edges are ordered: `λ₋ ≤ λ₊`. -/
theorem mpLowerEdge_le_mpUpperEdge (σ c : ℝ) : mpLowerEdge σ c ≤ mpUpperEdge σ c :=
  sub_nonneg.mp <| by
    rw [mpUpperEdge_sub_mpLowerEdge]
    exact mul_nonneg (by positivity) (Real.sqrt_nonneg c)

/-- The upper edge dominates the variance: `σ² ≤ λ₊`. -/
theorem le_mpUpperEdge (σ c : ℝ) : σ ^ 2 ≤ mpUpperEdge σ c := by
  have hsn : 0 ≤ √c := Real.sqrt_nonneg c
  have h : (1 : ℝ) ^ 2 ≤ (1 + √c) ^ 2 := by
    refine sq_le_sq' ?_ ?_ <;> linarith
  simpa only [mpUpperEdge, mul_one, one_pow] using mul_le_mul_of_nonneg_left h (sq_nonneg σ)

/-- The upper edge equals the variance only in the degenerate cases `σ = 0` or `c = 0`
(no estimation noise). -/
theorem mpUpperEdge_eq_variance_iff (σ c : ℝ) (hc : 0 ≤ c) :
    mpUpperEdge σ c = σ ^ 2 ↔ σ = 0 ∨ c = 0 := by
  rw [mpUpperEdge]
  constructor
  · intro h
    have h2 : σ ^ 2 * ((1 + √c) ^ 2 - 1) = 0 := by
      rw [mul_sub, mul_one]
      linarith
    rcases mul_eq_zero.mp h2 with h3 | h4
    · exact Or.inl (sq_eq_zero_iff.mp h3)
    · refine Or.inr ?_
      have hexp : (1 + √c) ^ 2 - 1 = √c * (2 + √c) := by ring
      rw [hexp] at h4
      rcases mul_eq_zero.mp h4 with h5 | h6
      · exact le_antisymm (Real.sqrt_eq_zero'.mp h5) hc
      · exact absurd h6 (by have := Real.sqrt_nonneg c; linarith)
  · rintro (h | h)
    · rw [h]; simp
    · rw [h, Real.sqrt_zero]; norm_num

/-- In the `N ≤ T` regime the variance sits in the support interval: `λ₋ ≤ σ²`. Together
with `le_mpUpperEdge` this is the sandwich `λ₋ ≤ σ² ≤ λ₊`. -/
theorem mpLowerEdge_le_variance_of_le_one (σ c : ℝ) (hc : c ≤ 1) :
    mpLowerEdge σ c ≤ σ ^ 2 := by
  have hsn : 0 ≤ √c := Real.sqrt_nonneg c
  have hs : √c ≤ 1 := by simpa using Real.sqrt_le_sqrt hc
  have h : (1 - √c) ^ 2 ≤ (1 : ℝ) ^ 2 := by
    refine sq_le_sq' ?_ ?_ <;> linarith
  simpa only [mpLowerEdge, mul_one, one_pow] using mul_le_mul_of_nonneg_left h (sq_nonneg σ)

/-- For a nonzero variance the lower edge is zero exactly at the rank boundary `N = T`. -/
theorem mpLowerEdge_eq_zero_iff {σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    mpLowerEdge σ c = 0 ↔ c = 1 := by
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ.ne'
  rw [mpLowerEdge, mul_eq_zero, or_iff_right hσ2, sq_eq_zero_iff, sub_eq_zero, eq_comm,
    Real.sqrt_eq_one]

/-- The product of the edges: `λ₊λ₋ = σ⁴(1 − c)²` for `c ≥ 0`. -/
theorem mpUpperEdge_mul_mpLowerEdge (σ c : ℝ) (hc : 0 ≤ c) :
    mpUpperEdge σ c * mpLowerEdge σ c = σ ^ 4 * (1 - c) ^ 2 := by
  have h5 : (1 + √c) * (1 - √c) = 1 - (√c) ^ 2 := by ring
  have key : (1 + √c) ^ 2 * (1 - √c) ^ 2 = (1 - c) ^ 2 := by
    rw [← mul_pow, h5, Real.sq_sqrt hc]
  rw [mpUpperEdge, mpLowerEdge, ← key]
  ring

/-! ### Continuity and limits -/

/-- The upper edge is continuous in the aspect ratio (`Real.sqrt` is total, so no domain
restriction is needed). -/
theorem continuous_mpUpperEdge (σ : ℝ) : Continuous (mpUpperEdge σ) := by
  unfold mpUpperEdge
  exact continuous_const.mul ((continuous_const.add Real.continuous_sqrt).pow 2)

/-- The lower edge is continuous in the aspect ratio. -/
theorem continuous_mpLowerEdge (σ : ℝ) : Continuous (mpLowerEdge σ) := by
  unfold mpLowerEdge
  exact continuous_const.mul ((continuous_const.sub Real.continuous_sqrt).pow 2)

/-- The upper edge is strictly increasing in the aspect ratio for `σ ≠ 0`: more instruments
per observation pushes the top of the noise bulk up. -/
theorem mpUpperEdge_lt_of_lt {σ : ℝ} (hσ : 0 < σ) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (h : c₁ < c₂) :
    mpUpperEdge σ c₁ < mpUpperEdge σ c₂ := by
  have hs : √c₁ < √c₂ := Real.sqrt_lt_sqrt hc₁ h
  have key : (1 + √c₂) ^ 2 - (1 + √c₁) ^ 2 = (√c₂ - √c₁) * (2 + √c₁ + √c₂) := by ring
  have hpos2 : 0 < 2 + √c₁ + √c₂ := by
    have h1 := Real.sqrt_nonneg c₁
    have h2 := Real.sqrt_nonneg c₂
    linarith
  rw [mpUpperEdge, mpUpperEdge, ← sub_pos, ← mul_sub, key]
  exact mul_pos (sq_pos_of_ne_zero hσ.ne') (mul_pos (sub_pos.2 hs) hpos2)

/-- The top of the bulk collapses to the variance as the aspect ratio tends to `0⁺`:
`λ₊ → σ²` when `T ≫ N`. -/
theorem tendsto_mpUpperEdge_zero (σ : ℝ) :
    Tendsto (mpUpperEdge σ) (𝓝[>] 0) (𝓝 (σ ^ 2)) := by
  have hval : mpUpperEdge σ 0 = σ ^ 2 := by simp [mpUpperEdge, Real.sqrt_zero]
  simpa only [hval] using
    ((continuous_mpUpperEdge σ).continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

/-- The bottom of the bulk collapses to the variance as the aspect ratio tends to `0⁺`:
`λ₋ → σ²` when `T ≫ N`. -/
theorem tendsto_mpLowerEdge_zero (σ : ℝ) :
    Tendsto (mpLowerEdge σ) (𝓝[>] 0) (𝓝 (σ ^ 2)) := by
  have hval : mpLowerEdge σ 0 = σ ^ 2 := by simp [mpLowerEdge, Real.sqrt_zero]
  simpa only [hval] using
    ((continuous_mpLowerEdge σ).continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

/-- The lower edge reaches zero at the rank boundary: `λ₋ → 0` as `c → 1`. -/
theorem tendsto_mpLowerEdge_one (σ : ℝ) : Tendsto (mpLowerEdge σ) (𝓝 1) (𝓝 0) := by
  have hval : mpLowerEdge σ 1 = 0 := by simp [mpLowerEdge, Real.sqrt_one]
  simpa only [hval] using (continuous_mpLowerEdge σ).continuousAt (x := 1) |>.tendsto

/-- The upper edge diverges for `σ ≠ 0`: as `c → ∞` the top of the noise bulk escapes. -/
theorem tendsto_mpUpperEdge_atTop {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (mpUpperEdge σ) atTop atTop := by
  have h1 : Tendsto (fun x : ℝ ↦ 1 + x) atTop atTop :=
    tendsto_atTop_mono (f := fun x : ℝ ↦ x) (g := fun x : ℝ ↦ 1 + x)
      (fun x ↦ by linarith) tendsto_id
  have h2 : Tendsto (fun x : ℝ ↦ (1 + x) ^ 2) atTop atTop := h1.atTop_pow₀ two_ne_zero
  have h3 : Tendsto (fun x : ℝ ↦ σ ^ 2 * (1 + x) ^ 2) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity)).mpr h2
  exact h3.comp Real.tendsto_sqrt_atTop

/-! ### The de Prado parameterization and variance scaling -/

/-- The upper edge in López de Prado's reciprocal parameter `q = T/N`: with `c = q⁻¹` the
edge is `σ²(1 + (√q)⁻¹)²`, the `eMax` of Snippet 2.1 of *Machine Learning for Asset
Managers*. -/
theorem mpUpperEdge_inv (σ q : ℝ) :
    mpUpperEdge σ q⁻¹ = σ ^ 2 * (1 + (√q)⁻¹) ^ 2 := by
  rw [mpUpperEdge, Real.sqrt_inv]

/-- The lower edge in López de Prado's reciprocal parameter `q = T/N`: the `eMin` of
Snippet 2.1. -/
theorem mpLowerEdge_inv (σ q : ℝ) :
    mpLowerEdge σ q⁻¹ = σ ^ 2 * (1 - (√q)⁻¹) ^ 2 := by
  rw [mpLowerEdge, Real.sqrt_inv]

/-- The edges are quadratic in the volatility scale: `λ₊(kσ, c) = k²λ₊(σ, c)`. -/
theorem mpUpperEdge_const_mul (k σ c : ℝ) :
    mpUpperEdge (k * σ) c = k ^ 2 * mpUpperEdge σ c := by
  rw [mpUpperEdge, mpUpperEdge]
  ring

/-- The lower edge scales the same way: `λ₋(kσ, c) = k²λ₋(σ, c)`. -/
theorem mpLowerEdge_const_mul (k σ c : ℝ) :
    mpLowerEdge (k * σ) c = k ^ 2 * mpLowerEdge σ c := by
  rw [mpLowerEdge, mpLowerEdge]
  ring

/-! ### Bridge to the portfolio layer -/

/-- An equicorrelation matrix has `1` on the diagonal, so its trace is the number of assets
and its average eigenvalue is exactly `1` — the entry variance `σ² = 1` of the correlation
matrices the denoising cut is applied to, which `le_mpUpperEdge` and
`mpLowerEdge_le_variance_of_le_one` sandwich inside `[mpLowerEdge 1 c, mpUpperEdge 1 c]`
for every aspect ratio `c ≤ 1`. -/
theorem trace_equicorrelationMatrix_eq_card (n : Type*) [Fintype n] [DecidableEq n] (ρ : ℝ) :
    (equicorrelationMatrix n ρ).trace = (Fintype.card n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, equicorrelationMatrix]

end MathFin
