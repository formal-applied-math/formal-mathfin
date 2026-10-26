/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Portfolio.ConvexQPKKT

/-!
# Cauchy-Schwarz for positive semidefinite forms, and constrained-Sharpe maximization

Two results on a positive semidefinite matrix form `Sig` over `ι → ℝ`:

* **PSD-form Cauchy-Schwarz** (`posSemidef_cauchySchwarz`): for `Sig` positive
  semidefinite, `x ⬝ᵥ (Sig *ᵥ y) ≤ √(x ⬝ᵥ (Sig *ᵥ x)) · √(y ⬝ᵥ (Sig *ᵥ y))`.
  This is the classical Cauchy-Schwarz inequality for the semi-inner product
  `⟨u, v⟩ = u ⬝ᵥ (Sig *ᵥ v)` induced by a PSD form (Horn & Johnson, *Matrix
  Analysis*, the Cauchy-Schwarz inequality for semi-inner products); it is
  one-sided because a singular `Sig` makes the form degenerate. The proof
  completes the square on the quadratic form of `Sig` at `x - t • y`, which is
  nonnegative for every real `t` by PSD-ness, and case-splits on
  `y ⬝ᵥ (Sig *ᵥ y) = 0`: in the degenerate branch the square reads
  `0 ≤ X - 2t·Q` for all `t`, forcing `Q ≤ 0`; in the nondegenerate branch,
  evaluating at `t = Q / Y` collapses the square to `0 ≤ X - Q²/Y`, i.e.
  `Q² ≤ X·Y`.
* **Constrained-Sharpe-ratio maximization** (`constrained_sharpe_maximized`):
  the tradeoff form of the Markowitz mean-variance problem. If `x1` satisfies
  the KKT stationarity, dual-feasibility and complementary-slackness conditions
  of the risk-penalized QP `min -μ ⬝ᵥ x + (t₁/2) · x ⬝ᵥ (Sig *ᵥ x)` (with `Sig`
  PSD and `t₁ > 0`; the KKT machinery is that of `MathFin.Portfolio.ConvexQPKKT`),
  then for every feasible competitor `y`:
  `μ ⬝ᵥ y - t₁·√(x1 ⬝ᵥ (Sig *ᵥ x1)) · √(y ⬝ᵥ (Sig *ᵥ y)) ≤ μ ⬝ᵥ x1 - t₁ · (x1 ⬝ᵥ (Sig *ᵥ x1))`.
  Route: stationarity rearranged to `μ = t₁ • Sig *ᵥ x1 + ∑ u k • a k` turns the
  return gap into `t₁ · (Q - X)` plus the complementary-slackness terms
  (nonpositive at any feasible `y`, by
  `kkt_complementary_term_nonneg`), and the bilinear term is bounded by the
  PSD-form Cauchy-Schwarz inequality above.

No claim is made here that an optimal solution is a KKT point (KKT necessity);
this module certifies candidates, matching the scope of
`MathFin.Portfolio.ConvexQPKKT`.
-/

@[expose] public section

namespace MathFin

open Matrix

variable {ι : Type*} [Fintype ι] {Sig : Matrix ι ι ℝ}

/-- **Bilinearity of the quadratic form** at `u + k • v`: the quadratic form of
any matrix (symmetry not needed) splits into the two square terms and the two
cross terms. -/
theorem posSemidef_quad_expansion (u v : ι → ℝ) (k : ℝ) :
    (u + k • v) ⬝ᵥ (Sig *ᵥ (u + k • v))
      = u ⬝ᵥ (Sig *ᵥ u) + k * (u ⬝ᵥ (Sig *ᵥ v) + v ⬝ᵥ (Sig *ᵥ u))
        + k ^ 2 * (v ⬝ᵥ (Sig *ᵥ v)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- **Cauchy–Schwarz for a positive semidefinite bilinear form**: for `Sig` PSD,

`x ⬝ᵥ (Sig *ᵥ y) ≤ √(x ⬝ᵥ (Sig *ᵥ x)) · √(y ⬝ᵥ (Sig *ᵥ y))`.

One-sided: a singular `Sig` makes the form a semi-inner product only. Proof:
the quadratic form of `Sig` is nonnegative at `x − t • y` for every real `t`
(completing the square); if `y ⬝ᵥ (Sig *ᵥ y) = 0` this reads `0 ≤ X − 2t·Q`
for all `t`, forcing `Q ≤ 0` once `t` exceeds `X/(2Q)`; otherwise evaluating
at `t = Q / Y` collapses the completed square to `0 ≤ X − Q²/Y`, i.e.
`Q² ≤ X·Y`. -/
theorem posSemidef_cauchySchwarz (hpsd : Sig.PosSemidef) (x y : ι → ℝ) :
    x ⬝ᵥ (Sig *ᵥ y) ≤
      Real.sqrt (x ⬝ᵥ (Sig *ᵥ x)) * Real.sqrt (y ⬝ᵥ (Sig *ᵥ y)) := by
  have hC : Sig.IsSymm := isHermitian_iff_isSymm.mp hpsd.isHermitian
  have hX : 0 ≤ x ⬝ᵥ (Sig *ᵥ x) := by
    simpa using hpsd.dotProduct_mulVec_nonneg x
  -- the completed square: the quadratic form of `Sig` at `x - t • y`
  have key : ∀ t : ℝ, 0 ≤
      x ⬝ᵥ (Sig *ᵥ x) - 2 * t * (x ⬝ᵥ (Sig *ᵥ y)) + t ^ 2 * (y ⬝ᵥ (Sig *ᵥ y)) := by
    intro t
    have h0 : 0 ≤ (x + (-t) • y) ⬝ᵥ (Sig *ᵥ (x + (-t) • y)) := by
      simpa using hpsd.dotProduct_mulVec_nonneg (x + (-t) • y)
    have h0' : (x + (-t) • y) ⬝ᵥ (Sig *ᵥ (x + (-t) • y))
        = x ⬝ᵥ (Sig *ᵥ x) - 2 * t * (x ⬝ᵥ (Sig *ᵥ y))
          + t ^ 2 * (y ⬝ᵥ (Sig *ᵥ y)) := by
      rw [posSemidef_quad_expansion x y (-t), dotProduct_mulVec_symm_comm hC y x]
      ring
    rw [h0'] at h0
    exact h0
  by_cases hY0 : y ⬝ᵥ (Sig *ᵥ y) = 0
  · -- degenerate: `Y = 0`; the completed square reads `0 ≤ X − 2t·Q` for all `t`
    have hQle0 : x ⬝ᵥ (Sig *ᵥ y) ≤ 0 := by
      by_contra hc
      push Not at hc
      have hneg := key (x ⬝ᵥ (Sig *ᵥ x) / (2 * x ⬝ᵥ (Sig *ᵥ y)) + 1)
      rw [hY0] at hneg
      simp only [mul_zero, add_zero] at hneg
      have hnz : (2:ℝ) * x ⬝ᵥ (Sig *ᵥ y) ≠ 0 := by linarith
      have hexp : 2 * ((x ⬝ᵥ (Sig *ᵥ x) / (2 * x ⬝ᵥ (Sig *ᵥ y)) + 1)
          * (x ⬝ᵥ (Sig *ᵥ y))) = x ⬝ᵥ (Sig *ᵥ x) + 2 * x ⬝ᵥ (Sig *ᵥ y) := by
        field_simp
      linarith
    rw [hY0, Real.sqrt_zero, mul_zero]
    exact hQle0
  · -- nondegenerate: evaluate the completed square at `t = Q / Y`
    have hYne : y ⬝ᵥ (Sig *ᵥ y) ≠ 0 := fun h => hY0 h
    have hYpos : (0:ℝ) < y ⬝ᵥ (Sig *ᵥ y) := by
      have hy : y ⬝ᵥ (Sig *ᵥ y) ≥ 0 := by
        simpa using hpsd.dotProduct_mulVec_nonneg y
      exact lt_of_le_of_ne hy (fun hc => hYne hc.symm)
    have hQt := key (x ⬝ᵥ (Sig *ᵥ y) / y ⬝ᵥ (Sig *ᵥ y))
    have h2q : 2 * (x ⬝ᵥ (Sig *ᵥ y) / y ⬝ᵥ (Sig *ᵥ y)) * (x ⬝ᵥ (Sig *ᵥ y))
        = 2 * (x ⬝ᵥ (Sig *ᵥ y)) ^ 2 / (y ⬝ᵥ (Sig *ᵥ y)) := by
      field_simp
    have ht2 : ((x ⬝ᵥ (Sig *ᵥ y)) / (y ⬝ᵥ (Sig *ᵥ y))) ^ 2 * (y ⬝ᵥ (Sig *ᵥ y))
        = (x ⬝ᵥ (Sig *ᵥ y)) ^ 2 / (y ⬝ᵥ (Sig *ᵥ y)) := by
      field_simp
    rw [h2q, ht2] at hQt
    have hsq : (x ⬝ᵥ (Sig *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (Sig *ᵥ x)) * (y ⬝ᵥ (Sig *ᵥ y)) := by
      field_simp at hQt ⊢
      linarith
    have habs : |x ⬝ᵥ (Sig *ᵥ y)|
        ≤ Real.sqrt ((x ⬝ᵥ (Sig *ᵥ x)) * (y ⬝ᵥ (Sig *ᵥ y))) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
    rw [← Real.sqrt_mul hX (y ⬝ᵥ (Sig *ᵥ y))]
    exact le_trans (le_abs_self _) habs

/-- **The constrained-Sharpe-ratio maximization** (the tradeoff form): if `x1`
satisfies the KKT stationarity, dual feasibility and complementary-slackness
conditions of the risk-penalized QP
`min −μ ⬝ᵥ x + (t₁/2) · x ⬝ᵥ (Sig *ᵥ x)`, with `Sig` positive semidefinite and
`t₁ > 0`, then for every feasible competitor `y`

`μ ⬝ᵥ y − t₁·√(x1 ⬝ᵥ (Sig *ᵥ x1)) · √(y ⬝ᵥ (Sig *ᵥ y))
  ≤ μ ⬝ᵥ x1 − t₁ · (x1 ⬝ᵥ (Sig *ᵥ x1))`,

i.e. `x1` maximizes the return gap at a price of risk proportional to the
competitor's own risk — the Markowitz/KKT tradeoff-form conclusion. Route:
stationarity rearranged to `μ = t₁ • Sig *ᵥ x1 + ∑ u k • a k` turns the return
gap into `t₁ · (Q − X)` plus the complementary-slackness terms (nonpositive at
any feasible `y`), and the bilinear term is bounded by Cauchy–Schwarz for the
PSD form. -/
theorem constrained_sharpe_maximized {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : ι → ℝ} {Sig : Matrix ι ι ℝ} (hpsd : Sig.PosSemidef) {t₁ : ℝ} (ht₁ : 0 < t₁)
    {a : κ → ι → ℝ} {b : κ → ℝ} {x1 : ι → ℝ} {u : κ → ℝ}
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hstat : -μ + t₁ • Sig *ᵥ x1 = -∑ k, u k • a k)
    (hcs : ∀ k, u k * (a k ⬝ᵥ x1 - b k) = 0)
    {y : ι → ℝ} (hfeasy : ∀ k, a k ⬝ᵥ y ≤ b k) :
    μ ⬝ᵥ y - t₁ * Real.sqrt (x1 ⬝ᵥ (Sig *ᵥ x1)) * Real.sqrt (y ⬝ᵥ (Sig *ᵥ y))
      ≤ μ ⬝ᵥ x1 - t₁ * (x1 ⬝ᵥ (Sig *ᵥ x1)) := by
  have hC : Sig.IsSymm := isHermitian_iff_isSymm.mp hpsd.isHermitian
  have hX : 0 ≤ x1 ⬝ᵥ (Sig *ᵥ x1) := by
    simpa using hpsd.dotProduct_mulVec_nonneg x1
  -- stationarity dot-product identities against `y` and against `x1`
  have hstaty : μ ⬝ᵥ y = t₁ * (x1 ⬝ᵥ (Sig *ᵥ y)) + ∑ k, u k * (a k ⬝ᵥ y) := by
    have h2 : y ⬝ᵥ (-μ + t₁ • Sig *ᵥ x1) = y ⬝ᵥ (-∑ k, u k • a k) := by rw [hstat]
    rw [dotProduct_add, dotProduct_neg, dotProduct_comm y μ, dotProduct_smul,
      dotProduct_mulVec_symm_comm hC y x1, dotProduct_neg, dotProduct_sum] at h2
    have h3 : ∀ k, y ⬝ᵥ (u k • a k) = u k * (a k ⬝ᵥ y) := by
      intro k
      rw [dotProduct_smul, dotProduct_comm y (a k)]
      simp only [smul_eq_mul]
    simp only [h3, smul_eq_mul] at h2
    linarith
  have hstatx : μ ⬝ᵥ x1 = t₁ * (x1 ⬝ᵥ (Sig *ᵥ x1)) + ∑ k, u k * (a k ⬝ᵥ x1) := by
    have h2 : x1 ⬝ᵥ (-μ + t₁ • Sig *ᵥ x1) = x1 ⬝ᵥ (-∑ k, u k • a k) := by rw [hstat]
    rw [dotProduct_add, dotProduct_neg, dotProduct_comm x1 μ, dotProduct_smul,
      dotProduct_mulVec_symm_comm hC x1 x1, dotProduct_neg, dotProduct_sum] at h2
    have h3 : ∀ k, x1 ⬝ᵥ (u k • a k) = u k * (a k ⬝ᵥ x1) := by
      intro k
      rw [dotProduct_smul, dotProduct_comm x1 (a k)]
      simp only [smul_eq_mul]
    simp only [h3, smul_eq_mul] at h2
    linarith
  -- return gap = t₁ (Q − X) + the complementary-slackness terms
  have hgap : μ ⬝ᵥ y - μ ⬝ᵥ x1
      = t₁ * (x1 ⬝ᵥ (Sig *ᵥ y) - x1 ⬝ᵥ (Sig *ᵥ x1))
        + (∑ k, u k * (a k ⬝ᵥ y) - ∑ k, u k * (a k ⬝ᵥ x1)) := by
    rw [hstaty, hstatx]
    ring
  have hcsle : 0 ≤ ∑ k, u k * (a k ⬝ᵥ x1 - a k ⬝ᵥ y) :=
    kkt_complementary_term_nonneg hu_nonneg hcs hfeasy
  have hsumsplit : ∑ k, u k * (a k ⬝ᵥ y) - ∑ k, u k * (a k ⬝ᵥ x1)
      = -∑ k, u k * (a k ⬝ᵥ x1 - a k ⬝ᵥ y) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- Cauchy–Schwarz bounds the bilinear term; assemble
  have hQle : x1 ⬝ᵥ (Sig *ᵥ y)
      ≤ Real.sqrt (x1 ⬝ᵥ (Sig *ᵥ x1)) * Real.sqrt (y ⬝ᵥ (Sig *ᵥ y)) :=
    posSemidef_cauchySchwarz hpsd x1 y
  have e1 : t₁ * (x1 ⬝ᵥ (Sig *ᵥ y)) ≤ t₁ * (Real.sqrt (x1 ⬝ᵥ (Sig *ᵥ x1))
      * Real.sqrt (y ⬝ᵥ (Sig *ᵥ y))) := mul_le_mul_of_nonneg_left hQle ht₁.le
  have e3 : t₁ * (x1 ⬝ᵥ (Sig *ᵥ y) - x1 ⬝ᵥ (Sig *ᵥ x1))
      = t₁ * (x1 ⬝ᵥ (Sig *ᵥ y)) - t₁ * (x1 ⬝ᵥ (Sig *ᵥ x1)) := by ring
  linarith [hgap, hsumsplit, hcsle, e1, e3]

end MathFin
