/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.SVI.Matrices
public import MathFin.BlackScholes.SVI.SignVariations

/-! # Signature of a symmetric matrix from its characteristic polynomial

Part of the SVI polynomial-sign certificate (#174).

The sign variations of the characteristic coefficients compute the inertia signature of a real
symmetric matrix (`signatureTest_eq_matrixSignature`), and a positive scalar factor does not
change the test.
-/

@[expose] public section

set_option maxHeartbeats 800000

namespace MathFin
namespace SVI
open Matrix Polynomial

/-- The signature `sigPos − sigNeg` of the quadratic form of a matrix. -/
noncomputable def matrixSignature {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℤ :=
  (sigPos M.toQuadraticForm' : ℤ) - (sigNeg M.toQuadraticForm' : ℤ)

private theorem quadratic_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    M.toQuadraticForm' x = dotProduct x (M *ᵥ x) := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

private theorem quadratic_diagonal {n : ℕ} (w : Fin n → ℝ) :
    (diagonal w).toQuadraticForm' = QuadraticMap.weightedSumSquares ℝ w := by
  ext x
  simp [quadratic_apply, mulVec_diagonal, dotProduct, QuadraticMap.weightedSumSquares_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem quadratic_conjugate {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℝ) :
    ((star (U : Matrix (Fin n) (Fin n) ℝ)) * M * (U : Matrix (Fin n) (Fin n) ℝ)).toQuadraticForm' =
      M.toQuadraticForm'.comp ((Matrix.UnitaryGroup.toLinearEquiv U).toLinearMap) := by
  ext x
  simp only [QuadraticMap.comp_apply, quadratic_apply]
  change dotProduct x ((star (U : Matrix (Fin n) (Fin n) ℝ) * M * (U : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x) =
    dotProduct ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)
      (M *ᵥ ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ x))
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  change dotProduct (vecMul x (U : Matrix (Fin n) (Fin n) ℝ).conjTranspose) _ = _
  rw [vecMul_conjTranspose]
  simp

/-- Characteristic sign variations compute the inertia signature of the
associated real quadratic form, even for singular matrices. -/
theorem signatureTest_eq_matrixSignature {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) : signatureTest M = matrixSignature M := by
  have hh : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hM
  have heq : (diagonal hh.eigenvalues).toQuadraticForm' =
      M.toQuadraticForm'.comp (Matrix.UnitaryGroup.toLinearEquiv hh.eigenvectorUnitary).toLinearMap := by
    rw [← quadratic_conjugate]
    have hdiag := hh.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_star_apply, Function.comp_def] using
      congrArg Matrix.toQuadraticForm' hdiag.symm
  have he : QuadraticMap.Equivalent M.toQuadraticForm'
      (QuadraticMap.weightedSumSquares ℝ hh.eigenvalues) := by
    rw [← quadratic_diagonal, heq]
    exact ⟨QuadraticMap.isometryEquivOfCompLinearEquiv _ _⟩
  unfold signatureTest matrixSignature
  rw [signatureTest_eq_root_counts M hM, he.sigPos_eq, he.sigNeg_eq,
    QuadraticForm.sigPos_weightedSumSquares, QuadraticForm.sigNeg_weightedSumSquares,
    hh.roots_charpoly_eq_eigenvalues]
  simp only [Multiset.countP_map, RCLike.ofReal_real_eq_id, Function.comp_def]
  simp only [id_eq, ← Finset.filter_val, ← Finset.card_def,
    Set.ncard_eq_toFinset_card' , Set.toFinset_ofPred]

private theorem sigPos_smul_pos {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (c : ℝ) (hc : 0 < c) : sigPos (c • Q) = sigPos Q := by
  have hpos (V : Submodule ℝ (Fin n → ℝ)) :
      ((c • Q).restrict V).PosDef ↔ (Q.restrict V).PosDef := by
    change (∀ x : V, x ≠ 0 → 0 < c * Q x) ↔ (∀ x : V, x ≠ 0 → 0 < Q x)
    simp only [mul_pos_iff_of_pos_left hc]
  apply le_antisymm
  · obtain ⟨V, hv, hp⟩ := exists_finrank_eq_sigPos_and_posDef (c • Q)
    rw [← hv]
    exact le_sigPos_of_posDef Q ((hpos V).mp hp)
  · obtain ⟨V, hv, hp⟩ := exists_finrank_eq_sigPos_and_posDef Q
    rw [← hv]
    exact le_sigPos_of_posDef (c • Q) ((hpos V).mpr hp)

private theorem sigNeg_smul_pos {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ))
    (c : ℝ) (hc : 0 < c) : sigNeg (c • Q) = sigNeg Q := by
  have he : -(c • Q) = c • (-Q) := by
    ext x
    simp
  rw [← sigPos_neg, he, sigPos_smul_pos _ c hc, sigPos_neg]

private theorem quadratic_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    (c • M).toQuadraticForm' = c • M.toQuadraticForm' := by
  ext x
  simp [quadratic_apply, Matrix.smul_mulVec, dotProduct_smul]

/-- A positive common denominator does not change the sign certificate. -/
theorem signatureTest_smul_pos {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (c : ℝ) (hc : 0 < c) : signatureTest (c • M) = signatureTest M := by
  have hcs : (c • M).IsSymm := by
    ext i j
    simpa using congrArg (c * ·) (congrFun (congrFun hM i) j)
  rw [signatureTest_eq_matrixSignature _ hcs, signatureTest_eq_matrixSignature _ hM]
  unfold matrixSignature
  rw [quadratic_smul, sigPos_smul_pos _ c hc, sigNeg_smul_pos _ c hc]

end SVI
end MathFin
