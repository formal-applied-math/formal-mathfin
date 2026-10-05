/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.SVI.Polynomial

/-! # The certificate matrices

Part of the SVI polynomial-sign certificate (#174).

Explicit denominator-free matrix constructions. Their correctness as a
root-counting certificate is proved in MatrixCertificate.lean. -/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- ℓ times the companion matrix of f/ℓ, where ℓ = leadingCoeff f.
Intended dimension: n = natDegree f, positive. -/
noncomputable def scaledCompanion (f : ℝ[X]) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if j.val + 1 = n then -f.coeff i.val
    else if i.val = j.val + 1 then f.leadingCoeff else 0

/-- The finite-support version of formula (17). Correct denominator clearing
requires i+j+r ≤ 38 on q.support, proved below for the SVI size bounds. -/
noncomputable def clearedHermite (f q : ℝ[X]) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ ∑ r ∈ q.support,
    q.coeff r * f.leadingCoeff ^ (38 - (i.val + j.val + r)) *
      Matrix.trace ((scaledCompanion f n) ^ (i.val + j.val + r))

theorem clearedHermite_symmetric (f q : ℝ[X]) (n : ℕ) :
    (clearedHermite f q n).IsSymm := by
  ext i j
  simp [clearedHermite, Matrix.transpose_apply, Nat.add_comm]

theorem exponent_bound (n : ℕ) (hn : n ≤ 9) (i j : Fin n) (r : ℕ) (hr : r ≤ 22) :
    i.val + j.val + r ≤ 38 := by omega

/-- Characteristic coefficient sign rule. Its identification with spectral
signature, including singular matrices, is proved in MatrixSignature.lean. -/
noncomputable def signatureTest {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℤ :=
  (M.charpoly.signVariations : ℤ) - ((M.charpoly.comp (-X)).signVariations : ℤ)

/-- The four denominator-cleared Hermite matrices of `P'` with weights `X²P²`, `XP²`, `X²P`, `XP`. -/
noncomputable def certificateMatrices (P : ℝ[X]) : Fin 4 →
    Matrix (Fin P.derivative.natDegree) (Fin P.derivative.natDegree) ℝ :=
  ![clearedHermite P.derivative (X^2*P^2) P.derivative.natDegree,
    clearedHermite P.derivative (X*P^2) P.derivative.natDegree,
    clearedHermite P.derivative (X^2*P) P.derivative.natDegree,
    clearedHermite P.derivative (X*P) P.derivative.natDegree]

/-- The signed combination of the four signature tests, which is four times `badCriticalCount` for a nonconstant polynomial of degree at most ten (`matrixCountFour_eq`). -/
noncomputable def matrixCountFour (P : ℝ[X]) : ℤ :=
  signatureTest (certificateMatrices P 0) + signatureTest (certificateMatrices P 1) -
    signatureTest (certificateMatrices P 2) - signatureTest (certificateMatrices P 3)

end SVI
end MathFin
