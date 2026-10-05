/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.SVI.TraceForm
public import MathFin.BlackScholes.SVI.ProductSignature

/-! # The Chinese remainder theorem for trace forms

Part of the SVI polynomial-sign certificate (#174).

For coprime `f`, `g`, `ℝ[X]/(fg)` is the product of the two quotients as algebras. If moreover
`f, g ≠ 0`, the weighted trace form splits as an orthogonal product, so signatures add.
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

@[simp] theorem aeval_pair {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℝ A] [Algebra ℝ B] (x : A) (y : B) (p : ℝ[X]) :
    aeval (x, y) p = (aeval x p, aeval y p) := by
  ext
  · exact (aeval_algHom_apply (AlgHom.fst ℝ A B) (x, y) p).symm
  · exact (aeval_algHom_apply (AlgHom.snd ℝ A B) (x, y) p).symm

/-- The canonical map `ℝ[X]/(fg) → ℝ[X]/(f) × ℝ[X]/(g)`. -/
noncomputable def quotientProdHom (f g : ℝ[X]) :
    AdjoinRoot (f*g) →ₐ[ℝ] AdjoinRoot f × AdjoinRoot g :=
  (AdjoinRoot.algHomOfDvd ℝ (f*g) f (dvd_mul_right _ _)).prod
    (AdjoinRoot.algHomOfDvd ℝ (f*g) g (dvd_mul_left _ _))

@[simp] theorem quotientProdHom_root (f g : ℝ[X]) :
    quotientProdHom f g (AdjoinRoot.root (f*g)) = (AdjoinRoot.root f, AdjoinRoot.root g) := by
  simp [quotientProdHom]

@[simp] theorem quotientProdHom_mk (f g p : ℝ[X]) :
    quotientProdHom f g (AdjoinRoot.mk (f*g) p) =
      (AdjoinRoot.mk f p, AdjoinRoot.mk g p) := by
  rw [← AdjoinRoot.aeval_eq,
    ← aeval_algHom_apply, quotientProdHom_root]
  simp [AdjoinRoot.aeval_eq]

theorem quotientProdHom_bijective (f g : ℝ[X]) (hc : IsCoprime f g) :
    Function.Bijective (quotientProdHom f g) := by
  constructor
  · intro x y h
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
    rw [quotientProdHom_mk, quotientProdHom_mk, Prod.mk.injEq] at h
    exact AdjoinRoot.mk_eq_mk.mpr
      (hc.mul_dvd (AdjoinRoot.mk_eq_mk.mp h.1) (AdjoinRoot.mk_eq_mk.mp h.2))
  · rintro ⟨x, y⟩
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
    obtain ⟨u, v, huv⟩ := hc
    let r := v*g*p + u*f*q
    refine ⟨AdjoinRoot.mk (f*g) r, ?_⟩
    rw [quotientProdHom_mk, Prod.mk.injEq]
    constructor
    · apply AdjoinRoot.mk_eq_mk.mpr
      refine ⟨u*(q-p), ?_⟩
      dsimp [r]
      linear_combination p * huv
    · apply AdjoinRoot.mk_eq_mk.mpr
      refine ⟨v*(p-q), ?_⟩
      dsimp [r]
      linear_combination q * huv

/-- Chinese remainder decomposition at the algebra level, preserving the
residue class of every polynomial. -/
noncomputable def quotientProdEquiv (f g : ℝ[X]) (hc : IsCoprime f g) :
    AdjoinRoot (f*g) ≃ₐ[ℝ] AdjoinRoot f × AdjoinRoot g :=
  AlgEquiv.ofBijective (quotientProdHom f g) (quotientProdHom_bijective f g hc)

@[simp] theorem quotientProdEquiv_mk (f g p : ℝ[X]) (hc : IsCoprime f g) :
    quotientProdEquiv f g hc (AdjoinRoot.mk (f*g) p) =
      (AdjoinRoot.mk f p, AdjoinRoot.mk g p) := quotientProdHom_mk f g p

@[simp] theorem quotientProdEquiv_root (f g : ℝ[X]) (hc : IsCoprime f g) :
    quotientProdEquiv f g hc (AdjoinRoot.root (f*g)) =
      (AdjoinRoot.root f, AdjoinRoot.root g) := quotientProdHom_root f g

/-- Coprime factors give an orthogonal product of their weighted trace forms.
The factors may themselves have arbitrarily repeated roots. -/
theorem weightedTraceForm_prod_equivalent (f g q : ℝ[X]) (hf : f ≠ 0) (hg : g ≠ 0)
    (hc : IsCoprime f g) :
    QuadraticMap.Equivalent (weightedTraceForm (f*g) q).toQuadraticMap
      (formProd (weightedTraceForm f q).toQuadraticMap
        (weightedTraceForm g q).toQuadraticMap) := by
  letI : Module.Free ℝ (AdjoinRoot f) := Module.Free.of_basis (AdjoinRoot.powerBasis hf).basis
  letI : Module.Free ℝ (AdjoinRoot g) := Module.Free.of_basis (AdjoinRoot.powerBasis hg).basis
  letI : FiniteDimensional ℝ (AdjoinRoot f) := Module.Finite.of_basis (AdjoinRoot.powerBasis hf).basis
  letI : FiniteDimensional ℝ (AdjoinRoot g) := Module.Finite.of_basis (AdjoinRoot.powerBasis hg).basis
  let e := quotientProdEquiv f g hc
  refine ⟨{ e.toLinearEquiv with map_app' := ?_ }⟩
  intro x
  simp only [formProd_apply, LinearMap.BilinMap.toQuadraticMap_apply, weightedTraceForm_apply]
  rw [← Algebra.trace_eq_of_algEquiv e]
  simp only [map_mul, ← aeval_algHom_apply, Algebra.trace_prod_apply]
  simp only [e, quotientProdEquiv_root, aeval_pair, Prod.fst_mul, Prod.snd_mul]
  rfl

theorem weightedTraceForm_prod_signature (f g q : ℝ[X]) (hf : f ≠ 0) (hg : g ≠ 0)
    (hc : IsCoprime f g) :
    formSignature (weightedTraceForm (f*g) q).toQuadraticMap =
      formSignature (weightedTraceForm f q).toQuadraticMap +
      formSignature (weightedTraceForm g q).toQuadraticMap := by
  letI : FiniteDimensional ℝ (AdjoinRoot f) := Module.Finite.of_basis (AdjoinRoot.powerBasis hf).basis
  letI : FiniteDimensional ℝ (AdjoinRoot g) := Module.Finite.of_basis (AdjoinRoot.powerBasis hg).basis
  rw [formSignature_eq_of_equivalent (weightedTraceForm_prod_equivalent f g q hf hg hc),
    formSignature_prod]

end SVI
end MathFin
