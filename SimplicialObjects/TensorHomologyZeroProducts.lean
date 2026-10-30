/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.ComponentLifts
public import SimplicialObjects.ComponentProducts
public import SimplicialObjects.TensorHomologyZero
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Degree-zero normalized tensor homology of binary products

The tensor product of degree-zero normalized homology groups with coefficients
`A` and `B` is isomorphic to degree-zero normalized homology of the binary
simplicial product with coefficients `A ⊗[ℤ] B`. Levelwise universe lifts put
the simplicial factors in a common universe without changing their components.

The construction passes through the coproduct descriptions of degree-zero
homology, distributes the algebraic tensor product over direct sums, compares
the lifted coefficient tensors, and reindexes by the product of components.
The tensor product on the source is the algebraic tensor product of the two
homology modules.

## Implementation notes

The additive reducts of the linear equivalences are composed before applying
`AddEquiv.toIntLinearEquiv`. This supplies integer linearity for the module
structures of the endpoints without requiring definitional equality between
the group-derived integer action and the tensor or bundled module action.

## References and attribution

The component description uses `SSet.tensorNormalizedHomologyZeroIsoComponents`
and Mathlib's normalization and degree-zero homology formalizations, notably
by Joël Riou. The distribution step uses Mathlib's tensor/direct-sum
isomorphism by Kenny Lau, Mario Carneiro and Eric Wieser; the coefficient
comparison uses the universe-lift module equivalence by Kim Morrison.
-/

@[expose] public section

universe a b w v pK pL

open CategoryTheory Limits
open scoped DirectSum Simplicial TensorProduct

namespace SSet

/-- The tensor product of degree-zero normalized homology with coefficients
`A` and `B` as degree-zero normalized homology of the binary simplicial product
with coefficients `A ⊗[ℤ] B`.

The coefficient, simplex and padding universes of the two factors are
independent. The product uses the two levelwise universe lifts, and its
padding is the maximum of the two factor paddings. Both inverse identities
are inherited from the coproduct, direct-sum, coefficient and component
comparison equivalences. -/
noncomputable def tensorNormalizedHomologyZeroProductIso
    (A : Type a) (B : Type b) [AddCommGroup A] [AddCommGroup B]
    (K : SSet.{w}) (L : SSet.{v}) :
    ModuleCat.of ℤ
      ((((SSet.tensorNormalizedChainComplex.{a, w, pK} A K).homology 0) :
          Type (max a w pK)) ⊗[ℤ]
       (((SSet.tensorNormalizedChainComplex.{b, v, pL} B L).homology 0) :
          Type (max b v pL))) ≅
    (SSet.tensorNormalizedChainComplex.{max a b, max w v, max pK pL}
      (A ⊗[ℤ] B)
      (CategoryTheory.Limits.prod
        ((SSet.uliftFunctor.{v, w}).obj K)
        ((SSet.uliftFunctor.{w, v}).obj L))).homology 0 := by
  classical
  let P := CategoryTheory.Limits.prod
    ((SSet.uliftFunctor.{v, w}).obj K)
    ((SSet.uliftFunctor.{w, v}).obj L)
  let CK := ModuleCat.of ℤ (ULift.{max w pK} A)
  let CL := ModuleCat.of ℤ (ULift.{max v pL} B)
  let CP := ModuleCat.of ℤ
    (ULift.{max (max w v) (max pK pL)} (A ⊗[ℤ] B))
  let eK := (tensorNormalizedHomologyZeroIsoComponents.{a, w, pK} A K).toLinearEquiv
  let eL := (tensorNormalizedHomologyZeroIsoComponents.{b, v, pL} B L).toLinearEquiv
  let dK := (ModuleCat.coprodIsoDirectSum (fun _ : π₀ K => CK)).toLinearEquiv
  let dL := (ModuleCat.coprodIsoDirectSum (fun _ : π₀ L => CL)).toLinearEquiv
  let eP := (tensorNormalizedHomologyZeroIsoComponents.{max a b, max w v, max pK pL}
    (A ⊗[ℤ] B) P).toLinearEquiv
  let dP := (ModuleCat.coprodIsoDirectSum.{0, max w v, max a b pK pL}
    (fun _ : π₀ P => CP)).toLinearEquiv
  let uK : CK ≃ₗ[ℤ] A :=
    (ULift.moduleEquiv : ULift.{max w pK} A ≃ₗ[ℤ] A).toAddEquiv.toIntLinearEquiv
  let uL : CL ≃ₗ[ℤ] B :=
    (ULift.moduleEquiv : ULift.{max v pL} B ≃ₗ[ℤ] B).toAddEquiv.toIntLinearEquiv
  let uP : CP ≃ₗ[ℤ] (A ⊗[ℤ] B) :=
    ((ULift.moduleEquiv :
      ULift.{max (max w v) (max pK pL)} (A ⊗[ℤ] B) ≃ₗ[ℤ] (A ⊗[ℤ] B)).toAddEquiv).toIntLinearEquiv
  let coefficients : (CK ⊗[ℤ] CL) ≃ₗ[ℤ] CP :=
    ((TensorProduct.congr uK uL).toAddEquiv.trans
      uP.symm.toAddEquiv).toIntLinearEquiv
  let components : (π₀ K × π₀ L) ≃ π₀ P :=
    (Equiv.prodCongr (piZeroULiftEquiv.{v, w} K).symm
      (piZeroULiftEquiv.{w, v} L).symm).trans
      (piZeroProdEquiv
        ((SSet.uliftFunctor.{v, w}).obj K)
        ((SSet.uliftFunctor.{w, v}).obj L)).symm
  let homologyTensor := TensorProduct.congr eK eL
  let coproductTensor := TensorProduct.congr dK dL
  let distribution := TensorProduct.directSum ℤ ℤ
    (fun _ : π₀ K => CK) (fun _ : π₀ L => CL)
  let coefficientSums := DirectSum.congrLinearEquiv
    (fun _ : π₀ K × π₀ L => coefficients)
  let reindex : (⨁ (_ : π₀ K × π₀ L), CP) ≃ₗ[ℤ] (⨁ (_ : π₀ P), CP) :=
    DirectSum.lequivCongrLeft ℤ components
  let total :
      (ModuleCat.of ℤ
         ((((SSet.tensorNormalizedChainComplex.{a, w, pK} A K).homology 0) :
             Type (max a w pK)) ⊗[ℤ]
          (((SSet.tensorNormalizedChainComplex.{b, v, pL} B L).homology 0) :
             Type (max b v pL))) : Type _) ≃ₗ[ℤ]
      ((SSet.tensorNormalizedChainComplex.{max a b, max w v, max pK pL}
         (A ⊗[ℤ] B)
         (CategoryTheory.Limits.prod
           ((SSet.uliftFunctor.{v, w}).obj K)
           ((SSet.uliftFunctor.{w, v}).obj L))).homology 0 : Type _) :=
    ((AddEquivClass.toAddEquiv homologyTensor).trans
    ((AddEquivClass.toAddEquiv coproductTensor).trans
      ((AddEquivClass.toAddEquiv distribution).trans
        ((AddEquivClass.toAddEquiv coefficientSums).trans
          ((AddEquivClass.toAddEquiv reindex).trans
            ((AddEquivClass.toAddEquiv dP.symm).trans (AddEquivClass.toAddEquiv
              eP.symm))))))).toIntLinearEquiv
  exact total.toModuleIso

end SSet

namespace SSet

section Characteristic

variable (A : Type a) (B : Type b) [AddCommGroup A] [AddCommGroup B]
  (K : SSet.{w}) (L : SSet.{v})

/-- The product isomorphism sends a tensor of vertex classes to the class of
its paired vertex, with the pure tensor of the two coefficients. -/
theorem tensorNormalizedHomologyZeroProductIso_hom_class
    (k : K _⦋0⦌) (l : L _⦋0⦌) (x : A) (y : B) :
    (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K L).hom
        ((tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
            (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)) ⊗ₜ[ℤ]
          (tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
            (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y))) =
      (tensorNormalizedChainComplex.{max a b, max w v, max pK pL}
        (A ⊗[ℤ] B)
        (Limits.prod ((uliftFunctor.{v, w}).obj K)
          ((uliftFunctor.{w, v}).obj L))).homologyπ₀
        (ULift.up
          ((Limits.prod ((uliftFunctor.{v, w}).obj K)
              ((uliftFunctor.{w, v}).obj L)).normalizedIntegralSimplex
            (prodVertex (X := (uliftFunctor.{v, w}).obj K)
              (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)) ⊗ₜ[ℤ]
            (x ⊗ₜ[ℤ] y))) := by
  classical
  let P := Limits.prod ((uliftFunctor.{v, w}).obj K) ((uliftFunctor.{w, v}).obj L)
  let CK := ModuleCat.of ℤ (ULift.{max w pK} A)
  let CL := ModuleCat.of ℤ (ULift.{max v pL} B)
  let CP := ModuleCat.of ℤ (ULift.{max (max w v) (max pK pL)} (A ⊗[ℤ] B))
  let eK := (tensorNormalizedHomologyZeroIsoComponents.{a, w, pK} A K).toLinearEquiv
  let eL := (tensorNormalizedHomologyZeroIsoComponents.{b, v, pL} B L).toLinearEquiv
  let dK := (ModuleCat.coprodIsoDirectSum (fun _ : π₀ K => CK)).toLinearEquiv
  let dL := (ModuleCat.coprodIsoDirectSum (fun _ : π₀ L => CL)).toLinearEquiv
  let eP := (tensorNormalizedHomologyZeroIsoComponents.{max a b, max w v, max pK pL}
    (A ⊗[ℤ] B) P).toLinearEquiv
  let dP := (ModuleCat.coprodIsoDirectSum.{0, max w v, max a b pK pL}
    (fun _ : π₀ P => CP)).toLinearEquiv
  let uK : CK ≃ₗ[ℤ] A :=
    (ULift.moduleEquiv : ULift.{max w pK} A ≃ₗ[ℤ] A).toAddEquiv.toIntLinearEquiv
  let uL : CL ≃ₗ[ℤ] B :=
    (ULift.moduleEquiv : ULift.{max v pL} B ≃ₗ[ℤ] B).toAddEquiv.toIntLinearEquiv
  let uP : CP ≃ₗ[ℤ] (A ⊗[ℤ] B) :=
    ((ULift.moduleEquiv :
      ULift.{max (max w v) (max pK pL)} (A ⊗[ℤ] B) ≃ₗ[ℤ] (A ⊗[ℤ] B)).toAddEquiv).toIntLinearEquiv
  let coefficients :=
    ((TensorProduct.congr uK uL).toAddEquiv.trans uP.symm.toAddEquiv).toIntLinearEquiv
      (modM := TensorProduct.instModule (R := ℤ) (M := CK) (N := CL))
      (modM₂ := CP.isModule)
  let components : (π₀ K × π₀ L) ≃ π₀ P :=
    (Equiv.prodCongr (piZeroULiftEquiv.{v, w} K).symm
      (piZeroULiftEquiv.{w, v} L).symm).trans
      (piZeroProdEquiv ((uliftFunctor.{v, w}).obj K)
        ((uliftFunctor.{w, v}).obj L)).symm
  have hK : dK (eK ((tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
      (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)))) =
      DirectSum.lof ℤ (π₀ K) (fun _ => CK) (π₀.mk k) (ULift.up x) := by
    change (ModuleCat.coprodIsoDirectSum (fun _ : π₀ K => CK)).hom
      ((tensorNormalizedHomologyZeroIsoComponents.{a, w, pK} A K).hom _) = _
    rw [tensorNormalizedHomologyZeroIsoComponents_hom_class]
    exact ConcreteCategory.congr_hom
      (ModuleCat.ι_coprodIsoDirectSum_hom (fun _ : π₀ K => CK) (π₀.mk k)) (ULift.up x)
  have hL : dL (eL ((tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
      (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y)))) =
      DirectSum.lof ℤ (π₀ L) (fun _ => CL) (π₀.mk l) (ULift.up y) := by
    change (ModuleCat.coprodIsoDirectSum (fun _ : π₀ L => CL)).hom
      ((tensorNormalizedHomologyZeroIsoComponents.{b, v, pL} B L).hom _) = _
    rw [tensorNormalizedHomologyZeroIsoComponents_hom_class]
    exact ConcreteCategory.congr_hom
      (ModuleCat.ι_coprodIsoDirectSum_hom (fun _ : π₀ L => CL) (π₀.mk l)) (ULift.up y)
  have hc : coefficients ((ULift.up x : CK) ⊗ₜ[ℤ] (ULift.up y : CL)) =
      (ULift.up (x ⊗ₜ[ℤ] y) : CP) := by
    change uP.symm (TensorProduct.congr uK uL
      ((ULift.up x : CK) ⊗ₜ[ℤ] (ULift.up y : CL))) = _
    rw [TensorProduct.congr_tmul]
    rfl
  have hs : DirectSum.congrLinearEquiv (fun _ : π₀ K × π₀ L => coefficients)
      (DirectSum.lof ℤ (π₀ K × π₀ L) (fun _ => CK ⊗[ℤ] CL)
        (π₀.mk k, π₀.mk l) ((ULift.up x : CK) ⊗ₜ[ℤ] (ULift.up y : CL))) =
      DirectSum.lof ℤ (π₀ K × π₀ L) (fun _ => CP)
        (π₀.mk k, π₀.mk l) (ULift.up (x ⊗ₜ[ℤ] y)) := by
    change DirectSum.map
      (fun _ : π₀ K × π₀ L => coefficients.toAddEquiv.toAddMonoidHom)
      (DirectSum.of (fun _ : π₀ K × π₀ L => CK ⊗[ℤ] CL)
        (π₀.mk k, π₀.mk l) ((ULift.up x : CK) ⊗ₜ[ℤ] (ULift.up y : CL))) =
      DirectSum.of (fun _ : π₀ K × π₀ L => CP)
        (π₀.mk k, π₀.mk l) (ULift.up (x ⊗ₜ[ℤ] y))
    rw [DirectSum.map_of]
    exact congrArg (DirectSum.of (fun _ : π₀ K × π₀ L => CP) (π₀.mk k, π₀.mk l)) hc
  have hcomp : components (π₀.mk k, π₀.mk l) =
      π₀.mk (prodVertex (X := (uliftFunctor.{v, w}).obj K)
        (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)) := by
    exact piZeroProdEquiv_symm_mk (X := (uliftFunctor.{v, w}).obj K)
      (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)
  have hr : DirectSum.lequivCongrLeft ℤ components
      (DirectSum.lof ℤ (π₀ K × π₀ L) (fun _ => CP)
        (π₀.mk k, π₀.mk l) (ULift.up (x ⊗ₜ[ℤ] y))) =
      DirectSum.lof ℤ (π₀ P) (fun _ => CP)
        (π₀.mk (prodVertex (X := (uliftFunctor.{v, w}).obj K)
          (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)))
        (ULift.up (x ⊗ₜ[ℤ] y)) := by
    have hi : (π₀.mk k, π₀.mk l) = components.symm
        (π₀.mk (prodVertex (X := (uliftFunctor.{v, w}).obj K)
          (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l))) := by
      rw [← hcomp]
      exact (components.symm_apply_apply _).symm
    exact DirectSum.lequivCongrLeft_lof ℤ hi _ _ (by simp)
  have hT : TensorProduct.congr dK dL (TensorProduct.congr eK eL
      ((tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
          (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)) ⊗ₜ[ℤ]
        (tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
          (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y)))) =
      DirectSum.lof ℤ (π₀ K) (fun _ => CK) (π₀.mk k) (ULift.up x) ⊗ₜ[ℤ]
        DirectSum.lof ℤ (π₀ L) (fun _ => CL) (π₀.mk l) (ULift.up y) := by
    calc
      _ = dK (eK ((tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
              (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)))) ⊗ₜ[ℤ]
            dL (eL ((tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
              (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y)))) := by
        rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul]
      _ = _ := congrArg₂
        (fun (z : ⨁ (_ : π₀ K), CK) (t : ⨁ (_ : π₀ L), CL) => z ⊗ₜ[ℤ] t) hK hL
  have hDgen : TensorProduct.directSum ℤ ℤ
      (fun _ : π₀ K => CK) (fun _ : π₀ L => CL)
      (DirectSum.lof ℤ (π₀ K) (fun _ => CK) (π₀.mk k) (ULift.up x) ⊗ₜ[ℤ]
        DirectSum.lof ℤ (π₀ L) (fun _ => CL) (π₀.mk l) (ULift.up y)) =
      DirectSum.lof ℤ (π₀ K × π₀ L) (fun _ => CK ⊗[ℤ] CL)
        (π₀.mk k, π₀.mk l) ((ULift.up x : CK) ⊗ₜ[ℤ] (ULift.up y : CL)) := by
    exact TensorProduct.directSum_lof_tmul_lof ℤ ℤ
      (M₁ := fun _ : π₀ K => CK) (M₂ := fun _ : π₀ L => CL)
      (π₀.mk k) (ULift.up x : CK) (π₀.mk l) (ULift.up y : CL)
  have hD : TensorProduct.directSum ℤ ℤ
      (fun _ : π₀ K => CK) (fun _ : π₀ L => CL)
      (TensorProduct.congr dK dL (TensorProduct.congr eK eL
        ((tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
            (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)) ⊗ₜ[ℤ]
          (tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
            (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y))))) =
      DirectSum.lof ℤ (π₀ K × π₀ L) (fun _ => CK ⊗[ℤ] CL)
        (π₀.mk k, π₀.mk l) ((ULift.up x : CK) ⊗ₜ[ℤ] (ULift.up y : CL)) := by
    calc
      _ = TensorProduct.directSum ℤ ℤ
          (fun _ : π₀ K => CK) (fun _ : π₀ L => CL)
          (DirectSum.lof ℤ (π₀ K) (fun _ => CK) (π₀.mk k) (ULift.up x) ⊗ₜ[ℤ]
            DirectSum.lof ℤ (π₀ L) (fun _ => CL) (π₀.mk l) (ULift.up y)) :=
        congrArg (fun z : (⨁ (_ : π₀ K), CK) ⊗[ℤ] (⨁ (_ : π₀ L), CL) =>
          TensorProduct.directSum ℤ ℤ
            (fun _ : π₀ K => CK) (fun _ : π₀ L => CL) z) hT
      _ = _ := hDgen
  have hP : dP.symm
      (DirectSum.lof ℤ (π₀ P) (fun _ => CP)
        (π₀.mk (prodVertex (X := (uliftFunctor.{v, w}).obj K)
          (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)))
        (ULift.up (x ⊗ₜ[ℤ] y))) =
      Sigma.ι (fun _ : π₀ P => CP)
        (π₀.mk (prodVertex (X := (uliftFunctor.{v, w}).obj K)
          (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)))
        (ULift.up (x ⊗ₜ[ℤ] y)) := by
    exact ConcreteCategory.congr_hom
      (ModuleCat.lof_coprodIsoDirectSum_inv.{0, max w v, max a b pK pL}
        (fun _ : π₀ P => CP)
        (π₀.mk (prodVertex (X := (uliftFunctor.{v, w}).obj K)
          (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l))))
      (ULift.up (x ⊗ₜ[ℤ] y) : CP)
  have hE : eP.symm
      (Sigma.ι (fun _ : π₀ P => CP)
        (π₀.mk (prodVertex (X := (uliftFunctor.{v, w}).obj K)
          (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)))
        (ULift.up (x ⊗ₜ[ℤ] y))) =
      (tensorNormalizedChainComplex.{max a b, max w v, max pK pL}
        (A ⊗[ℤ] B) P).homologyπ₀
        (ULift.up (P.normalizedIntegralSimplex
          (prodVertex (X := (uliftFunctor.{v, w}).obj K)
            (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)) ⊗ₜ[ℤ]
          (x ⊗ₜ[ℤ] y))) := by
    apply eP.injective
    rw [LinearEquiv.apply_symm_apply]
    simpa only [eP, Iso.toLinearEquiv_apply] using
      (tensorNormalizedHomologyZeroIsoComponents_hom_class.{max a b, max w v, max pK pL}
        (A ⊗[ℤ] B) P
        (prodVertex (X := (uliftFunctor.{v, w}).obj K)
          (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)) (x ⊗ₜ[ℤ] y)).symm
  calc
    _ = eP.symm (dP.symm (DirectSum.lequivCongrLeft ℤ components
        (DirectSum.congrLinearEquiv (fun _ : π₀ K × π₀ L => coefficients)
          (TensorProduct.directSum ℤ ℤ (fun _ : π₀ K => CK) (fun _ : π₀ L => CL)
            (TensorProduct.congr dK dL (TensorProduct.congr eK eL
              ((tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
                  (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)) ⊗ₜ[ℤ]
                (tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
                  (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y))))))))) := by
      change
        (((AddEquivClass.toAddEquiv (TensorProduct.congr eK eL)).trans
          ((AddEquivClass.toAddEquiv (TensorProduct.congr dK dL)).trans
            ((AddEquivClass.toAddEquiv (TensorProduct.directSum ℤ ℤ
              (fun _ : π₀ K => CK) (fun _ : π₀ L => CL))).trans
              ((AddEquivClass.toAddEquiv (DirectSum.congrLinearEquiv
                (fun _ : π₀ K × π₀ L => coefficients))).trans
                ((AddEquivClass.toAddEquiv (DirectSum.lequivCongrLeft ℤ components)).trans
                  ((AddEquivClass.toAddEquiv dP.symm).trans
                    (AddEquivClass.toAddEquiv eP.symm))))))).toIntLinearEquiv
          ((tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
              (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)) ⊗ₜ[ℤ]
            (tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
              (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y)))) = _
      simp only [AddEquiv.coe_toIntLinearEquiv, AddEquiv.trans_apply,
        LinearEquiv.coe_addEquiv_apply]
    _ = eP.symm (dP.symm (DirectSum.lequivCongrLeft ℤ components
        (DirectSum.congrLinearEquiv (fun _ : π₀ K × π₀ L => coefficients)
          (DirectSum.lof ℤ (π₀ K × π₀ L) (fun _ => CK ⊗[ℤ] CL)
            (π₀.mk k, π₀.mk l) ((ULift.up x : CK) ⊗ₜ[ℤ] (ULift.up y : CL)))))) :=
      congrArg (fun z : ⨁ (_ : π₀ K × π₀ L), CK ⊗[ℤ] CL =>
        eP.symm (dP.symm (DirectSum.lequivCongrLeft ℤ components
          (DirectSum.congrLinearEquiv (fun _ : π₀ K × π₀ L => coefficients) z)))) hD
    _ = eP.symm (dP.symm (DirectSum.lequivCongrLeft ℤ components
        (DirectSum.lof ℤ (π₀ K × π₀ L) (fun _ => CP)
          (π₀.mk k, π₀.mk l) (ULift.up (x ⊗ₜ[ℤ] y))))) :=
      congrArg (fun z : ⨁ (_ : π₀ K × π₀ L), CP =>
        eP.symm (dP.symm (DirectSum.lequivCongrLeft ℤ components z))) hs
    _ = eP.symm (dP.symm
        (DirectSum.lof ℤ (π₀ P) (fun _ => CP)
          (π₀.mk (prodVertex (X := (uliftFunctor.{v, w}).obj K)
            (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)))
          (ULift.up (x ⊗ₜ[ℤ] y)))) :=
      congrArg (fun z : ⨁ (_ : π₀ P), CP => eP.symm (dP.symm z)) hr
    _ = eP.symm
        (Sigma.ι (fun _ : π₀ P => CP)
          (π₀.mk (prodVertex (X := (uliftFunctor.{v, w}).obj K)
            (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)))
          (ULift.up (x ⊗ₜ[ℤ] y))) :=
      congrArg (fun z : (∐ (fun _ : π₀ P => CP) : ModuleCat ℤ) => eP.symm z) hP
    _ = _ := hE

/-- The inverse product isomorphism recovers a tensor of vertex classes from
its paired vertex and pure coefficient tensor. -/
theorem tensorNormalizedHomologyZeroProductIso_inv_class
    (k : K _⦋0⦌) (l : L _⦋0⦌) (x : A) (y : B) :
    (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K L).inv
        ((tensorNormalizedChainComplex.{max a b, max w v, max pK pL}
          (A ⊗[ℤ] B)
          (Limits.prod ((uliftFunctor.{v, w}).obj K)
            ((uliftFunctor.{w, v}).obj L))).homologyπ₀
          (ULift.up
            ((Limits.prod ((uliftFunctor.{v, w}).obj K)
                ((uliftFunctor.{w, v}).obj L)).normalizedIntegralSimplex
              (prodVertex (X := (uliftFunctor.{v, w}).obj K)
                (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)) ⊗ₜ[ℤ]
                (x ⊗ₜ[ℤ] y)))) =
      (tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
          (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)) ⊗ₜ[ℤ]
        (tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
          (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y)) := by
  rw [← tensorNormalizedHomologyZeroProductIso_hom_class.{a, b, w, v, pK, pL}
    A B K L k l x y]
  exact ConcreteCategory.congr_hom
    (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K L).hom_inv_id _

universe u

/-- Linear maps out of the tensor of the two homology modules are determined
by pure tensors of vertex classes. The target module has an independent universe. -/
theorem tensorNormalizedHomologyZeroProduct_ext
    {N : ModuleCat.{u} ℤ}
    {F G : (ModuleCat.of ℤ
      ((((tensorNormalizedChainComplex.{a, w, pK} A K).homology 0) : Type (max a w pK)) ⊗[ℤ]
        (((tensorNormalizedChainComplex.{b, v, pL} B L).homology 0) : Type (max b v pL))))
      →ₗ[ℤ] N}
    (h : ∀ (k : K _⦋0⦌) (l : L _⦋0⦌) (x : A) (y : B),
      F ((tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
            (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)) ⊗ₜ[ℤ]
          (tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
            (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y))) =
        G ((tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
            (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)) ⊗ₜ[ℤ]
          (tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
            (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y)))) : F = G := by
  classical
  let CK := ModuleCat.of ℤ (ULift.{max w pK} A)
  let CL := ModuleCat.of ℤ (ULift.{max v pL} B)
  let eK := (tensorNormalizedHomologyZeroIsoComponents.{a, w, pK} A K).toLinearEquiv.trans
    (ModuleCat.coprodIsoDirectSum (fun _ : π₀ K => CK)).toLinearEquiv
  let eL := (tensorNormalizedHomologyZeroIsoComponents.{b, v, pL} B L).toLinearEquiv.trans
    (ModuleCat.coprodIsoDirectSum (fun _ : π₀ L => CL)).toLinearEquiv
  apply LinearMap.ext
  intro q
  induction q using TensorProduct.inductionOn with
  | tmul z t =>
    obtain ⟨s, rfl⟩ := eK.symm.surjective z
    obtain ⟨t, rfl⟩ := eL.symm.surjective t
    induction s using DirectSum.induction_on with
    | zero => simp
    | of c x =>
      induction t using DirectSum.induction_on with
      | zero => simp
      | of d y =>
        obtain ⟨k, rfl⟩ := π₀.mk_surjective c
        obtain ⟨l, rfl⟩ := π₀.mk_surjective d
        obtain ⟨x⟩ := x
        obtain ⟨y⟩ := y
        have hK : eK.symm (DirectSum.of (fun _ : π₀ K => CK) (π₀.mk k) (ULift.up x)) =
            (tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
              (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)) := by
          have hi : (ModuleCat.coprodIsoDirectSum (fun _ : π₀ K => CK)).inv
              (DirectSum.lof ℤ (π₀ K) (fun _ => CK) (π₀.mk k) (ULift.up x)) =
              Sigma.ι (fun _ : π₀ K => CK) (π₀.mk k) (ULift.up x) :=
            ConcreteCategory.congr_hom
              (ModuleCat.lof_coprodIsoDirectSum_inv (fun _ : π₀ K => CK) (π₀.mk k))
              (ULift.up x : CK)
          exact (congrArg
            (fun z => (tensorNormalizedHomologyZeroIsoComponents.{a, w, pK} A K).inv z)
            hi).trans
            (tensorNormalizedHomologyZeroIsoComponents_inv_ι.{a, w, pK} A K k x)
        have hL : eL.symm (DirectSum.of (fun _ : π₀ L => CL) (π₀.mk l) (ULift.up y)) =
            (tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
              (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y)) := by
          have hi : (ModuleCat.coprodIsoDirectSum (fun _ : π₀ L => CL)).inv
              (DirectSum.lof ℤ (π₀ L) (fun _ => CL) (π₀.mk l) (ULift.up y)) =
              Sigma.ι (fun _ : π₀ L => CL) (π₀.mk l) (ULift.up y) :=
            ConcreteCategory.congr_hom
              (ModuleCat.lof_coprodIsoDirectSum_inv (fun _ : π₀ L => CL) (π₀.mk l))
              (ULift.up y : CL)
          exact (congrArg
            (fun z => (tensorNormalizedHomologyZeroIsoComponents.{b, v, pL} B L).inv z)
            hi).trans
            (tensorNormalizedHomologyZeroIsoComponents_inv_ι.{b, v, pL} B L l y)
        rw [hK, hL]
        exact h k l x y
      | add t₁ t₂ ht₁ ht₂ =>
        simp only [map_add, TensorProduct.tmul_add, ht₁, ht₂]
    | add s₁ s₂ hs₁ hs₂ =>
      simp only [map_add, TensorProduct.add_tmul, hs₁, hs₂]
  | add q₁ q₂ hq₁ hq₂ =>
    simp only [F.map_add, G.map_add, hq₁, hq₂]

/-- The forward vertex-class formula uniquely determines the product map;
no invertibility assumption on the map is needed. -/
theorem tensorNormalizedHomologyZeroProductIso_hom_unique
    (F : ModuleCat.of ℤ
      ((((tensorNormalizedChainComplex.{a, w, pK} A K).homology 0) : Type (max a w pK)) ⊗[ℤ]
        (((tensorNormalizedChainComplex.{b, v, pL} B L).homology 0) : Type (max b v pL))) ⟶
      (tensorNormalizedChainComplex.{max a b, max w v, max pK pL} (A ⊗[ℤ] B)
        (Limits.prod ((uliftFunctor.{v, w}).obj K) ((uliftFunctor.{w, v}).obj L))).homology 0)
    (h : ∀ (k : K _⦋0⦌) (l : L _⦋0⦌) (x : A) (y : B),
      F ((tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
            (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)) ⊗ₜ[ℤ]
          (tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
            (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y))) =
        (tensorNormalizedChainComplex.{max a b, max w v, max pK pL} (A ⊗[ℤ] B)
          (Limits.prod ((uliftFunctor.{v, w}).obj K) ((uliftFunctor.{w, v}).obj L))).homologyπ₀
          (ULift.up
            ((Limits.prod ((uliftFunctor.{v, w}).obj K)
                ((uliftFunctor.{w, v}).obj L)).normalizedIntegralSimplex
              (prodVertex (X := (uliftFunctor.{v, w}).obj K)
                (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)) ⊗ₜ[ℤ]
                (x ⊗ₜ[ℤ] y)))) :
    F = (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K L).hom := by
  apply ModuleCat.hom_ext
  apply tensorNormalizedHomologyZeroProduct_ext A B K L
  intro k l x y
  exact (h k l x y).trans
    (tensorNormalizedHomologyZeroProductIso_hom_class.{a, b, w, v, pK, pL}
      A B K L k l x y).symm

/-- The inverse vertex-class formula uniquely determines the inverse map;
no invertibility assumption on the map is needed. -/
theorem tensorNormalizedHomologyZeroProductIso_inv_unique
    (G : (tensorNormalizedChainComplex.{max a b, max w v, max pK pL} (A ⊗[ℤ] B)
        (Limits.prod ((uliftFunctor.{v, w}).obj K) ((uliftFunctor.{w, v}).obj L))).homology 0 ⟶
      ModuleCat.of ℤ
        ((((tensorNormalizedChainComplex.{a, w, pK} A K).homology 0) : Type (max a w pK)) ⊗[ℤ]
          (((tensorNormalizedChainComplex.{b, v, pL} B L).homology 0) : Type (max b v pL))))
    (h : ∀ (k : K _⦋0⦌) (l : L _⦋0⦌) (x : A) (y : B),
      G ((tensorNormalizedChainComplex.{max a b, max w v, max pK pL} (A ⊗[ℤ] B)
          (Limits.prod ((uliftFunctor.{v, w}).obj K) ((uliftFunctor.{w, v}).obj L))).homologyπ₀
          (ULift.up
            ((Limits.prod ((uliftFunctor.{v, w}).obj K)
                ((uliftFunctor.{w, v}).obj L)).normalizedIntegralSimplex
              (prodVertex (X := (uliftFunctor.{v, w}).obj K)
                (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)) ⊗ₜ[ℤ]
                (x ⊗ₜ[ℤ] y)))) =
        (tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
            (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)) ⊗ₜ[ℤ]
          (tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
            (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y))) :
    G = (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K L).inv := by
  let Φ := tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K L
  have hc : Φ.hom ≫ G = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply tensorNormalizedHomologyZeroProduct_ext A B K L
    intro k l x y
    change G (Φ.hom
      ((tensorNormalizedChainComplex.{a, w, pK} A K).homologyπ₀
          (ULift.up (K.normalizedIntegralSimplex k ⊗ₜ[ℤ] x)) ⊗ₜ[ℤ]
        (tensorNormalizedChainComplex.{b, v, pL} B L).homologyπ₀
          (ULift.up (L.normalizedIntegralSimplex l ⊗ₜ[ℤ] y)))) = _
    rw [tensorNormalizedHomologyZeroProductIso_hom_class]
    exact h k l x y
  calc
    G = Φ.inv ≫ (Φ.hom ≫ G) := by simp
    _ = Φ.inv := by rw [hc, Category.comp_id]

end Characteristic

end SSet
