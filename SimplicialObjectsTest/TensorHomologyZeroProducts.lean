/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Logic.Equiv.Prod
import SimplicialObjects.ComponentLifts
import SimplicialObjects.ComponentProducts
import SimplicialObjects.TensorHomologyZero
import SimplicialObjects.TensorHomologyZeroProducts
import SimplicialObjects.TensorHomologyZeroProductNaturality

/-!
# Degree-zero homology of a lifted discrete binary product

The constant simplicial set on `Fin 2` has two components, distinguished by its
constant vertex labels. After lifting both factors, the categorical
product has four components. The component comparisons classify them by
`Fin 2 × Fin 2`, using vertices supplied by the Cartesian monoidal comparison.

Integer coefficient coordinates distinguish four nonzero source tensors and
four nonzero product vertex classes for independent padding universes. The
product isomorphism sends each source tensor to the correspondingly labelled
product class. Naturality computes the flip/collapse and the multiplication by
two and three coefficient maps on these classes.

The construction uses Mathlib's component quotient and constant simplicial
object. All simplicial objects here lie in universe zero.
-/

open CategoryTheory Limits

open scoped Simplicial

namespace SimplicialObjectsTest

open SSet

private def twoPoint : SSet.{0} :=
  (SimplicialObject.const (Type 0)).obj (Fin 2)

/-- Constant labels identify the components of the discrete two-point set. -/
private def twoPointComponentEquiv : π₀ twoPoint ≃ Fin 2 where
  toFun := π₀.lift (fun x ↦ x) (by
    intro x₀ x₁ e
    exact e.src_eq.symm.trans e.tgt_eq)
  invFun i := π₀.mk (X := twoPoint) i
  left_inv z := by
    obtain ⟨i, rfl⟩ := π₀.mk_surjective z
    rfl
  right_inv i := rfl

private lemma twoPointComponentEquiv_mk (i : Fin 2) :
    twoPointComponentEquiv (π₀.mk (X := twoPoint) i) = i :=
  rfl

private def liftedTwoPoint : SSet.{0} :=
  (SSet.uliftFunctor.{0, 0}).obj twoPoint

private def liftedTwoPointComponentEquiv : π₀ liftedTwoPoint ≃ Fin 2 :=
  (piZeroULiftEquiv.{0, 0} twoPoint).trans twoPointComponentEquiv

private lemma liftedTwoPointComponentEquiv_mk (i : Fin 2) :
    liftedTwoPointComponentEquiv
      (π₀.mk (X := liftedTwoPoint) (ULift.up i)) = i := by
  exact (congrArg twoPointComponentEquiv
    (piZeroULiftEquiv_apply_mk.{0, 0} twoPoint
      (ULift.up (show twoPoint _⦋0⦌ from i)))).trans
    (twoPointComponentEquiv_mk i)

private noncomputable def twoPointProduct : SSet.{0} :=
  Limits.prod liftedTwoPoint liftedTwoPoint

/-- Product vertices supplied by the Cartesian monoidal comparison. -/
private noncomputable def twoPointProductVertex (i j : Fin 2) :
    twoPointProduct _⦋0⦌ :=
  prodVertex (X := liftedTwoPoint) (Y := liftedTwoPoint) (ULift.up i) (ULift.up j)

/-- Apply the component comparison, then lower both factors. -/
private noncomputable def twoPointProductComponentEquiv :
    π₀ twoPointProduct ≃ (Fin 2 × Fin 2) :=
  (piZeroProdEquiv liftedTwoPoint liftedTwoPoint).trans
    (Equiv.prodCongr liftedTwoPointComponentEquiv liftedTwoPointComponentEquiv)

private theorem twoPointProductComponentEquiv_mk (i j : Fin 2) :
    twoPointProductComponentEquiv (π₀.mk (twoPointProductVertex i j)) = (i, j) := by
  have hfst := congrArg (π₀.mk (X := liftedTwoPoint))
    (prodVertex_fst (X := liftedTwoPoint) (Y := liftedTwoPoint)
      (ULift.up (show twoPoint _⦋0⦌ from i))
      (ULift.up (show twoPoint _⦋0⦌ from j)))
  have hsnd := congrArg (π₀.mk (X := liftedTwoPoint))
    (prodVertex_snd (X := liftedTwoPoint) (Y := liftedTwoPoint)
      (ULift.up (show twoPoint _⦋0⦌ from i))
      (ULift.up (show twoPoint _⦋0⦌ from j)))
  exact (congrArg
    (Equiv.prodCongr liftedTwoPointComponentEquiv liftedTwoPointComponentEquiv)
    (piZeroProdEquiv_mk (X := liftedTwoPoint) (Y := liftedTwoPoint)
      (twoPointProductVertex i j))).trans
    (Prod.ext
      ((congrArg liftedTwoPointComponentEquiv hfst).trans
        (liftedTwoPointComponentEquiv_mk i))
      ((congrArg liftedTwoPointComponentEquiv hsnd).trans
        (liftedTwoPointComponentEquiv_mk j)))

/-- The four pair-indexed vertex components are distinct and exhaust the product. -/
private theorem twoPointProductComponents_bijective :
    Function.Bijective (fun p : Fin 2 × Fin 2 ↦
      π₀.mk (twoPointProductVertex p.1 p.2)) := by
  constructor
  · intro p q h
    have h' := congrArg twoPointProductComponentEquiv h
    simpa only [twoPointProductComponentEquiv_mk] using h'
  · intro z
    refine ⟨twoPointProductComponentEquiv z, ?_⟩
    apply twoPointProductComponentEquiv.injective
    exact twoPointProductComponentEquiv_mk _ _

/-! ## Distinct vertex classes in degree-zero tensor homology

Component coordinates distinguish the four vertex tensors and the four product
vertex classes. The labels below use only edge invariance and the two product
projections. The homology coordinates use the component isomorphism separately
on the two factors and on the product.
-/

universe a w p pK pL

open scoped TensorProduct

/-- The constant label descends through the lifted component quotient. -/
private def liftedTwoPointLabel : π₀ liftedTwoPoint → Fin 2 :=
  π₀.lift (fun x ↦ x.down) (by
    intro x₀ x₁ e
    exact congrArg ULift.down (e.src_eq.symm.trans e.tgt_eq))

private lemma liftedTwoPointLabel_mk (i : Fin 2) :
    liftedTwoPointLabel (π₀.mk (X := liftedTwoPoint) (ULift.up i)) = i :=
  rfl

/-- Label a product component by its two projected constant labels. -/
private noncomputable def twoPointProductLabel (c : π₀ twoPointProduct) : Fin 2 × Fin 2 :=
  (liftedTwoPointLabel (mapπ₀ (Limits.prod.fst : twoPointProduct ⟶ liftedTwoPoint) c),
    liftedTwoPointLabel (mapπ₀ (Limits.prod.snd : twoPointProduct ⟶ liftedTwoPoint) c))

private lemma twoPointProductLabel_mk (i j : Fin 2) :
    twoPointProductLabel (π₀.mk (twoPointProductVertex i j)) = (i, j) := by
  have hfst := (mapπ₀_mk
    (Limits.prod.fst : twoPointProduct ⟶ liftedTwoPoint)
    (twoPointProductVertex i j)).trans
      (congrArg (π₀.mk (X := liftedTwoPoint))
        (prodVertex_fst (X := liftedTwoPoint) (Y := liftedTwoPoint)
          (ULift.up (show twoPoint _⦋0⦌ from i))
          (ULift.up (show twoPoint _⦋0⦌ from j))))
  have hsnd := (mapπ₀_mk
    (Limits.prod.snd : twoPointProduct ⟶ liftedTwoPoint)
    (twoPointProductVertex i j)).trans
      (congrArg (π₀.mk (X := liftedTwoPoint))
        (prodVertex_snd (X := liftedTwoPoint) (Y := liftedTwoPoint)
          (ULift.up (show twoPoint _⦋0⦌ from i))
          (ULift.up (show twoPoint _⦋0⦌ from j))))
  exact Prod.ext
    ((congrArg liftedTwoPointLabel hfst).trans (liftedTwoPointLabel_mk i))
    ((congrArg liftedTwoPointLabel hsnd).trans (liftedTwoPointLabel_mk j))

/-- A component label selects a coefficient coordinate of normalized homology. -/
private noncomputable def tensorVertexCoordinate
    (A : Type a) [AddCommGroup A] (S : SSet.{w})
    {I : Type} (label : π₀ S → I) (i : I) :
    (tensorNormalizedChainComplex.{a, w, p} A S).homology 0 →ₗ[ℤ] A := by
  classical
  let M := ModuleCat.of ℤ (ULift.{max w p} A)
  exact (ULift.moduleEquiv : ULift.{max w p} A ≃ₗ[ℤ] A).toLinearMap.comp
    (((tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom ≫
      Sigma.desc (fun c : π₀ S ↦ if label c = i then 𝟙 M else 0)).hom)

private lemma tensorVertexCoordinate_class
    (A : Type a) [AddCommGroup A] (S : SSet.{w})
    {I : Type} (label : π₀ S → I) (i : I) (v : S _⦋0⦌) (x : A) :
    tensorVertexCoordinate.{a, w, p} A S label i
        ((tensorNormalizedChainComplex.{a, w, p} A S).homologyπ₀
          (ULift.up (S.normalizedIntegralSimplex v ⊗ₜ[ℤ] x))) =
      (by
        classical
        exact if label (π₀.mk v) = i then x else 0) := by
  classical
  let M := ModuleCat.of ℤ (ULift.{max w p} A)
  change (ULift.moduleEquiv : ULift.{max w p} A ≃ₗ[ℤ] A)
      ((Sigma.desc (fun c : π₀ S ↦ if label c = i then 𝟙 M else 0))
        ((tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom
          ((tensorNormalizedChainComplex.{a, w, p} A S).homologyπ₀
            (ULift.up (S.normalizedIntegralSimplex v ⊗ₜ[ℤ] x))))) = _
  rw [tensorNormalizedHomologyZeroIsoComponents_hom_class]
  change (ULift.moduleEquiv : ULift.{max w p} A ≃ₗ[ℤ] A)
      ((Sigma.ι (fun _ : π₀ S ↦ M) (π₀.mk v) ≫
        Sigma.desc (fun c : π₀ S ↦ if label c = i then 𝟙 M else 0))
          (ULift.up x)) = _
  rw [Sigma.ι_desc]
  split_ifs <;> rfl

private noncomputable def twoPointH0Class (i : Fin 2) :
    (tensorNormalizedChainComplex.{0, 0, p} ℤ twoPoint).homology 0 :=
  (tensorNormalizedChainComplex.{0, 0, p} ℤ twoPoint).homologyπ₀
    (ULift.up (twoPoint.normalizedIntegralSimplex i ⊗ₜ[ℤ] (1 : ℤ)))

/-- Transport the coefficient coordinate to the usual integer module. -/
private noncomputable def twoPointClassCoordinate (i : Fin 2) :
    (tensorNormalizedChainComplex.{0, 0, p} ℤ twoPoint).homology 0 →ₗ[ℤ] ℤ :=
  ((AddEquiv.refl ℤ).toIntLinearEquiv
    (modM := AddCommGroup.toIntModule ℤ)).toLinearMap.comp
      (tensorVertexCoordinate.{0, 0, p} ℤ twoPoint twoPointComponentEquiv i)

private lemma twoPointClassCoordinate_class (i j : Fin 2) :
    twoPointClassCoordinate.{p} i (twoPointH0Class.{p} j) =
      if j = i then 1 else 0 := by
  classical
  have h := tensorVertexCoordinate_class.{0, 0, p} ℤ twoPoint
    twoPointComponentEquiv i (show twoPoint _⦋0⦌ from j) (1 : ℤ)
  by_cases hji : j = i <;>
    simpa [twoPointClassCoordinate, twoPointH0Class, twoPointComponentEquiv_mk, hji] using h

private noncomputable def twoPointSourceClass (q : Fin 2 × Fin 2) :
    ((tensorNormalizedChainComplex.{0, 0, pK} ℤ twoPoint).homology 0) ⊗[ℤ]
      ((tensorNormalizedChainComplex.{0, 0, pL} ℤ twoPoint).homology 0) :=
  twoPointH0Class.{pK} q.1 ⊗ₜ[ℤ] twoPointH0Class.{pL} q.2

private noncomputable def twoPointSourceDetector (q : Fin 2 × Fin 2) :
    (((tensorNormalizedChainComplex.{0, 0, pK} ℤ twoPoint).homology 0) ⊗[ℤ]
      ((tensorNormalizedChainComplex.{0, 0, pL} ℤ twoPoint).homology 0)) →ₗ[ℤ] ℤ := by
  let d := (TensorProduct.lid ℤ ℤ).toLinearMap.comp
    (TensorProduct.map (twoPointClassCoordinate.{pK} q.1)
      (twoPointClassCoordinate.{pL} q.2))
  -- The detector's source uses the canonical integer action on the tensor group.
  exact d.toAddMonoidHom.toIntLinearMap

private lemma twoPointSourceDetector_class (q s : Fin 2 × Fin 2) :
    twoPointSourceDetector.{pK, pL} q (twoPointSourceClass.{pK, pL} s) =
      if s = q then 1 else 0 := by
  classical
  change (TensorProduct.lid ℤ ℤ)
      (TensorProduct.map (twoPointClassCoordinate.{pK} q.1)
        (twoPointClassCoordinate.{pL} q.2)
        (twoPointH0Class.{pK} s.1 ⊗ₜ[ℤ] twoPointH0Class.{pL} s.2)) = _
  rw [TensorProduct.map_tmul, twoPointClassCoordinate_class, twoPointClassCoordinate_class]
  by_cases h₁ : s.1 = q.1 <;> by_cases h₂ : s.2 = q.2 <;>
    simp [h₁, h₂, Prod.ext_iff, TensorProduct.lid_tmul]

private noncomputable def twoPointTargetClass (q : Fin 2 × Fin 2) :
    (tensorNormalizedChainComplex.{0, 0, p}
      (ℤ ⊗[ℤ] ℤ) twoPointProduct).homology 0 :=
  (tensorNormalizedChainComplex.{0, 0, p}
    (ℤ ⊗[ℤ] ℤ) twoPointProduct).homologyπ₀
      (ULift.up (twoPointProduct.normalizedIntegralSimplex
        (twoPointProductVertex q.1 q.2) ⊗ₜ[ℤ] ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ))))

private noncomputable def twoPointTargetDetector (q : Fin 2 × Fin 2) :
    (tensorNormalizedChainComplex.{0, 0, p}
      (ℤ ⊗[ℤ] ℤ) twoPointProduct).homology 0 →ₗ[ℤ] ℤ :=
  ((TensorProduct.lid ℤ ℤ).toAddEquiv.toIntLinearEquiv
    (modM := AddCommGroup.toIntModule (ℤ ⊗[ℤ] ℤ))).toLinearMap.comp
      (tensorVertexCoordinate.{0, 0, p}
        (ℤ ⊗[ℤ] ℤ) twoPointProduct twoPointProductLabel q)

private lemma twoPointTargetDetector_class (q s : Fin 2 × Fin 2) :
    twoPointTargetDetector.{p} q (twoPointTargetClass.{p} s) =
      if s = q then 1 else 0 := by
  classical
  change (TensorProduct.lid ℤ ℤ)
      (tensorVertexCoordinate.{0, 0, p}
        (ℤ ⊗[ℤ] ℤ) twoPointProduct twoPointProductLabel q
        ((tensorNormalizedChainComplex.{0, 0, p}
          (ℤ ⊗[ℤ] ℤ) twoPointProduct).homologyπ₀
            (ULift.up (twoPointProduct.normalizedIntegralSimplex
              (twoPointProductVertex s.1 s.2) ⊗ₜ[ℤ] ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)))))) = _
  rw [tensorVertexCoordinate_class, twoPointProductLabel_mk]
  by_cases h : s = q <;> simp [h, TensorProduct.lid_tmul]

/-- The four source tensors and the four product classes are nonzero and distinct. -/
private theorem twoPointH0_nonvacuity :
    (∀ q : Fin 2 × Fin 2, twoPointSourceClass.{pK, pL} q ≠ 0) ∧
    Function.Injective twoPointSourceClass.{pK, pL} ∧
    (∀ q : Fin 2 × Fin 2, twoPointTargetClass.{max pK pL} q ≠ 0) ∧
    Function.Injective twoPointTargetClass.{max pK pL} := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q h
    have e := congrArg (twoPointSourceDetector.{pK, pL} q) h
    simp [twoPointSourceDetector_class] at e
  · intro q s h
    by_contra hqs
    have hsq : s ≠ q := Ne.symm hqs
    have e := congrArg (twoPointSourceDetector.{pK, pL} q) h
    simp [twoPointSourceDetector_class, hsq] at e
  · intro q h
    have e := congrArg (twoPointTargetDetector.{max pK pL} q) h
    simp [twoPointTargetDetector_class] at e
  · intro q s h
    by_contra hqs
    have hsq : s ≠ q := Ne.symm hqs
    have e := congrArg (twoPointTargetDetector.{max pK pL} q) h
    simp [twoPointTargetDetector_class, hsq] at e

/-- The degree-zero product isomorphism for two discrete two-point factors. -/
private noncomputable def twoPointH0ProductIso :
    ModuleCat.of ℤ
      ((((SSet.tensorNormalizedChainComplex.{0, 0, pK} ℤ twoPoint).homology 0) :
          Type pK) ⊗[ℤ]
        (((SSet.tensorNormalizedChainComplex.{0, 0, pL} ℤ twoPoint).homology 0) :
          Type pL)) ≅
    (SSet.tensorNormalizedChainComplex.{0, 0, max pK pL}
      (ℤ ⊗[ℤ] ℤ) twoPointProduct).homology 0 :=
  SSet.tensorNormalizedHomologyZeroProductIso.{0, 0, 0, 0, pK, pL}
    ℤ ℤ twoPoint twoPoint

end SimplicialObjectsTest

namespace SimplicialObjectsTest

universe pK pL

/-- On the four integer vertex tensors of the discrete two-by-two product,
the product isomorphism has the corresponding four product vertex classes. -/
private theorem twoPointH0ProductIso_hom_table :
    (twoPointH0ProductIso.{pK, pL}).hom (twoPointSourceClass.{pK, pL} (0, 0)) =
        twoPointTargetClass.{max pK pL} (0, 0) ∧
      (twoPointH0ProductIso.{pK, pL}).hom (twoPointSourceClass.{pK, pL} (0, 1)) =
        twoPointTargetClass.{max pK pL} (0, 1) ∧
      (twoPointH0ProductIso.{pK, pL}).hom (twoPointSourceClass.{pK, pL} (1, 0)) =
        twoPointTargetClass.{max pK pL} (1, 0) ∧
      (twoPointH0ProductIso.{pK, pL}).hom (twoPointSourceClass.{pK, pL} (1, 1)) =
        twoPointTargetClass.{max pK pL} (1, 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SSet.tensorNormalizedHomologyZeroProductIso_hom_class.{0, 0, 0, 0, pK, pL}
      ℤ ℤ twoPoint twoPoint (0 : Fin 2) (0 : Fin 2) (1 : ℤ) (1 : ℤ)
  · exact SSet.tensorNormalizedHomologyZeroProductIso_hom_class.{0, 0, 0, 0, pK, pL}
      ℤ ℤ twoPoint twoPoint (0 : Fin 2) (1 : Fin 2) (1 : ℤ) (1 : ℤ)
  · exact SSet.tensorNormalizedHomologyZeroProductIso_hom_class.{0, 0, 0, 0, pK, pL}
      ℤ ℤ twoPoint twoPoint (1 : Fin 2) (0 : Fin 2) (1 : ℤ) (1 : ℤ)
  · exact SSet.tensorNormalizedHomologyZeroProductIso_hom_class.{0, 0, 0, 0, pK, pL}
      ℤ ℤ twoPoint twoPoint (1 : Fin 2) (1 : Fin 2) (1 : ℤ) (1 : ℤ)

end SimplicialObjectsTest

namespace SimplicialObjectsTest

open CategoryTheory Limits Opposite SSet
open scoped Simplicial TensorProduct

/-- Flipping the first label and collapsing the second sends the four product
classes to the corresponding classes with labels `(1 - i, 0)`. -/
example (q : Fin 2 × Fin 2) :
    let f : twoPoint ⟶ twoPoint :=
      (SimplicialObject.const (Type 0)).map (TypeCat.ofHom (fun i : Fin 2 ↦ 1 - i))
    let g : twoPoint ⟶ twoPoint :=
      (SimplicialObject.const (Type 0)).map (TypeCat.ofHom (fun _ : Fin 2 ↦ 0))
    HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexMap.{0, 0, 0} (ℤ ⊗[ℤ] ℤ)
          (Limits.prod.map ((SSet.uliftFunctor.{0, 0}).map f)
            ((SSet.uliftFunctor.{0, 0}).map g))) 0
        (twoPointTargetClass.{0} q) =
      twoPointTargetClass.{0} (1 - q.1, 0) := by
  dsimp only
  let f : twoPoint ⟶ twoPoint :=
    (SimplicialObject.const (Type 0)).map (TypeCat.ofHom (fun i : Fin 2 ↦ 1 - i))
  let g : twoPoint ⟶ twoPoint :=
    (SimplicialObject.const (Type 0)).map (TypeCat.ofHom (fun _ : Fin 2 ↦ 0))
  let E := twoPointH0ProductIso.{0, 0}
  let Hf := HomologicalComplex.homologyMap
    (tensorNormalizedChainComplexMap.{0, 0, 0} ℤ f) 0
  let Hg := HomologicalComplex.homologyMap
    (tensorNormalizedChainComplexMap.{0, 0, 0} ℤ g) 0
  let H := HomologicalComplex.homologyMap
    (tensorNormalizedChainComplexMap.{0, 0, 0} (ℤ ⊗[ℤ] ℤ)
      (Limits.prod.map ((SSet.uliftFunctor.{0, 0}).map f)
        ((SSet.uliftFunctor.{0, 0}).map g))) 0
  have hf : Hf (twoPointH0Class.{0} q.1) = twoPointH0Class.{0} (1 - q.1) :=
    tensorNormalizedHomologyZeroMap_class.{0, 0, 0} ℤ f q.1 1
  have hg : Hg (twoPointH0Class.{0} q.2) = twoPointH0Class.{0} 0 :=
    tensorNormalizedHomologyZeroMap_class.{0, 0, 0} ℤ g q.2 1
  have hs : E.hom (twoPointSourceClass.{0, 0} q) = twoPointTargetClass.{0} q :=
    tensorNormalizedHomologyZeroProductIso_hom_class.{0, 0, 0, 0, 0, 0}
      ℤ ℤ twoPoint twoPoint q.1 q.2 1 1
  have ht : E.hom (twoPointSourceClass.{0, 0} (1 - q.1, 0)) =
      twoPointTargetClass.{0} (1 - q.1, 0) :=
    tensorNormalizedHomologyZeroProductIso_hom_class.{0, 0, 0, 0, 0, 0}
      ℤ ℤ twoPoint twoPoint (1 - q.1) (0 : Fin 2) 1 1
  have e := ConcreteCategory.congr_hom
    (tensorNormalizedHomologyZeroProductIso_hom_naturality.{0, 0, 0, 0, 0, 0} ℤ ℤ f g)
    (twoPointSourceClass.{0, 0} q)
  change E.hom (TensorProduct.map Hf.hom Hg.hom
      (twoPointH0Class.{0} q.1 ⊗ₜ[ℤ] twoPointH0Class.{0} q.2)) =
    H (E.hom (twoPointSourceClass.{0, 0} q)) at e
  rw [TensorProduct.map_tmul] at e
  exact (congrArg (fun z => H z) hs.symm).trans
    (e.symm.trans ((congrArg (fun z => E.hom z)
      (congrArg₂ (fun s t => s ⊗ₜ[ℤ] t) hf hg)).trans ht))

/-- Multiplying the coefficients in the two factors by two and three multiplies
each of the four product vertex classes by six. -/
example (q : Fin 2 × Fin 2) :
    let m : ℤ →+ ℤ := (2 : ℤ) • AddMonoidHom.id ℤ
    let n : ℤ →+ ℤ := (3 : ℤ) • AddMonoidHom.id ℤ
    HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
          (TensorProduct.map m.toIntLinearMap n.toIntLinearMap).toAddMonoidHom
          twoPointProduct) 0 (twoPointTargetClass.{0} q) =
      (6 : ℤ) • twoPointTargetClass.{0} q := by
  dsimp only
  let m : ℤ →+ ℤ := (2 : ℤ) • AddMonoidHom.id ℤ
  let n : ℤ →+ ℤ := (3 : ℤ) • AddMonoidHom.id ℤ
  let E := twoPointH0ProductIso.{0, 0}
  let Hm := HomologicalComplex.homologyMap
    (tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0} m twoPoint) 0
  let Hn := HomologicalComplex.homologyMap
    (tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0} n twoPoint) 0
  let H := HomologicalComplex.homologyMap
    (tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
      (TensorProduct.map m.toIntLinearMap n.toIntLinearMap).toAddMonoidHom
      twoPointProduct) 0
  have hv (c : ℤ) (i : Fin 2) :
      HomologicalComplex.homologyMap
          (tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
            (c • AddMonoidHom.id ℤ) twoPoint) 0 (twoPointH0Class.{0} i) =
        c • twoPointH0Class.{0} i := by
    have h := tensorNormalizedHomologyZeroCoefficientMap_class.{0, 0, 0, 0}
      (c • AddMonoidHom.id ℤ) twoPoint i (1 : ℤ)
    let v : ℤ →+ (tensorNormalizedChainComplex.{0, 0, 0} ℤ twoPoint).homology 0 :=
      { toFun := fun x ↦
          (tensorNormalizedChainComplex.{0, 0, 0} ℤ twoPoint).homologyπ₀
            (ULift.up (twoPoint.normalizedIntegralSimplex i ⊗ₜ[ℤ] x))
        map_zero' := by
          rw [TensorProduct.tmul_zero]
          exact (tensorNormalizedChainComplex.{0, 0, 0} ℤ twoPoint).homologyπ₀.hom.map_zero
        map_add' := by
          intro x y
          rw [TensorProduct.tmul_add]
          exact (tensorNormalizedChainComplex.{0, 0, 0} ℤ twoPoint).homologyπ₀.hom.map_add
            (ULift.up (twoPoint.normalizedIntegralSimplex i ⊗ₜ[ℤ] x))
            (ULift.up (twoPoint.normalizedIntegralSimplex i ⊗ₜ[ℤ] y)) }
    exact h.trans (map_zsmul v c (1 : ℤ))
  have hs : E.hom (twoPointSourceClass.{0, 0} q) = twoPointTargetClass.{0} q :=
    tensorNormalizedHomologyZeroProductIso_hom_class.{0, 0, 0, 0, 0, 0}
      ℤ ℤ twoPoint twoPoint q.1 q.2 1 1
  have hscale : E.hom
      (((2 : ℤ) • twoPointH0Class.{0} q.1) ⊗ₜ[ℤ]
        ((3 : ℤ) • twoPointH0Class.{0} q.2)) =
      (6 : ℤ) • twoPointTargetClass.{0} q := by
    let M := (tensorNormalizedChainComplex.{0, 0, 0} ℤ twoPoint).homology 0
    -- Integer multiplication is preserved by these additive maps in each factor.
    let u : M →+ (tensorNormalizedChainComplex.{0, 0, 0}
        (ℤ ⊗[ℤ] ℤ) twoPointProduct).homology 0 :=
      { toFun := fun x ↦ E.hom (x ⊗ₜ[ℤ] ((3 : ℤ) • twoPointH0Class.{0} q.2))
        map_zero' := by
          rw [TensorProduct.zero_tmul]
          exact E.hom.hom.map_zero
        map_add' := by
          intro x y
          rw [TensorProduct.add_tmul]
          exact E.hom.hom.map_add _ _ }
    let v : M →+ (tensorNormalizedChainComplex.{0, 0, 0}
        (ℤ ⊗[ℤ] ℤ) twoPointProduct).homology 0 :=
      { toFun := fun y ↦ E.hom (twoPointH0Class.{0} q.1 ⊗ₜ[ℤ] y)
        map_zero' := by
          rw [TensorProduct.tmul_zero]
          exact E.hom.hom.map_zero
        map_add' := by
          intro x y
          rw [TensorProduct.tmul_add]
          exact E.hom.hom.map_add _ _ }
    have hu := map_zsmul u (2 : ℤ) (twoPointH0Class.{0} q.1)
    have hv := map_zsmul v (3 : ℤ) (twoPointH0Class.{0} q.2)
    refine hu.trans ((congrArg (fun z ↦ (2 : ℤ) • z) hv).trans ?_)
    exact (mul_zsmul (E.hom (twoPointSourceClass.{0, 0} q)) (2 : ℤ) 3).symm.trans
      (congrArg (fun z ↦ (6 : ℤ) • z) hs)
  have e := ConcreteCategory.congr_hom
    (tensorNormalizedHomologyZeroProductIso_hom_coefficient_naturality.{0, 0, 0, 0, 0, 0, 0, 0}
      m n twoPoint twoPoint)
    (twoPointSourceClass.{0, 0} q)
  change E.hom (TensorProduct.map Hm.hom Hn.hom
      (twoPointH0Class.{0} q.1 ⊗ₜ[ℤ] twoPointH0Class.{0} q.2)) =
    H (E.hom (twoPointSourceClass.{0, 0} q)) at e
  rw [TensorProduct.map_tmul] at e
  exact (congrArg (fun z => H z) hs.symm).trans
    (e.symm.trans ((congrArg (fun z => E.hom z)
      (congrArg₂ (fun s t => s ⊗ₜ[ℤ] t) (hv 2 q.1) (hv 3 q.2))).trans hscale))

end SimplicialObjectsTest
