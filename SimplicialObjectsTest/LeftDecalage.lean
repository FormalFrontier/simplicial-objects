/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects.LeftDecalage
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

@[expose] public section

open CategoryTheory Category Opposite SimplicialObjects.LeftDecalage
open scoped Simplicial

namespace SimplicialObjectsTest.LeftDecalage

private theorem generic_degree_zero {C : Type*} [Category* C] (X : SimplicialObject C) :
    (augmented X).left _⦋0⦌ = X _⦋1⦌ := path_obj X 0

private theorem generic_boundaries {C : Type*} [Category* C] (X : SimplicialObject C) :
    (augmented X).hom.app (op ⦋0⦌) = X.δ (1 : Fin 2) ∧
      (projection X).app (op ⦋0⦌) = X.δ (0 : Fin 2) :=
  ⟨augmentation_zero X, projection_zero X⟩

private def generic_extraDegeneracy {C : Type*} [Category* C] (X : SimplicialObject C) :
    SimplicialObject.Augmented.ExtraDegeneracy (augmented X) := extraDegeneracy X

private def generic_section {C : Type*} [Category* C] (X : SimplicialObject C) :
    (SimplicialObject.const C).obj (X _⦋0⦌) ⟶ (augmented X).left :=
  (extraDegeneracy X).section_

private theorem generic_section_identity {C : Type*} [Category* C]
    (X : SimplicialObject C) :
    generic_section X ≫ (augmented X).hom = 𝟙 _ :=
  (extraDegeneracy X).section_comp_hom

private def generic_homotopy {C : Type*} [Category* C] (X : SimplicialObject C) :
    SimplicialObject.Homotopy
      ((augmented X).hom ≫ (extraDegeneracy X).section_) (𝟙 (augmented X).left) :=
  (extraDegeneracy X).homotopy

private def transported_extraDegeneracy {C D : Type*} [Category* C] [Category* D]
    (X : SimplicialObject C) (targetFunctor : C ⥤ D) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (((SimplicialObject.Augmented.whiskering C D).obj targetFunctor).obj (augmented X)) :=
  (extraDegeneracy X).map targetFunctor

private theorem generic_functoriality {C : Type*} [Category* C]
    {X Y : SimplicialObject C} (morphism : X ⟶ Y) (degree : ℕ) :
    ((functor C).map morphism).left.app (op ⦋degree⦌) =
        morphism.app (op ⦋degree + 1⦌) ∧
      ((functor C).map morphism).right = morphism.app (op ⦋0⦌) :=
  ⟨functor_map_left_app morphism degree, functor_map_right morphism⟩

private theorem generic_natural_projection {C : Type*} [Category* C]
    {X Y : SimplicialObject C} (morphism : X ⟶ Y) :
    ((functor C ⋙ SimplicialObject.Augmented.drop).map morphism) ≫ projection Y =
      projection X ≫ morphism :=
  (naturalProjection C).naturality morphism

private theorem generic_extra_naturality {C : Type*} [Category* C]
    {X Y : SimplicialObject C} (morphism : X ⟶ Y) (degree : ℕ) :
    (extraDegeneracy X).s' ≫ ((functor C).map morphism).left.app (op ⦋0⦌) =
        ((functor C).map morphism).right ≫ (extraDegeneracy Y).s' ∧
      (extraDegeneracy X).s degree ≫
          ((functor C).map morphism).left.app (op ⦋degree + 1⦌) =
        ((functor C).map morphism).left.app (op ⦋degree⦌) ≫
          (extraDegeneracy Y).s degree :=
  ⟨extraDegeneracy_s'_naturality morphism, extraDegeneracy_s_naturality morphism degree⟩

private def twoPointSSet : SSet := (SimplicialObject.const (Type)).obj Bool

private theorem nonterminal_augmentation_point :
    ¬ Subsingleton (augmented twoPointSSet).right := by
  change ¬ Subsingleton Bool
  intro pointSubsingleton
  have impossible : true = false := pointSubsingleton.elim true false
  cases impossible

private abbrev standardEdge : SSet := SSet.stdSimplex.obj ⦋1⦌

private theorem standardEdge_degree_zero :
    (augmented standardEdge).left _⦋0⦌ = standardEdge _⦋1⦌ := path_obj standardEdge 0

private theorem standardEdge_distinguishes_faces :
    (augmented standardEdge).hom.app (op ⦋0⦌) ≠
      (projection standardEdge).app (op ⦋0⦌) := by
  intro equality
  rw [augmentation_zero, projection_zero] at equality
  change standardEdge.δ (1 : Fin 2) = standardEdge.δ (0 : Fin 2) at equality
  let faceEquality := equality
  have valueEquality := congrArg
    (fun (arrow : standardEdge _⦋1⦌ ⟶ standardEdge _⦋0⦌) =>
      arrow (SSet.stdSimplex.objEquiv.symm (𝟙 (⦋1⦌ : SimplexCategory)))) faceEquality
  dsimp only [standardEdge] at valueEquality
  rw [SSet.stdSimplex.δ_objEquiv_symm_apply,
    SSet.stdSimplex.δ_objEquiv_symm_apply, Category.comp_id] at valueEquality
  have indexEquality :=
    (SSet.stdSimplex.objEquiv (n := ⦋1⦌) (m := op ⦋0⦌)).symm.injective valueEquality
  have different : (SimplexCategory.δ (1 : Fin 2) : ⦋0⦌ ⟶ ⦋1⦌) ≠
      SimplexCategory.δ 0 := by
    intro impossible
    have imageEquality := SimplexCategory.congr_toOrderHom_apply impossible (0 : Fin 1)
    simp [SimplexCategory.δ, Fin.succAbove] at imageEquality
  exact different indexEquality

end SimplicialObjectsTest.LeftDecalage
