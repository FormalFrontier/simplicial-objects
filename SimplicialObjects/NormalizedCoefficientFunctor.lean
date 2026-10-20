/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.Normalization
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.ULift

/-!
# Coefficients in normalized simplicial chains

`SSet.normalizedChainComplexFunctor` packages normalized chains as a functor in
both the coefficient object and the simplicial set. Its objects are Mathlib's
`SSet.normalizedChainComplexFunctorObj`; coefficient morphisms act by
`CategoryTheory.SimplicialObject.Splitting.nondegComplexMap` on the corresponding
coefficient-valued simplicial morphisms. Simplicial maps need not preserve the
chosen nondegenerate summands.

`AddCommGrpCat.uliftIntModuleFunctor` sends an abelian group to its universe lift
with the canonical integer-module structure. It sends a lifted element to the
lift of its image under the coefficient homomorphism.

## References

* Mathlib's normalized simplicial chains and split simplicial objects supply the
  fixed-coefficient objects and simplicial maps.
* `SimplicialObjects.Normalization` supplies normalized maps for arbitrary
  coefficient-valued simplicial morphisms.
* Mathlib's `ModuleCat.uliftFunctor`, by Nailin Guan, supplies the ULift
  conjugation approach to module morphisms; `AddMonoidHom.toIntLinearMap` uses
  the canonical integer actions of abelian groups. Mathlib is separately licensed
  under Apache-2.0.
-/

@[expose] public section

universe w v u a q

open CategoryTheory Limits

namespace SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Normalized simplicial chains, functorial in the coefficient object and in all
simplicial maps, in a preadditive category with the required coproducts. -/
noncomputable def normalizedChainComplexFunctor :
    C ⥤ (SSet.{w} ⥤ ChainComplex C ℕ) where
  obj R := normalizedChainComplexFunctorObj R
  map {R R'} g :=
    { app S :=
        (S.splitting.map (sigmaConst.obj R)).nondegComplexMap
          (S.splitting.map (sigmaConst.obj R'))
          (Functor.whiskerLeft S (sigmaConst.map g))
      naturality S T f := by
        have h :
            (S.splitting.map (sigmaConst.obj R)).nondegComplexMap
                (T.splitting.map (sigmaConst.obj R))
                (Functor.whiskerRight f (sigmaConst.obj R)) ≫
              (T.splitting.map (sigmaConst.obj R)).nondegComplexMap
                (T.splitting.map (sigmaConst.obj R'))
                (Functor.whiskerLeft T (sigmaConst.map g)) =
            (S.splitting.map (sigmaConst.obj R)).nondegComplexMap
                (S.splitting.map (sigmaConst.obj R'))
                (Functor.whiskerLeft S (sigmaConst.map g)) ≫
              (S.splitting.map (sigmaConst.obj R')).nondegComplexMap
                (T.splitting.map (sigmaConst.obj R'))
                (Functor.whiskerRight f (sigmaConst.obj R')) := by
          rw [← SimplicialObject.Splitting.nondegComplexMap_comp,
            ← SimplicialObject.Splitting.nondegComplexMap_comp,
            ← Functor.whiskerLeft_comp_whiskerRight]
        change normalizedChainComplexMap f R ≫ _ = _ ≫ normalizedChainComplexMap f R'
        exact
          (congrArg
            (fun k : S.normalizedChainComplex R ⟶ T.normalizedChainComplex R =>
              k ≫ (T.splitting.map (sigmaConst.obj R)).nondegComplexMap
                (T.splitting.map (sigmaConst.obj R'))
                (Functor.whiskerLeft T (sigmaConst.map g)))
            (nondegComplexMap_eq_normalizedChainComplexMap f R).symm).trans
            (h.trans
              (congrArg
                (fun k : S.normalizedChainComplex R' ⟶ T.normalizedChainComplex R' =>
                  (S.splitting.map (sigmaConst.obj R)).nondegComplexMap
                      (S.splitting.map (sigmaConst.obj R'))
                      (Functor.whiskerLeft S (sigmaConst.map g)) ≫ k)
                (nondegComplexMap_eq_normalizedChainComplexMap f R'))) }
  map_id R := by
    apply NatTrans.ext
    funext S
    change
      (S.splitting.map (sigmaConst.obj R)).nondegComplexMap
          (S.splitting.map (sigmaConst.obj R))
          (Functor.whiskerLeft S (sigmaConst.map (𝟙 R))) =
        𝟙 ((S.splitting.map (sigmaConst.obj R)).nondegComplex)
    rw [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id']
    exact (S.splitting.map (sigmaConst.obj R)).nondegComplexMap_id
  map_comp g h := by
    rename_i R R' R''
    apply NatTrans.ext
    funext S
    change
      (S.splitting.map (sigmaConst.obj R)).nondegComplexMap
          (S.splitting.map (sigmaConst.obj R''))
          (Functor.whiskerLeft S (sigmaConst.map (g ≫ h))) =
        (S.splitting.map (sigmaConst.obj R)).nondegComplexMap
            (S.splitting.map (sigmaConst.obj R'))
            (Functor.whiskerLeft S (sigmaConst.map g)) ≫
          (S.splitting.map (sigmaConst.obj R')).nondegComplexMap
            (S.splitting.map (sigmaConst.obj R''))
            (Functor.whiskerLeft S (sigmaConst.map h))
    rw [Functor.map_comp, Functor.whiskerLeft_comp,
      SimplicialObject.Splitting.nondegComplexMap_comp]

/-- Fixing the coefficient recovers Mathlib's normalized-chain functor. -/
@[simp]
theorem normalizedChainComplexFunctor_obj (R : C) :
    (normalizedChainComplexFunctor.{w, v, u} (C := C)).obj R =
      normalizedChainComplexFunctorObj.{w, v, u} (C := C) R := rfl

/-- Coefficient morphisms act by the normalized map of the whiskered coefficient
transformation. -/
@[simp]
theorem normalizedChainComplexFunctor_map_app {R R' : C} (g : R ⟶ R')
    (S : SSet.{w}) :
    ((normalizedChainComplexFunctor.{w, v, u} (C := C)).map g).app S =
      (S.splitting.map (sigmaConst.obj R)).nondegComplexMap
        (S.splitting.map (sigmaConst.obj R'))
        (Functor.whiskerLeft S (sigmaConst.map g)) := rfl

end SSet

namespace AddCommGrpCat

/-- Lift an abelian group to a universe-lifted module with its canonical integer
action; morphisms are the conjugates of their canonical integer-linear maps. -/
noncomputable def uliftIntModuleFunctor :
    AddCommGrpCat.{a} ⥤ ModuleCat.{max a q} ℤ where
  obj A := ModuleCat.of ℤ (ULift.{q} A)
  map g := ModuleCat.ofHom
    ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
      g.hom.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap)
  map_id A := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    cases x
    rfl
  map_comp g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    cases x
    rfl

/-- The lifted coefficient object carries the canonical integer-module structure. -/
@[simp]
theorem uliftIntModuleFunctor_obj (A : AddCommGrpCat.{a}) :
    (uliftIntModuleFunctor.{a, q}).obj A = ModuleCat.of ℤ (ULift.{q} A) := rfl

/-- A lifted element is sent to the lift of its coefficient image. -/
@[simp]
theorem uliftIntModuleFunctor_map_up {A B : AddCommGrpCat.{a}} (g : A ⟶ B) (x : A) :
    ConcreteCategory.hom (X := ModuleCat.of ℤ (ULift.{q} A))
      (Y := ModuleCat.of ℤ (ULift.{q} B)) (uliftIntModuleFunctor.{a, q}.map g)
      (ULift.up x) = ULift.up (g.hom x) := rfl

end AddCommGrpCat
