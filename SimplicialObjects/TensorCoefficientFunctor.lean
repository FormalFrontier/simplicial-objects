/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorCoefficientMaps
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Coefficient functor for normalized integral tensor chains

The normalized tensor-chain functor is additively functorial in its abelian
coefficient group. Its objects are the fixed-coefficient functors
`SSet.tensorNormalizedChainComplexFunctor`, and its coefficient components are
`SSet.tensorNormalizedChainComplexCoefficientMap`. The tensor carriers and their
independently specified alternating differentials are unchanged.

The characteristic equations identify objects, simplicial maps, coefficient
components, and their raw degree maps. Together with the pure-tensor, generator,
every-simplex, uniqueness, and mixed-naturality equations of
`SimplicialObjects.TensorCoefficientMaps` and `SimplicialObjects.TensorMaps`, they
allow computations without unfolding the coefficient functor. The
`Functor.Additive` instance provides coefficient additivity through
`Functor.map_add` and Mathlib's other additive-functor laws.

## Implementation notes

The coefficient, simplex, and padding universes are independent. For coefficient
universe `a` and padding `p`, both the fixed-coefficient functor and coefficient
components use padding `max a p`. This gives a common target category and
specializes the balanced coefficient composition law to a single coefficient
universe. Only identity, composition, and mixed naturality enter the functor data.
Additivity is derived from raw coefficient additivity using the pointwise
preadditive structures on chain maps and natural transformations.

## References

* Mathlib supplies `AddCommGrpCat`, `Functor.Additive`, and the pointwise
  preadditive structures on chain complexes and functor categories.
* `SimplicialObjects.TensorMaps` supplies the fixed-coefficient tensor-chain
  functor; `SimplicialObjects.TensorCoefficientMaps` supplies the coefficient
  morphisms and their identity, composition, component, additivity, and naturality
  equations.
-/

@[expose] public section

universe a w p

open CategoryTheory

namespace SSet

/-- Normalized integral tensor chains, curried as a functor from abelian
coefficient groups to functors on simplicial sets. Both the fixed-coefficient
functor and coefficient components use the common padding `max a p`. -/
noncomputable def tensorNormalizedChainComplexCoefficientFunctor :
    AddCommGrpCat.{a} ⥤ (SSet.{w} ⥤ ChainComplex (ModuleCat.{max a w p} ℤ) ℕ) where
  obj A := tensorNormalizedChainComplexFunctor.{a, w, max a p} A
  map g :=
    { app S := tensorNormalizedChainComplexCoefficientMap.{a, a, w, max a p} g.hom S
      naturality S T f :=
        tensorNormalizedChainComplexCoefficientMap_naturality.{a, a, w, max a p} f g.hom }
  map_id A := by
    apply NatTrans.ext
    funext S
    exact tensorNormalizedChainComplexCoefficientMap_id.{a, w, max a p} (A := A) S
  map_comp g h := by
    apply NatTrans.ext
    funext S
    exact tensorNormalizedChainComplexCoefficientMap_comp.{a, a, a, w, p} g.hom h.hom S

/-- At a coefficient group, the coefficient functor is the fixed-coefficient
simplicial tensor-chain functor with common padding. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientFunctor_obj (A : AddCommGrpCat.{a}) :
    (tensorNormalizedChainComplexCoefficientFunctor.{a, w, p}).obj A =
      tensorNormalizedChainComplexFunctor.{a, w, max a p} A := rfl

/-- Evaluating at a coefficient group and a simplicial set gives the specified
tensor complex with its alternating differential. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientFunctor_obj_obj
    (A : AddCommGrpCat.{a}) (S : SSet.{w}) :
    ((tensorNormalizedChainComplexCoefficientFunctor.{a, w, p}).obj A).obj S =
      tensorNormalizedChainComplex.{a, w, max a p} A S :=
  tensorNormalizedChainComplexFunctor_obj.{a, w, max a p} A S

/-- Simplicial morphisms act by the existing tensor chain maps. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientFunctor_obj_map
    (A : AddCommGrpCat.{a}) {S T : SSet.{w}} (f : S ⟶ T) :
    ((tensorNormalizedChainComplexCoefficientFunctor.{a, w, p}).obj A).map f =
      tensorNormalizedChainComplexMap.{a, w, max a p} A f :=
  tensorNormalizedChainComplexFunctor_map.{a, w, max a p} A f

/-- The coefficient natural transformation has the balanced coefficient chain
map as its component at each simplicial set. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientFunctor_map_app
    {A B : AddCommGrpCat.{a}} (g : A ⟶ B) (S : SSet.{w}) :
    ((tensorNormalizedChainComplexCoefficientFunctor.{a, w, p}).map g).app S =
      tensorNormalizedChainComplexCoefficientMap.{a, a, w, max a p} g.hom S := rfl

/-- Each degree component is the raw tensor coefficient operation, so its
pure-tensor and simplex formulas apply directly. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientFunctor_map_app_f
    {A B : AddCommGrpCat.{a}} (g : A ⟶ B) (S : SSet.{w}) (n : ℕ) :
    (((tensorNormalizedChainComplexCoefficientFunctor.{a, w, p}).map g).app S).f n =
      tensorNormalizedCoefficientMap.{a, a, w, max a p} g.hom S n :=
  tensorNormalizedChainComplexCoefficientMap_f.{a, a, w, max a p} g.hom S n

/-- The coefficient-curried tensor-chain functor is additive. Addition of
coefficient morphisms is preserved degreewise on each simplicial set. -/
instance tensorNormalizedChainComplexCoefficientFunctor_additive :
    (tensorNormalizedChainComplexCoefficientFunctor.{a, w, p}).Additive where
  map_add {A B g h} := by
    apply NatTrans.ext
    funext S
    refine Eq.trans
      (tensorNormalizedChainComplexCoefficientFunctor_map_app.{a, w, p} (g + h) S) ?_
    simp only [AddCommGrpCat.hom_add]
    refine Eq.trans
      (tensorNormalizedChainComplexCoefficientMap_add.{a, a, w, max a p} g.hom h.hom S) ?_
    refine Eq.trans
      (congrArg₂ (· + ·)
        (tensorNormalizedChainComplexCoefficientFunctor_map_app.{a, w, p} g S).symm
        (tensorNormalizedChainComplexCoefficientFunctor_map_app.{a, w, p} h S).symm) ?_
    exact (NatTrans.app_add S
      ((tensorNormalizedChainComplexCoefficientFunctor.{a, w, p}).map g)
      ((tensorNormalizedChainComplexCoefficientFunctor.{a, w, p}).map h)).symm

end SSet
