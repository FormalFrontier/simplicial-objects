/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

/-!
# Path components and singular components

Continuous maps act directly on Mathlib's `ZerothHomotopy`, the quotient by `Joined`.
`TopCat.zerothHomotopyFunctor` packages this action at a fixed universe, and
`TopCat.zerothHomotopyIso` identifies it naturally with singular simplicial components.
The direct action itself allows different source and target universes.

The representative API uses the existing `ZerothHomotopy.mk`, `rec`, `mk_surjective`,
and `lift`; no additional quotient or descent construction is needed. Naturality
squares are available through `TopCat.zerothHomotopyIso.hom.naturality` and
`TopCat.zerothHomotopyIso.inv.naturality`.

## References

This construction uses Mathlib's `Quotient.map` and `Joined.map` approach and
Joël Riou's `TopCat.zerothHomotopyEquiv`, together with `SSet.mapπ₀` and
`SSet.π₀Functor`. See Mathlib
[83abb3e776bdefcbc447a1e44d0debe4010039e5](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5),
particularly `Topology/Connected/PathConnected.lean`, `Data/Quot.lean`,
`Topology/Homotopy/TopCat/ZerothHomotopy.lean`, and
`AlgebraicTopology/SimplicialSet/{PiZero,TopAdj}.lean`.
-/

@[expose] public section

open CategoryTheory

universe u v t w

namespace ZerothHomotopy

/-- A continuous map acts on path components by mapping representatives. -/
def map {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : ZerothHomotopy X → ZerothHomotopy Y :=
  Quotient.map (fun x => f x) (fun _ _ h => Joined.map h f.continuous)

/-- The action on the path component of a point. -/
@[simp]
lemma map_mk {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : map f (mk x) = mk (f x) :=
  rfl

/-- The identity continuous map fixes every path component. -/
@[simp]
lemma map_id_apply {X : Type u} [TopologicalSpace X] (z : ZerothHomotopy X) :
    map (ContinuousMap.id X) z = z :=
  ZerothHomotopy.rec (fun _ => rfl) z

/-- The action respects composition, with independent space universes. -/
@[simp]
lemma map_comp_apply {X : Type u} {Y : Type v} {Z : Type t}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (z : ZerothHomotopy X) :
    map (g.comp f) z = map g (map f z) :=
  ZerothHomotopy.rec (fun _ => rfl) z

end ZerothHomotopy

namespace TopCat

/-- The functor sending a space to its set of path components. -/
def zerothHomotopyFunctor : TopCat.{w} ⥤ Type w where
  obj X := ZerothHomotopy X
  map f := TypeCat.ofHom (ZerothHomotopy.map f.hom)
  map_id _X := ConcreteCategory.hom_ext _ _ (fun z => ZerothHomotopy.map_id_apply z)
  map_comp f g :=
    ConcreteCategory.hom_ext _ _ (fun z => ZerothHomotopy.map_comp_apply f.hom g.hom z)

/-- Object evaluation for the path-component functor. -/
@[simp]
lemma zerothHomotopyFunctor_obj (X : TopCat.{w}) :
    zerothHomotopyFunctor.obj X = ZerothHomotopy X :=
  rfl

/-- Map evaluation for the path-component functor. -/
@[simp]
lemma zerothHomotopyFunctor_map_apply {X Y : TopCat.{w}} (f : X ⟶ Y)
    (z : ZerothHomotopy X) :
    ConcreteCategory.hom (zerothHomotopyFunctor.map f) z = ZerothHomotopy.map f.hom z :=
  rfl

/-- Mathlib's singular-component equivalence commutes with every continuous map.

The proof uses Joël Riou's representative formula for `zerothHomotopyEquiv`,
`SSet.mapπ₀_mk`, and the singular vertex identification from Mathlib's `TopAdj`.
-/
lemma zerothHomotopyEquiv_naturality {X Y : TopCat.{w}} (f : C(X, Y))
    (z : ZerothHomotopy X) :
    zerothHomotopyEquiv (ZerothHomotopy.map f z) =
      SSet.mapπ₀ (toSSet.map (ofHom f)) (zerothHomotopyEquiv z) := by
  induction z using ZerothHomotopy.rec with
  | mk x =>
    rw [ZerothHomotopy.map_mk, zerothHomotopyEquiv_mk,
      zerothHomotopyEquiv_mk, SSet.mapπ₀_mk]
    apply congrArg SSet.π₀.mk
    apply toSSetObj₀Equiv.injective
    rfl

/-- Path components are naturally isomorphic to singular simplicial components.

Each component is exactly `(TopCat.zerothHomotopyEquiv (X := X)).toIso`, oriented
from topological path components to singular components. This packages Joël Riou's
Mathlib equivalence and its quotient/`Joined`/`π₀` representative formulas; see the
Mathlib source references in the module documentation.
-/
noncomputable def zerothHomotopyIso :
    zerothHomotopyFunctor.{w} ≅ toSSet ⋙ SSet.π₀Functor :=
  NatIso.ofComponents (fun X => (zerothHomotopyEquiv (X := X)).toIso)
    (fun f => ConcreteCategory.hom_ext _ _ (fun z =>
      zerothHomotopyEquiv_naturality f.hom z))

/-- Evaluation of the forward comparison on a path component. -/
@[simp]
lemma zerothHomotopyIso_hom_app_apply (X : TopCat.{w}) (z : ZerothHomotopy X) :
    zerothHomotopyIso.hom.app X z = zerothHomotopyEquiv z :=
  rfl

/-- Evaluation of the inverse comparison on a singular component. -/
@[simp]
lemma zerothHomotopyIso_inv_app_apply (X : TopCat.{w}) (z : (toSSet.obj X).π₀) :
    zerothHomotopyIso.inv.app X z = zerothHomotopyEquiv.symm z :=
  rfl

/-- The inverse singular-component equivalence commutes with continuous maps. -/
lemma zerothHomotopyEquiv_symm_naturality {X Y : TopCat.{w}} (f : C(X, Y))
    (z : (toSSet.obj X).π₀) :
    ZerothHomotopy.map f (zerothHomotopyEquiv.symm z) =
      zerothHomotopyEquiv.symm (SSet.mapπ₀ (toSSet.map (ofHom f)) z) :=
  (ConcreteCategory.congr_hom (zerothHomotopyIso.inv.naturality (ofHom f)) z).symm

end TopCat
