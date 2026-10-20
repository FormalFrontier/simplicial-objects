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
Both the direct action and singular-simplex postcomposition allow different
source and target universes. `TopCat.toSSetPostcomp` is defined on the lifted
topological simplices, and `TopCat.toSSetMapπ₀` descends it through singular edges.
`TopCat.zerothHomotopyEquiv_postcomp_naturality` and its inverse version give
the comparison squares without identifying the two universes.

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

open CategoryTheory Convexity

open scoped Simplicial

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

section Postcomposition

variable {X : TopCat.{u}} {Y : TopCat.{v}} {Z : TopCat.{t}}

/-- Postcomposition of singular simplices by a continuous map, allowing the
source and target spaces to lie in different universes. -/
noncomputable def toSSetPostcomp (f : C(X, Y)) (n : SimplexCategoryᵒᵖ)
    (a : (toSSet.obj X).obj n) : (toSSet.obj Y).obj n :=
  ULift.up (ofHom
    (⟨fun z => f (a.down.hom (ULift.up z.down)),
      f.continuous.comp (a.down.hom.continuous.comp
        (continuous_uliftUp.comp continuous_uliftDown))⟩ :
      C(ULift.{v} (StdSimplex ℝ (Fin (n.unop.len + 1))), Y)))

/-- Evaluation on the lifted topological simplex. -/
@[simp]
lemma toSSetPostcomp_apply (f : C(X, Y)) (n : SimplexCategoryᵒᵖ)
    (a : (toSSet.obj X).obj n)
    (z : ULift.{v} (StdSimplex ℝ (Fin (n.unop.len + 1)))) :
    ConcreteCategory.hom (X := SimplexCategory.toTop.{v}.obj n.unop) (Y := Y)
      (toSSetPostcomp f n a).down z = f (a.down.hom (ULift.up z.down)) :=
  rfl

/-- The simplex encoding intertwines postcomposition with continuous-map composition. -/
@[simp]
lemma toSSetObjEquiv_postcomp (f : C(X, Y)) (n : SimplexCategoryᵒᵖ)
    (a : (toSSet.obj X).obj n) :
    toSSetObjEquiv Y n (toSSetPostcomp f n a) =
      f.comp (toSSetObjEquiv X n a) :=
  rfl

/-- Postcomposition can also be computed in the continuous-map encoding. -/
lemma toSSetPostcomp_eq (f : C(X, Y)) (n : SimplexCategoryᵒᵖ)
    (a : (toSSet.obj X).obj n) :
    toSSetPostcomp f n a =
      (toSSetObjEquiv Y n).symm (f.comp (toSSetObjEquiv X n a)) := by
  apply (toSSetObjEquiv Y n).injective
  simp only [toSSetObjEquiv_postcomp, Equiv.apply_symm_apply]

/-- Postcomposition commutes with every simplicial operator. -/
lemma toSSetPostcomp_naturality (f : C(X, Y)) {n m : SimplexCategory}
    (α : n ⟶ m) (a : (toSSet.obj X).obj (Opposite.op m)) :
    (toSSet.obj Y).map α.op (toSSetPostcomp f _ a) =
      toSSetPostcomp f _ ((toSSet.obj X).map α.op a) := by
  apply ULift.ext
  apply TopCat.ext
  intro z
  rfl

/-- Face maps commute with postcomposition. -/
@[simp]
lemma toSSetPostcomp_δ (f : C(X, Y)) {n : ℕ}
    (i : Fin (n + 2)) (a : (toSSet.obj X) _⦋n + 1⦌) :
    (toSSet.obj Y).δ i (toSSetPostcomp f _ a) =
      toSSetPostcomp f _ ((toSSet.obj X).δ i a) :=
  toSSetPostcomp_naturality f (SimplexCategory.δ i) a

/-- Degeneracy maps commute with postcomposition. -/
@[simp]
lemma toSSetPostcomp_σ (f : C(X, Y)) {n : ℕ}
    (i : Fin (n + 1)) (a : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj Y).σ i (toSSetPostcomp f _ a) =
      toSSetPostcomp f _ ((toSSet.obj X).σ i a) :=
  toSSetPostcomp_naturality f (SimplexCategory.σ i) a

/-- The identity map fixes every singular simplex. -/
@[simp]
lemma toSSetPostcomp_id (n : SimplexCategoryᵒᵖ) (a : (toSSet.obj X).obj n) :
    toSSetPostcomp (ContinuousMap.id X) n a = a := by
  apply ULift.ext
  apply TopCat.ext
  intro z
  rfl

/-- Successive postcompositions agree with postcomposition by the composite. -/
@[simp]
lemma toSSetPostcomp_comp (f : C(X, Y)) (g : C(Y, Z))
    (n : SimplexCategoryᵒᵖ) (a : (toSSet.obj X).obj n) :
    toSSetPostcomp (g.comp f) n a =
      toSSetPostcomp g n (toSSetPostcomp f n a) := by
  apply ULift.ext
  apply TopCat.ext
  intro z
  rfl

/-- On a fixed universe, postcomposition is the singular functor's map. -/
lemma toSSetPostcomp_eq_map {Y : TopCat.{u}} (f : C(X, Y))
    (n : SimplexCategoryᵒᵖ) (a : (toSSet.obj X).obj n) :
    toSSetPostcomp f n a = (toSSet.map (ofHom f)).app n a := by
  apply ULift.ext
  apply TopCat.ext
  intro z
  rfl

/-- A constant singular vertex is sent to the vertex of its image point. -/
@[simp]
lemma toSSetPostcomp_vertex (f : C(X, Y)) (x : X) :
    toSSetPostcomp f _ (toSSetObj₀Equiv.symm x) =
      toSSetObj₀Equiv.symm (f x) := by
  apply (toSSetObjEquiv Y _).injective
  ext d
  rfl

/-- Evaluation of a vertex after postcomposition. -/
@[simp]
lemma toSSetObj₀Equiv_postcomp (f : C(X, Y)) (a : (toSSet.obj X) _⦋0⦌) :
    toSSetObj₀Equiv (toSSetPostcomp f _ a) = f (toSSetObj₀Equiv a) :=
  rfl

/-- An edge is sent to the edge obtained by postcomposing its singular simplex. -/
noncomputable def toSSetPostcompEdge (f : C(X, Y))
    {a b : (toSSet.obj X) _⦋0⦌} (e : (toSSet.obj X).Edge a b) :
    (toSSet.obj Y).Edge (toSSetPostcomp f _ a) (toSSetPostcomp f _ b) :=
  SSet.Edge.mk (toSSetPostcomp f _ e.edge)
    (by rw [toSSetPostcomp_δ, e.src_eq])
    (by rw [toSSetPostcomp_δ, e.tgt_eq])

/-- The underlying simplex of the postcomposed edge. -/
@[simp]
lemma toSSetPostcompEdge_edge (f : C(X, Y))
    {a b : (toSSet.obj X) _⦋0⦌} (e : (toSSet.obj X).Edge a b) :
    (toSSetPostcompEdge f e).edge = toSSetPostcomp f _ e.edge :=
  rfl

/-- Postcomposition on singular components, descended from vertices and edges. -/
noncomputable def toSSetMapπ₀ (f : C(X, Y)) :
    (toSSet.obj X).π₀ → (toSSet.obj Y).π₀ :=
  SSet.π₀.lift (fun a => SSet.π₀.mk (toSSetPostcomp f _ a))
    (fun _ _ e => SSet.π₀.sound (toSSetPostcompEdge f e))

/-- The action on the component represented by a singular vertex. -/
@[simp]
lemma toSSetMapπ₀_mk (f : C(X, Y)) (a : (toSSet.obj X) _⦋0⦌) :
    toSSetMapπ₀ f (SSet.π₀.mk a) = SSet.π₀.mk (toSSetPostcomp f _ a) :=
  rfl

/-- The action is determined by its values on singular vertices. -/
lemma toSSetMapπ₀_unique (f : C(X, Y))
    (g : (toSSet.obj X).π₀ → (toSSet.obj Y).π₀)
    (h : ∀ a, g (SSet.π₀.mk a) = SSet.π₀.mk (toSSetPostcomp f _ a)) :
    g = toSSetMapπ₀ f := by
  funext c
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective c
  exact h a

/-- The identity map fixes singular components. -/
@[simp]
lemma toSSetMapπ₀_id : toSSetMapπ₀ (ContinuousMap.id X) = id := by
  funext c
  induction c using SSet.π₀.rec with
  | mk a => simp only [toSSetMapπ₀_mk, toSSetPostcomp_id, id_eq]

/-- The singular-component action respects composition across universes. -/
@[simp]
lemma toSSetMapπ₀_comp (f : C(X, Y)) (g : C(Y, Z)) :
    toSSetMapπ₀ (g.comp f) = toSSetMapπ₀ g ∘ toSSetMapπ₀ f := by
  funext c
  induction c using SSet.π₀.rec with
  | mk a => simp only [toSSetMapπ₀_mk, toSSetPostcomp_comp, Function.comp_apply]

/-- On a fixed universe this agrees with the action of the singular functor on components. -/
lemma toSSetMapπ₀_eq_mapπ₀ {Y : TopCat.{u}} (f : C(X, Y)) :
    toSSetMapπ₀ f = SSet.mapπ₀ (toSSet.map (ofHom f)) := by
  symm
  apply toSSetMapπ₀_unique
  intro a
  simp only [SSet.mapπ₀_mk, toSSetPostcomp_eq_map]

/-- The continuous-map encoding yields the same descended component action. -/
lemma toSSetMapπ₀_eq_lift (f : C(X, Y)) :
    toSSetMapπ₀ f = SSet.π₀.lift
      (fun a => SSet.π₀.mk ((toSSetObjEquiv Y _).symm
        (f.comp (toSSetObjEquiv X _ a))))
      (fun _ _ e => by
        simpa only [← toSSetPostcomp_eq] using
          SSet.π₀.sound (toSSetPostcompEdge f e)) := by
  symm
  apply toSSetMapπ₀_unique
  intro a
  simp only [SSet.π₀.lift_mk, ← toSSetPostcomp_eq]

/-- Decoding a singular edge gives a path on the ordinary unit interval.

The two inverse homeomorphisms convert the interval parameter to a point of
its topological simplex before evaluating the singular simplex. -/
lemma toSSetObjEdgeEquiv_path_apply {x y : X}
    (e : (toSSet.obj X).Edge (toSSetObj₀Equiv.symm x) (toSSetObj₀Equiv.symm y))
    (r : unitInterval) :
    pathEquiv (toSSetObjEdgeEquiv e) r =
      toSSetObjEquiv X _ e.edge
        (stdSimplexHomeomorphI.{u}.symm (I.homeomorph.{u}.symm r)) :=
  rfl

/-- Joined points have image vertices in the same singular component. -/
lemma toSSetPostcomp_joined (f : C(X, Y)) {x y : X} (h : Joined x y) :
    SSet.π₀.mk ((toSSetObj₀Equiv (X := Y)).symm (f x)) =
      SSet.π₀.mk ((toSSetObj₀Equiv (X := Y)).symm (f y)) := by
  obtain ⟨p⟩ := h
  exact SSet.π₀.sound (toSSetObjEdgeEquiv.symm (pathEquiv.symm (p.map f.continuous)))

/-- The endpoints of a singular edge have image points in the same path component. -/
lemma toSSetPostcomp_edge_sound (f : C(X, Y))
    {a b : (toSSet.obj X) _⦋0⦌} (e : (toSSet.obj X).Edge a b) :
    ZerothHomotopy.mk (f (toSSetObj₀Equiv a)) =
      ZerothHomotopy.mk (f (toSSetObj₀Equiv b)) := by
  obtain ⟨x, rfl⟩ := toSSetObj₀Equiv.symm.surjective a
  obtain ⟨y, rfl⟩ := toSSetObj₀Equiv.symm.surjective b
  simpa only [Equiv.apply_symm_apply] using
    ZerothHomotopy.sound ((pathEquiv (toSSetObjEdgeEquiv e)).map f.continuous)

/-- The comparison with singular components commutes with continuous maps
between spaces in independent universes. -/
lemma zerothHomotopyEquiv_postcomp_naturality (f : C(X, Y)) :
    zerothHomotopyEquiv (X := Y) ∘ ZerothHomotopy.map f =
      toSSetMapπ₀ f ∘ zerothHomotopyEquiv (X := X) := by
  funext z
  induction z using ZerothHomotopy.rec with
  | mk x =>
    simp only [Function.comp_apply, ZerothHomotopy.map_mk,
      zerothHomotopyEquiv_mk, toSSetMapπ₀_mk, toSSetPostcomp_vertex]

/-- The inverse comparison also commutes with maps between independent universes. -/
lemma zerothHomotopyEquiv_symm_postcomp_naturality (f : C(X, Y)) :
    ZerothHomotopy.map f ∘ (zerothHomotopyEquiv (X := X)).symm =
      (zerothHomotopyEquiv (X := Y)).symm ∘ toSSetMapπ₀ f := by
  funext c
  apply (zerothHomotopyEquiv (X := Y)).injective
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    congrFun (zerothHomotopyEquiv_postcomp_naturality f)
      ((zerothHomotopyEquiv (X := X)).symm c)

/-- The forward square is the quotient recursor sending a point to its image vertex. -/
lemma toSSetMapπ₀_comp_zerothHomotopyEquiv (f : C(X, Y)) :
    toSSetMapπ₀ f ∘ zerothHomotopyEquiv (X := X) =
      Quotient.lift (fun x => SSet.π₀.mk (toSSetObj₀Equiv.symm (f x)))
        (fun _ _ h => toSSetPostcomp_joined f h) := by
  funext z
  induction z using ZerothHomotopy.rec with
  | mk x =>
    simp only [Function.comp_apply, zerothHomotopyEquiv_mk,
      toSSetMapπ₀_mk, toSSetPostcomp_vertex]; rfl

/-- The inverse square is the edge-descended recursor on singular vertices. -/
lemma zerothHomotopyEquiv_symm_comp_toSSetMapπ₀ (f : C(X, Y)) :
    (zerothHomotopyEquiv (X := Y)).symm ∘ toSSetMapπ₀ f =
      SSet.π₀.lift (fun a => ZerothHomotopy.mk (f (toSSetObj₀Equiv a)))
        (fun _ _ e => toSSetPostcomp_edge_sound f e) := by
  funext c
  induction c using SSet.π₀.rec with
  | mk a =>
    simp only [Function.comp_apply, toSSetMapπ₀_mk, zerothHomotopyEquiv_symm_mk,
      toSSetObj₀Equiv_postcomp, SSet.π₀.lift_mk]

end Postcomposition

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
    ConcreteCategory.hom (X := ZerothHomotopy X) (Y := ZerothHomotopy Y)
      (zerothHomotopyFunctor.map f) z = ZerothHomotopy.map f.hom z :=
  rfl

/-- Mathlib's singular-component equivalence commutes with every continuous map.

The proof uses Joël Riou's representative formula for `zerothHomotopyEquiv`,
`SSet.mapπ₀_mk`, and the singular vertex identification from Mathlib's `TopAdj`.
-/
lemma zerothHomotopyEquiv_naturality {X Y : TopCat.{w}} (f : C(X, Y))
    (z : ZerothHomotopy X) :
    zerothHomotopyEquiv (ZerothHomotopy.map f z) =
      SSet.mapπ₀ (toSSet.map (ofHom f)) (zerothHomotopyEquiv z) := by
  simpa only [Function.comp_apply, toSSetMapπ₀_eq_mapπ₀] using
    congrFun (zerothHomotopyEquiv_postcomp_naturality f) z

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
    ConcreteCategory.hom (X := ZerothHomotopy X)
      (Y := SSet.π₀Functor.obj (toSSet.obj X))
      (zerothHomotopyIso.hom.app X) z = zerothHomotopyEquiv z :=
  rfl

/-- Evaluation of the inverse comparison on a singular component. -/
@[simp]
lemma zerothHomotopyIso_inv_app_apply (X : TopCat.{w}) (z : (toSSet.obj X).π₀) :
    ConcreteCategory.hom (X := SSet.π₀Functor.obj (toSSet.obj X))
      (Y := ZerothHomotopy X)
      (zerothHomotopyIso.inv.app X) z = zerothHomotopyEquiv.symm z :=
  rfl

/-- The inverse singular-component equivalence commutes with continuous maps. -/
lemma zerothHomotopyEquiv_symm_naturality {X Y : TopCat.{w}} (f : C(X, Y))
    (z : (toSSet.obj X).π₀) :
    ZerothHomotopy.map f (zerothHomotopyEquiv.symm z) =
      zerothHomotopyEquiv.symm (SSet.mapπ₀ (toSSet.map (ofHom f)) z) :=
  (ConcreteCategory.congr_hom (zerothHomotopyIso.inv.naturality (ofHom f)) z).symm

end TopCat
