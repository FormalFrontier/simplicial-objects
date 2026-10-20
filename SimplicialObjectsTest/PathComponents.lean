/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects.PathComponents
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order

/-!
# A transposition of two path components

The stock topology on `Fin 2` is discrete. Its transposition exchanges two distinct
path components, whose images under `TopCat.zerothHomotopyIso` remain distinct.
The naturality square computes the action on the corresponding singular components.
Negation on independently lifted copies of discrete `Bool` also acts on singular
simplices and components, exchanging both classes. Empty sources supply the boundary
case in every singular degree and for both component quotients.

## References

The separation proofs use Mathlib's `PreconnectedSpace.constant` and
`TotallyDisconnectedSpace.eq_of_continuous`: a path into a discrete space has equal
endpoints. See Mathlib
[83abb3e776bdefcbc447a1e44d0debe4010039e5](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Connected/TotallyDisconnected.lean).
-/

open CategoryTheory Convexity

namespace TopCat.PathComponentsExamples

/-- The continuous transposition of the discrete two-point space. -/
private def twoPointSwap : C(Fin 2, Fin 2) where
  toFun i := if i = 0 then 1 else 0
  continuous_toFun := continuous_of_discreteTopology

/-- The transposition sends zero to one. -/
@[simp]
private lemma twoPointSwap_zero : twoPointSwap 0 = 1 := by
  simp [twoPointSwap]

/-- The transposition sends one to zero. -/
@[simp]
private lemma twoPointSwap_one : twoPointSwap 1 = 0 := by
  simp [twoPointSwap]

/-- The two points of the discrete two-point space have distinct path classes. -/
private lemma twoPoint_classes_ne :
    ZerothHomotopy.mk (0 : Fin 2) ≠ ZerothHomotopy.mk (1 : Fin 2) := by
  intro h
  obtain ⟨p⟩ := (Quotient.exact h : Joined (0 : Fin 2) (1 : Fin 2))
  have h01 : (0 : Fin 2) = 1 := by
    simpa only [Path.source, Path.target] using
      (PreconnectedSpace.constant (inferInstance : PreconnectedSpace unitInterval)
        p.continuous : p 0 = p 1)
  exact (by decide : (0 : Fin 2) ≠ 1) h01

/-- A nonconstant map exchanges distinct path classes, and the natural comparison
computes its action on the corresponding distinct singular components. -/
private theorem twoPointSwap_components :
    let X := TopCat.of (Fin 2)
    let c₀ := ZerothHomotopy.mk (0 : Fin 2)
    let c₁ := ZerothHomotopy.mk (1 : Fin 2)
    c₀ ≠ c₁ ∧
    twoPointSwap 0 = 1 ∧ twoPointSwap 1 = 0 ∧ twoPointSwap 0 ≠ twoPointSwap 1 ∧
    zerothHomotopyFunctor.map (TopCat.ofHom twoPointSwap) c₀ = c₁ ∧
    zerothHomotopyFunctor.map (TopCat.ofHom twoPointSwap) c₁ = c₀ ∧
    zerothHomotopyFunctor.map (TopCat.ofHom twoPointSwap) c₀ ≠
      zerothHomotopyFunctor.map (TopCat.ofHom twoPointSwap) c₁ ∧
    zerothHomotopyIso.hom.app X c₀ ≠ zerothHomotopyIso.hom.app X c₁ ∧
    (TopCat.toSSet ⋙ SSet.π₀Functor).map (TopCat.ofHom twoPointSwap)
        (zerothHomotopyIso.hom.app X c₀) = zerothHomotopyIso.hom.app X c₁ := by
  dsimp only
  have hmap₀ : zerothHomotopyFunctor.map (TopCat.ofHom twoPointSwap)
      (ZerothHomotopy.mk (0 : Fin 2)) = ZerothHomotopy.mk (1 : Fin 2) := by
    exact (zerothHomotopyFunctor_map_apply (TopCat.ofHom twoPointSwap)
      (ZerothHomotopy.mk (0 : Fin 2))).trans
        ((ZerothHomotopy.map_mk twoPointSwap (0 : Fin 2)).trans
          (congrArg ZerothHomotopy.mk twoPointSwap_zero))
  have hmap₁ : zerothHomotopyFunctor.map (TopCat.ofHom twoPointSwap)
      (ZerothHomotopy.mk (1 : Fin 2)) = ZerothHomotopy.mk (0 : Fin 2) := by
    exact (zerothHomotopyFunctor_map_apply (TopCat.ofHom twoPointSwap)
      (ZerothHomotopy.mk (1 : Fin 2))).trans
        ((ZerothHomotopy.map_mk twoPointSwap (1 : Fin 2)).trans
          (congrArg ZerothHomotopy.mk twoPointSwap_one))
  refine ⟨twoPoint_classes_ne, twoPointSwap_zero, twoPointSwap_one, ?_,
    hmap₀, hmap₁, ?_, ?_, ?_⟩
  · simpa only [twoPointSwap_zero, twoPointSwap_one] using
      (show (1 : Fin 2) ≠ 0 by decide)
  · rw [hmap₀, hmap₁]
    exact Ne.symm twoPoint_classes_ne
  · intro h
    exact twoPoint_classes_ne
      ((zerothHomotopyEquiv (X := TopCat.of (Fin 2))).injective h)
  · exact (zerothHomotopyIso.hom.naturality_apply (TopCat.ofHom twoPointSwap)
      (ZerothHomotopy.mk (0 : Fin 2))).symm.trans
        (congrArg (fun z =>
          zerothHomotopyIso.hom.app (TopCat.of (Fin 2)) z) hmap₀)

end TopCat.PathComponentsExamples

namespace TopCat.SingularPostcompositionExamples

open scoped Simplicial

universe u v

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := ⟨rfl⟩

private abbrev B := ULift.{u} Bool

/-- Negation between two lifted copies of discrete Bool. -/
private def boolNeg : C(B.{u}, B.{v}) where
  toFun x := ULift.up (!x.down)
  continuous_toFun := continuous_of_discreteTopology

/-- The two path classes are separated by constancy of paths into a discrete space. -/
private theorem bool_path_injective :
    Function.Injective (ZerothHomotopy.mk (X := B.{u})) := by
  intro x y h
  obtain ⟨p⟩ := (Quotient.exact h : Joined x y)
  simpa only [Path.source, Path.target] using
    (TotallyDisconnectedSpace.eq_of_continuous p p.continuous
      (0 : unitInterval) 1)

/-- Bool has exactly the two indicated path classes. -/
private theorem bool_path_classes :
    ZerothHomotopy.mk (ULift.up false : B.{u}) ≠
        ZerothHomotopy.mk (ULift.up true : B.{u}) ∧
      ∀ c : ZerothHomotopy B.{u},
        c = ZerothHomotopy.mk (ULift.up false : B.{u}) ∨
          c = ZerothHomotopy.mk (ULift.up true : B.{u}) := by
  constructor
  · intro h
    have h' := congrArg ULift.down (bool_path_injective h)
    cases h'
  · intro c
    obtain ⟨⟨b⟩, rfl⟩ := ZerothHomotopy.mk_surjective c
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The same two constant vertices exhaust and separate the singular components. -/
private theorem bool_singular_classes :
    SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up false)) ≠
        SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up true)) ∧
      ∀ c : (toSSet.obj (of B.{u})).π₀,
        c = SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up false : B.{u})) ∨
          c = SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up true : B.{u})) := by
  let e := zerothHomotopyEquiv (X := of B.{u})
  have hfalse : e (ZerothHomotopy.mk (ULift.up false : B.{u})) =
      SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up false : B.{u})) :=
    zerothHomotopyEquiv_mk (X := of B.{u}) (ULift.up false : B.{u})
  have htrue : e (ZerothHomotopy.mk (ULift.up true : B.{u})) =
      SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up true : B.{u})) :=
    zerothHomotopyEquiv_mk (X := of B.{u}) (ULift.up true : B.{u})
  constructor
  · intro h
    apply bool_path_classes.1
    exact e.injective ((hfalse.trans h).trans htrue.symm)
  · intro c
    obtain ⟨x, hx⟩ := ZerothHomotopy.mk_surjective (e.symm c)
    have hc : e (ZerothHomotopy.mk x) = c :=
      (congrArg e hx).trans (e.apply_symm_apply c)
    rcases x with ⟨b⟩
    cases b
    · exact Or.inl (hc.symm.trans hfalse)
    · exact Or.inr (hc.symm.trans htrue)

/-- The stock comparison and its inverse identify these very representatives. -/
private theorem bool_comparison (b : Bool) :
    zerothHomotopyEquiv (X := of B.{u}) (ZerothHomotopy.mk (ULift.up b)) =
        SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up b : B.{u})) ∧
      (zerothHomotopyEquiv (X := of B.{u})).symm
          (SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up b : B.{u}))) =
        ZerothHomotopy.mk (ULift.up b : B.{u}) := by
  let e := zerothHomotopyEquiv (X := of B.{u})
  have h : e (ZerothHomotopy.mk (ULift.up b : B.{u})) =
      SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up b : B.{u})) :=
    zerothHomotopyEquiv_mk (X := of B.{u}) (ULift.up b : B.{u})
  exact ⟨h, (congrArg e.symm h.symm).trans
    (e.symm_apply_apply (ZerothHomotopy.mk (ULift.up b : B.{u})))⟩

/-- Negation acts on constant simplices in every singular degree. -/
private theorem boolNeg_simplex (n : SimplexCategoryᵒᵖ) (b : Bool) :
    toSSetPostcomp (X := of B.{u}) (Y := of B.{v}) boolNeg.{u, v} n
        ((toSSetObjEquiv (of B.{u}) n).symm
          (ContinuousMap.const _ (ULift.up b))) =
      (toSSetObjEquiv (of B.{v}) n).symm
        (ContinuousMap.const _ (ULift.up (!b))) := by
  apply (toSSetObjEquiv (of B.{v}) n).injective
  rw [toSSetObjEquiv_postcomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext d
  rfl

/-- Both values move under the simplex, singular-component and path-component actions. -/
private theorem boolNeg_both_values :
    toSSetPostcomp (X := of B.{u}) (Y := of B.{v}) boolNeg.{u, v} _
        ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up false : B.{u})) =
      (toSSetObj₀Equiv (X := of B.{v})).symm (ULift.up true : B.{v}) ∧
    toSSetPostcomp (X := of B.{u}) (Y := of B.{v}) boolNeg.{u, v} _
        ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up true : B.{u})) =
      (toSSetObj₀Equiv (X := of B.{v})).symm (ULift.up false : B.{v}) ∧
    toSSetMapπ₀ (X := of B.{u}) (Y := of B.{v}) boolNeg.{u, v}
        (SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up false : B.{u}))) =
      SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{v})).symm (ULift.up true : B.{v})) ∧
    toSSetMapπ₀ (X := of B.{u}) (Y := of B.{v}) boolNeg.{u, v}
        (SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up true : B.{u}))) =
      SSet.π₀.mk ((toSSetObj₀Equiv (X := of B.{v})).symm (ULift.up false : B.{v})) ∧
    ZerothHomotopy.map boolNeg.{u, v} (ZerothHomotopy.mk (ULift.up false)) =
      ZerothHomotopy.mk (ULift.up true : B.{v}) ∧
    ZerothHomotopy.map boolNeg.{u, v} (ZerothHomotopy.mk (ULift.up true)) =
      ZerothHomotopy.mk (ULift.up false : B.{v}) := by
  have hfalse :
      toSSetPostcomp (X := of B.{u}) (Y := of B.{v}) boolNeg.{u, v} _
          ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up false : B.{u})) =
        (toSSetObj₀Equiv (X := of B.{v})).symm (ULift.up true : B.{v}) :=
    toSSetPostcomp_vertex (X := of B.{u}) (Y := of B.{v})
      boolNeg.{u, v} (ULift.up false : B.{u})
  have htrue :
      toSSetPostcomp (X := of B.{u}) (Y := of B.{v}) boolNeg.{u, v} _
          ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up true : B.{u})) =
        (toSSetObj₀Equiv (X := of B.{v})).symm (ULift.up false : B.{v}) :=
    toSSetPostcomp_vertex (X := of B.{u}) (Y := of B.{v})
      boolNeg.{u, v} (ULift.up true : B.{u})
  refine ⟨hfalse, htrue, ?_, ?_, ?_, ?_⟩
  · exact (toSSetMapπ₀_mk (X := of B.{u}) (Y := of B.{v}) boolNeg.{u, v}
      ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up false : B.{u}))).trans
        (congrArg (SSet.π₀.mk (X := toSSet.obj (of B.{v}))) hfalse)
  · exact (toSSetMapπ₀_mk (X := of B.{u}) (Y := of B.{v}) boolNeg.{u, v}
      ((toSSetObj₀Equiv (X := of B.{u})).symm (ULift.up true : B.{u}))).trans
        (congrArg (SSet.π₀.mk (X := toSSet.obj (of B.{v}))) htrue)
  · exact ZerothHomotopy.map_mk boolNeg.{u, v} (ULift.up false : B.{u})
  · exact ZerothHomotopy.map_mk boolNeg.{u, v} (ULift.up true : B.{u})

/-- With an empty source every singular degree and both component quotients are empty. -/
private theorem empty_components (X : TopCat.{u}) [IsEmpty X] :
    (∀ n : SimplexCategoryᵒᵖ, IsEmpty ((toSSet.obj X).obj n)) ∧
      IsEmpty (toSSet.obj X).π₀ ∧ IsEmpty (ZerothHomotopy X) := by
  have h : ∀ n : SimplexCategoryᵒᵖ, IsEmpty ((toSSet.obj X).obj n) := by
    intro n
    exact ⟨fun a => isEmptyElim (a.down.hom (ULift.up (StdSimplex.single 0)))⟩
  refine ⟨h, ⟨fun c => ?_⟩, ⟨fun z => ?_⟩⟩
  · obtain ⟨a, _⟩ := SSet.π₀.mk_surjective c
    exact (h _).false a
  · obtain ⟨x, _⟩ := ZerothHomotopy.mk_surjective z
    exact isEmptyElim x

/-- No point of an empty source is needed for either square, with arbitrary target. -/
private theorem empty_squares {X : TopCat.{u}} {Y : TopCat.{v}} [IsEmpty X]
    (f : C(X, Y)) :
    zerothHomotopyEquiv (X := Y) ∘ ZerothHomotopy.map f =
        toSSetMapπ₀ f ∘ zerothHomotopyEquiv (X := X) ∧
      ZerothHomotopy.map f ∘ (zerothHomotopyEquiv (X := X)).symm =
        (zerothHomotopyEquiv (X := Y)).symm ∘ toSSetMapπ₀ f := by
  constructor
  · funext z
    exact False.elim ((empty_components X).2.2.false z)
  · funext c
    exact False.elim ((empty_components X).2.1.false c)

end TopCat.SingularPostcompositionExamples
