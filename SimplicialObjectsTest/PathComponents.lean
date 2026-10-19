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

## References

The separation proof uses Mathlib's `PreconnectedSpace.constant`: a path into a
discrete space has equal endpoints. See Mathlib
[83abb3e776bdefcbc447a1e44d0debe4010039e5](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Connected/TotallyDisconnected.lean).
-/

open CategoryTheory

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
