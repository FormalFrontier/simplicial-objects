/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Logic.Equiv.Prod
import SimplicialObjects.ComponentLifts
import SimplicialObjects.ComponentProducts

/-!
# Components of a lifted discrete binary product

The constant simplicial set on `Fin 2` has two components, distinguished by its
constant vertex labels. After lifting both factors, the categorical
product has four components. The component comparisons classify them by
`Fin 2 × Fin 2`, using vertices supplied by the Cartesian monoidal comparison.

The construction uses Mathlib's component quotient and constant simplicial
object. All simplicial objects here lie in universe zero. The classification
concerns components only, independently of coefficients or homology comparisons.
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

end SimplicialObjectsTest
