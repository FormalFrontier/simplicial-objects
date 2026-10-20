/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Connected components and universe lifts

The levelwise universe lift of a simplicial set has the same connected components.
The comparison sends the class of `ULift.up x` to the class of `x`; its inverse
lifts vertices. Both maps descend through `SSet.π₀.lift`, using the corresponding
maps on edges.
-/

@[expose] public section

universe r w

open CategoryTheory

open scoped Simplicial

namespace SSet

/-- The connected components of a universe lift are equivalent to those of the
original simplicial set. The universe parameters are ordered as `r, w`, with `r`
the lift level and `w` the universe of the simplices of `K`. -/
def piZeroULiftEquiv (K : SSet.{w}) :
    π₀ ((uliftFunctor.{r, w}).obj K) ≃ π₀ K where
  toFun := π₀.lift (fun x ↦ π₀.mk x.down) (by
    intro x₀ x₁ e
    exact π₀.sound (Edge.mk e.edge.down
      (congrArg ULift.down e.src_eq) (congrArg ULift.down e.tgt_eq)))
  invFun := π₀.lift (fun x ↦ π₀.mk (ULift.up x)) (by
    intro x₀ x₁ e
    exact π₀.sound (Edge.mk (ULift.up e.edge)
      (congrArg ULift.up e.src_eq) (congrArg ULift.up e.tgt_eq)))
  left_inv z := by
    obtain ⟨x, rfl⟩ := π₀.mk_surjective z
    cases x
    rfl
  right_inv z := by
    obtain ⟨x, rfl⟩ := π₀.mk_surjective z
    rfl

/-- The component comparison lowers a lifted vertex. -/
@[simp]
lemma piZeroULiftEquiv_apply_mk (K : SSet.{w})
    (x : ((uliftFunctor.{r, w}).obj K) _⦋0⦌) :
    piZeroULiftEquiv.{r, w} K (π₀.mk x) = π₀.mk x.down :=
  rfl

/-- The inverse component comparison lifts a vertex. -/
@[simp]
lemma piZeroULiftEquiv_symm_apply_mk (K : SSet.{w}) (x : K _⦋0⦌) :
    (piZeroULiftEquiv.{r, w} K).symm (π₀.mk x) = π₀.mk (ULift.up x) :=
  rfl

/-- Lowering components commutes with a morphism of simplicial sets. -/
lemma piZeroULiftEquiv_naturality {K K' : SSet.{w}} (f : K ⟶ K')
    (z : π₀ ((uliftFunctor.{r, w}).obj K)) :
    piZeroULiftEquiv.{r, w} K' (mapπ₀ ((uliftFunctor.{r, w}).map f) z) =
      mapπ₀ f (piZeroULiftEquiv.{r, w} K z) := by
  obtain ⟨x, rfl⟩ := π₀.mk_surjective z
  rfl

/-- Lifting components commutes with a morphism of simplicial sets. -/
lemma piZeroULiftEquiv_symm_naturality {K K' : SSet.{w}} (f : K ⟶ K')
    (z : π₀ K) :
    (piZeroULiftEquiv.{r, w} K').symm (mapπ₀ f z) =
      mapπ₀ ((uliftFunctor.{r, w}).map f) ((piZeroULiftEquiv.{r, w} K).symm z) := by
  obtain ⟨x, rfl⟩ := π₀.mk_surjective z
  rfl

/-- The component comparison is determined by its values on lifted vertices. -/
lemma piZeroULiftEquiv_unique (K : SSet.{w})
    (f : π₀ ((uliftFunctor.{r, w}).obj K) → π₀ K)
    (h : ∀ x : K _⦋0⦌, f (π₀.mk (ULift.up x)) = π₀.mk x) :
    f = piZeroULiftEquiv.{r, w} K := by
  funext z
  obtain ⟨x, rfl⟩ := π₀.mk_surjective z
  cases x with
  | up x => exact h x

end SSet
