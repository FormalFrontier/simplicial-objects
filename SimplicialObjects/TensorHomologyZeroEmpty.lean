/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorHomologyZero
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Degree-zero normalized tensor homology of the empty boundary

The boundary of the standard zero-simplex is the empty simplicial set. Its
component coproduct is initial, so the component comparison identifies its
normalized tensor homology in degree zero with a zero object.

This uses Mathlib's standard boundary, simplicial component quotient and empty
colimit APIs, together with the component comparison in
`SimplicialObjects.TensorHomologyZero`.
-/

@[expose] public section

universe a w p

open CategoryTheory Limits
open scoped Simplicial

namespace SSet

/-- Degree-zero normalized tensor homology of the empty standard boundary
is zero for arbitrary coefficients, with independent coefficient, simplex and
padding universes. -/
theorem tensorNormalizedHomologyZero_boundary_zero_isZero
    (A : Type a) [AddCommGroup A] :
    IsZero ((tensorNormalizedChainComplex.{a, w, p} A
      (∂Δ[0] : SSet.{w})).homology 0) := by
  let : IsEmpty (π₀ (∂Δ[0] : SSet.{w})) := ⟨fun c ↦ by
    obtain ⟨x, _⟩ := π₀.mk_surjective c
    simpa only [boundary_zero, Subfunctor.bot_obj, Set.mem_empty_iff_false]
      using x.property⟩
  let : IsEmpty (Discrete (π₀ (∂Δ[0] : SSet.{w}))) :=
    ⟨fun c ↦ isEmptyElim c.as⟩
  let F : Discrete (π₀ (∂Δ[0] : SSet.{w})) ⥤ ModuleCat.{max a w p} ℤ :=
    Discrete.functor (fun _ ↦ ModuleCat.of ℤ (ULift.{max w p} A))
  have h : IsZero (colimit F) :=
    (isColimitEquivIsInitialOfIsEmpty _ _ (colimit.isColimit F)).isZero
  exact h.of_iso
    (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A (∂Δ[0] : SSet.{w}))

end SSet
