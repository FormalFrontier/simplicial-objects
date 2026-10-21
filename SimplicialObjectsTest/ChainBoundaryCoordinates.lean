/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects.ChainBoundaryCoordinates

/-!
# The integral boundary of the standard identity edge

For the identity edge of `Δ[1]`, the zeroth face is vertex one and the first
face is vertex zero. The boundary of its source summand with coefficient
`ULift.up (1 : ℤ)` therefore has integral coordinates
`Finsupp.single v₁ 1 - Finsupp.single v₀ 1`.
The vertices are distinct and this boundary is a nonzero chain. This is not a
claim of nonzero homology: the chain is a boundary.

The input chain is the coproduct inclusion of the identity simplex with
lifted integer coefficient one.

## References

Mathlib supplies the standard simplex, its simplex and vertex equivalences,
and the face convention. The integral coordinate API is the Formal Frontier
Agents' simplicial-chain formalization, including Prism's work. The existing
standard-interval normalization examples use the same identity edge and face
orientation; here the chains are the all-simplex chains with lifted integer
coefficients.
-/

open CategoryTheory
open scoped Simplicial

universe u

namespace AlgebraicTopology

/-- The standard identity edge is nondegenerate, has the stated oriented
faces, and has distinct endpoints. -/
private theorem stdSimplex_one_identity_edge_shape :
    let X : SSet.{u} := Δ[1]
    let e : X _⦋1⦌ := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)
    let v : Fin 2 → X _⦋0⦌ := fun i ↦ SSet.stdSimplex.obj₀Equiv.symm i
    e ∈ X.nonDegenerate 1 ∧
      X.δ (0 : Fin 2) e = v 1 ∧ X.δ (1 : Fin 2) e = v 0 ∧ v 0 ≠ v 1 := by
  dsimp only
  refine ⟨SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate 1, ?_, ?_, ?_⟩
  · apply SSet.stdSimplex.ext
    intro j
    fin_cases j
    rw [SSet.stdSimplex.δ_apply]
    rfl
  · apply SSet.stdSimplex.ext
    intro j
    fin_cases j
    rw [SSet.stdSimplex.δ_apply]
    rfl
  · intro h
    have h01 : (0 : Fin 2) = 1 := SSet.stdSimplex.obj₀Equiv.symm.injective h
    exact (by decide : (0 : Fin 2) ≠ 1) h01

/-- The boundary of the lifted unit in the identity-edge summand has the
terminal unit coordinate minus the initial unit coordinate. -/
private theorem stdSimplex_one_identity_edge_boundary_coordinates :
    let X : SSet.{u} := Δ[1]
    let e : X _⦋1⦌ := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)
    let v : Fin 2 → X _⦋0⦌ := fun i ↦ SSet.stdSimplex.obj₀Equiv.symm i
    (chainGroupIsoFinsupp X 0).hom.hom
        (((X.chainComplex integerCoefficients.{u}).d 1 0).hom
          ((X.ιChainComplex (R := integerCoefficients.{u}) e).hom
            (ULift.up (1 : ℤ)))) =
      Finsupp.single (v 1) 1 - Finsupp.single (v 0) 1 := by
  dsimp only
  rw [chainGroupIsoFinsupp_d_apply, chainGroupIsoFinsupp_hom_ι, Fin.sum_univ_two]
  have hshape := stdSimplex_one_identity_edge_shape.{u}
  dsimp only at hshape
  simp [hshape.2.1, hshape.2.2.1, sub_eq_add_neg]

/-- The boundary of the lifted unit identity-edge chain is nonzero as a
chain in degree zero, without any assertion of nonzero homology. -/
private theorem stdSimplex_one_identity_edge_boundary_ne_zero :
    let X : SSet.{u} := Δ[1]
    let e : X _⦋1⦌ := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)
    ((X.chainComplex integerCoefficients.{u}).d 1 0).hom
        ((X.ιChainComplex (R := integerCoefficients.{u}) e).hom
          (ULift.up (1 : ℤ))) ≠ 0 := by
  dsimp only
  intro h
  have hc := stdSimplex_one_identity_edge_boundary_coordinates.{u}
  dsimp only at hc
  rw [h, map_zero] at hc
  have hv := congrArg
    (fun c : ((Δ[1] : SSet.{u}) _⦋0⦌) →₀ ℤ ↦
      c (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) hc
  have hshape := stdSimplex_one_identity_edge_shape.{u}
  dsimp only at hshape
  have h01 := hshape.2.2.2
  have hzero_one : (0 : ℤ) = 1 := by
    simpa only [Finsupp.zero_apply, Finsupp.sub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne' h01, sub_zero] using hv
  exact zero_ne_one hzero_one

end AlgebraicTopology
