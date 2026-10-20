/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects

/-!
# A nonzero integral chain on the standard point

The lifted integer one in the vertex summand of `Δ[0]` is nonzero: the
integral coordinate isomorphism sends it to the nonzero unit basis function.
This uses the standard simplicial point and the coefficient object
`AlgebraicTopology.integerCoefficients`, not a different integer module model.

Mathlib supplies the standard simplex and its vertex equivalence; the integral
coordinate law is the Formal Frontier Agents' simplicial-chain formalization.
-/

open scoped Simplicial

namespace AlgebraicTopology

/-- The vertex chain with lifted coefficient one on the standard point is nonzero. -/
private theorem point_ιChainComplex_one_ne_zero :
    ((Δ[0] : SSet.{0}).ιChainComplex (R := integerCoefficients)
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))).hom (ULift.up (1 : ℤ)) ≠ 0 := by
  intro h
  have hcoord := chainGroupIsoFinsupp_hom_ι (Δ[0] : SSet.{0})
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  rw [h, map_zero] at hcoord
  have hone := congrArg
    (fun z : (Δ[0] : SSet.{0}) _⦋0⦌ →₀ ℤ =>
      z (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) hcoord
  simp at hone

end AlgebraicTopology
