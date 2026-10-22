/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects
import SimplicialObjects.ChainComplexCoordinates

/-!
# Integral chains on a point and a two-point collapse

The lifted integer one in the vertex summand of `Δ[0]` is nonzero: the
integral coordinate isomorphism sends it to the nonzero unit basis function.
This uses the standard simplicial point and the coefficient object
`AlgebraicTopology.integerCoefficients`, not a different integer module model.

For the constant simplicial collapse from `Fin 2` to `PUnit`, the sum of the two
unit vertex chains has image with coordinate `single PUnit.unit 2`. This evaluates
the natural chain-complex comparison in degree zero and uses its arbitrary-chain
naturality, exhibiting coefficient accumulation under a noninjective map.

Mathlib supplies the standard simplex and its vertex equivalence; the integral
coordinate law is the Formal Frontier Agents' simplicial-chain formalization.
-/

open CategoryTheory
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

/-- Collapsing two vertices adds their unit coefficients in integral coordinates. -/
private theorem const_fin_two_collapse_chain_coordinates :
    let X : SSet.{0} := (Functor.const _).obj (Fin 2)
    let Y : SSet.{0} := (Functor.const _).obj PUnit
    let f : X ⟶ Y := (Functor.const _).map (↾fun _ : Fin 2 ↦ PUnit.unit)
    (chainGroupIsoFinsupp Y 0).hom.hom
        (((SSet.chainComplexMap f integerCoefficients).f 0).hom
          ((X.ιChainComplex (R := integerCoefficients) (n := 0) (0 : Fin 2)).hom
              (ULift.up (1 : ℤ)) +
            (X.ιChainComplex (R := integerCoefficients) (n := 0) (1 : Fin 2)).hom
              (ULift.up (1 : ℤ)))) =
      Finsupp.single PUnit.unit 2 := by
  intro X Y f
  let c : (X.chainComplex integerCoefficients).X 0 :=
    (X.ιChainComplex (R := integerCoefficients) (n := 0) (0 : Fin 2)).hom
        (ULift.up (1 : ℤ)) +
      (X.ιChainComplex (R := integerCoefficients) (n := 0) (1 : Fin 2)).hom
        (ULift.up (1 : ℤ))
  have hc : (chainGroupIsoFinsupp X 0).hom.hom c =
      Finsupp.single (0 : Fin 2) (1 : ℤ) +
        Finsupp.single (1 : Fin 2) (1 : ℤ) := by
    dsimp only [c]
    rw [map_add, chainGroupIsoFinsupp_hom_ι, chainGroupIsoFinsupp_hom_ι]
  have hcomparison : ((chainComplexIsoFinsupp.hom.app X).f 0).hom c =
      Finsupp.single (0 : Fin 2) (1 : ℤ) +
        Finsupp.single (1 : Fin 2) (1 : ℤ) :=
    (chainComplexIsoFinsupp_hom_f_apply X 0 c).trans hc
  rw [← chainComplexIsoFinsupp_eval Y 0]
  change ((chainComplexIsoFinsupp.hom.app Y).f 0).hom
      (((SSet.chainComplexMap f integerCoefficients).f 0).hom c) =
    Finsupp.single PUnit.unit 2
  refine (chainComplexIsoFinsupp_naturality_apply f 0 c).trans ?_
  refine (congrArg
    (Finsupp.mapDomain (fun x : X _⦋0⦌ => f.app (Opposite.op ⦋0⦌) x))
    hcomparison).trans ?_
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  simp [f, ← Finsupp.single_add]

end AlgebraicTopology
