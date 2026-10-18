/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.PointHomology
public import SimplicialObjects.TensorCoefficientMaps
public import SimplicialObjectsTest.TensorCoefficientMaps
import Mathlib.Data.ZMod.Basic

/-!
# Coefficient reduction through point homology

The degree-zero comparisons on the standard simplicial point turn the integer
to modulo-two chain morphism into a map between the lifted coefficient objects.
The coefficient-change square and inverse comparison law show that coefficient
one reduces to one. The first homology of the same point with integer
coefficients vanishes. The point and interval coefficient examples are imported
from `SimplicialObjectsTest.TensorCoefficientMaps`.

## References

* May, *A Concise Course in Algebraic Topology*, revised edition, Chapter 13, §1,
  and Chapter 16, §4: point homology and normalized simplicial chains.
* Mathlib supplies categorical homology, lifted integer-module structures and
  terminality of the standard simplicial point.
* `SimplicialObjects.TensorCoefficients`, `SimplicialObjects.TensorCoefficientMaps`
  and `SimplicialObjects.PointHomology` supply the normalized tensor complex,
  coefficient change and degree-zero comparison morphisms.
-/

open CategoryTheory Limits
open scoped Simplicial

namespace SSet

/-- Reduction modulo two, passing from coefficients to degree-zero point homology
and back through the normalized integral tensor complex. -/
private noncomputable def pointReductionThroughHomology :
    (ModuleCat.of ℤ (ULift.{0} ℤ) : ModuleCat.{0} ℤ) ⟶
      (ModuleCat.of ℤ (ULift.{0} (ZMod 2)) : ModuleCat.{0} ℤ) :=
  tensorNormalizedCoefficientToHomologyZero.{0, 0, 0}
      ℤ (Δ[0] : SSet.{0}) stdSimplex.isTerminalObj₀ ≫
    HomologicalComplex.homologyMap
      (tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
        (Int.castAddHom (ZMod 2)) (Δ[0] : SSet.{0})) 0 ≫
    tensorNormalizedHomologyZeroToCoefficient.{0, 0, 0}
      (ZMod 2) (Δ[0] : SSet.{0}) stdSimplex.isTerminalObj₀

/-- The coefficient value obtained by reducing the integral coefficient-one point
class through the degree-zero homology comparisons. -/
private noncomputable def pointReductionOneThroughHomology :
    (ModuleCat.of ℤ (ULift.{0} (ZMod 2)) : ModuleCat.{0} ℤ) :=
  pointReductionThroughHomology (ULift.up (1 : ℤ))

/-- Reduction through degree-zero point homology sends the lifted integer one to
one modulo two, by coefficient naturality and the inverse comparison law. -/
private theorem pointReductionOneThroughHomology_eq_one :
    pointReductionOneThroughHomology = (ULift.up (1 : ZMod 2) : ULift.{0} (ZMod 2)) := by
  have h := (tensorNormalizedHomologyZeroIsoCoefficient.{0, 0, 0}
    ℤ (Δ[0] : SSet.{0}) stdSimplex.isTerminalObj₀).inv_hom_id
  simp only [tensorNormalizedHomologyZeroIsoCoefficient_inv,
    tensorNormalizedHomologyZeroIsoCoefficient_hom] at h
  rw [pointReductionOneThroughHomology, pointReductionThroughHomology,
    tensorNormalizedHomologyZeroToCoefficient_coefficient_naturality.{0, 0, 0, 0}
      ℤ (ZMod 2) (Δ[0] : SSet.{0}) stdSimplex.isTerminalObj₀ (Int.castAddHom (ZMod 2)),
    ← Category.assoc, h, Category.id_comp]
  change (ULift.up (((1 : ℤ) : ZMod 2)) : ULift.{0} (ZMod 2)) = ULift.up (1 : ZMod 2)
  rw [Int.cast_one]

/-- The standard simplicial point has zero first homology with integer
coefficients, the positive-degree point dimension statement of May, Chapter 13, §1. -/
private theorem isZero_tensorNormalizedHomology_one_standardPoint :
    IsZero ((tensorNormalizedChainComplex.{0, 0, 0} ℤ (Δ[0] : SSet.{0})).homology 1) :=
  isZero_tensorNormalizedHomology_succ.{0, 0, 0}
    ℤ (Δ[0] : SSet.{0}) stdSimplex.isTerminalObj₀ 0

/-- The standard simplicial point has zero degree-zero homology with the trivial
coefficient group `ZMod 1`. -/
private theorem isZero_tensorNormalizedHomology_zero_standardPoint_zmod_one :
    IsZero ((tensorNormalizedChainComplex.{0, 0, 0}
      (ZMod 1) (Δ[0] : SSet.{0})).homology 0) := by
  have hC : IsZero (ModuleCat.of ℤ (ULift.{0} (ZMod 1)) : ModuleCat.{0} ℤ) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  exact hC.of_iso (tensorNormalizedHomologyZeroIsoCoefficient.{0, 0, 0}
    (ZMod 1) (Δ[0] : SSet.{0}) stdSimplex.isTerminalObj₀)

end SSet
