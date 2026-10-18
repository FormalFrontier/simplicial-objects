/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorCoefficientSequences
public import SimplicialObjectsTest.TensorCoefficientMaps
public import SimplicialObjectsTest.Normalization
public import Mathlib.Data.ZMod.Basic

/-!
# Doubling and reduction as endpoint-preservation examples

Integer doubling and reduction modulo two specialize coefficient endpoint
preservation to the standard point in degree zero and the standard interval in
degree one. The coefficient injectivity, exactness and surjectivity inputs come
from the coefficient-map tests. The same point and interval short complexes are
short exact; their carriers, maps and nonzero tensor generators are unchanged.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial
open SimplicialObjectsTest.Normalization

namespace SimplicialObjectsTest.TensorCoefficientMaps

/-- The degree injectivity statement specializes to integer doubling on the point
in degree zero and on the interval in degree one. -/
theorem doubling_injective_on_point_and_interval :
    Function.Injective
      (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        ((2 : ℕ) • AddMonoidHom.id ℤ) (Δ[0] : SSet.{0}) 0) ∧
    Function.Injective
      (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        ((2 : ℕ) • AddMonoidHom.id ℤ) interval 1) := by
  constructor
  · exact SSet.tensorNormalizedCoefficientMap_injective.{0, 0, 0, 0}
      ((2 : ℕ) • AddMonoidHom.id ℤ) integer_doubling_injective (Δ[0] : SSet.{0}) 0
  · exact SSet.tensorNormalizedCoefficientMap_injective.{0, 0, 0, 0}
      ((2 : ℕ) • AddMonoidHom.id ℤ) integer_doubling_injective interval 1

/-- The degree surjectivity statement specializes to reduction modulo two on the
point in degree zero and on the interval in degree one. -/
theorem reduction_surjective_on_point_and_interval :
    Function.Surjective
      (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        (Int.castAddHom (ZMod 2)) (Δ[0] : SSet.{0}) 0) ∧
    Function.Surjective
      (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        (Int.castAddHom (ZMod 2)) interval 1) := by
  constructor
  · exact SSet.tensorNormalizedCoefficientMap_surjective.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) binary_reduction_surjective (Δ[0] : SSet.{0}) 0
  · exact SSet.tensorNormalizedCoefficientMap_surjective.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) binary_reduction_surjective interval 1

/-- The chain monomorphism statement uses the closed injectivity of integer doubling
on the same point and interval complexes. -/
theorem doubling_mono_on_point_and_interval :
    Mono (SSet.tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
      ((2 : ℕ) • AddMonoidHom.id ℤ) (Δ[0] : SSet.{0})) ∧
    Mono (SSet.tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
      ((2 : ℕ) • AddMonoidHom.id ℤ) interval) := by
  constructor
  · exact SSet.tensorNormalizedChainComplexCoefficientMap_mono.{0, 0, 0, 0}
      ((2 : ℕ) • AddMonoidHom.id ℤ) integer_doubling_injective (Δ[0] : SSet.{0})
  · exact SSet.tensorNormalizedChainComplexCoefficientMap_mono.{0, 0, 0, 0}
      ((2 : ℕ) • AddMonoidHom.id ℤ) integer_doubling_injective interval

/-- The chain epimorphism statement uses the closed surjectivity of reduction modulo
two on the same point and interval complexes. -/
theorem reduction_epi_on_point_and_interval :
    Epi (SSet.tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) (Δ[0] : SSet.{0})) ∧
    Epi (SSet.tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) interval) := by
  constructor
  · exact SSet.tensorNormalizedChainComplexCoefficientMap_epi.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) binary_reduction_surjective (Δ[0] : SSet.{0})
  · exact SSet.tensorNormalizedChainComplexCoefficientMap_epi.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) binary_reduction_surjective interval

/-- The short-exactness statement applies to the closed point and interval short
complexes, using only the three closed coefficient inputs. -/
theorem doubling_reduction_shortExact_on_point_and_interval :
    pointDoublingReductionShortComplex.ShortExact ∧
      intervalDoublingReductionShortComplex.ShortExact := by
  constructor
  · exact SSet.tensorNormalizedChainComplexCoefficientShortComplex_shortExact.{0, 0, 0, 0, 0}
      ((2 : ℕ) • AddMonoidHom.id ℤ) (Int.castAddHom (ZMod 2)) integer_doubling_injective
      integer_doubling_reduction_exact_coefficients binary_reduction_surjective
      (Δ[0] : SSet.{0})
  · exact SSet.tensorNormalizedChainComplexCoefficientShortComplex_shortExact.{0, 0, 0, 0, 0}
      ((2 : ℕ) • AddMonoidHom.id ℤ) (Int.castAddHom (ZMod 2)) integer_doubling_injective
      integer_doubling_reduction_exact_coefficients binary_reduction_surjective interval

end SimplicialObjectsTest.TensorCoefficientMaps
