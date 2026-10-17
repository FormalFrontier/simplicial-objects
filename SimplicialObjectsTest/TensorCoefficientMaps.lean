/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects.TensorCoefficientMaps
import SimplicialObjectsTest.Normalization
import Mathlib.Data.ZMod.Basic

/-!
# Reduction modulo two on the standard interval

Reduction of integer coefficients kills a nonzero tensor with coefficient two,
but preserves a nonzero generator with coefficient one. The reduced edge has a
nonzero boundary. These calculations use the degree operation and the existing
normalized coefficient action, independently of the four compatibility
statements. The final four examples evaluate those statements on the interval.
-/

open CategoryTheory Limits Opposite
open scoped Simplicial TensorProduct
open SimplicialObjectsTest.Normalization

namespace SimplicialObjectsTest.TensorCoefficientMaps

private def initialVertex : interval.nonDegenerate 0 := ⟨vertex 0, vertex_nondegenerate 0⟩
private def terminalVertex : interval.nonDegenerate 0 := ⟨vertex 1, vertex_nondegenerate 1⟩
private def intervalEdge : interval.nonDegenerate 1 := ⟨edge, edge_nondegenerate⟩

private noncomputable def integerVertex (x : ℤ) :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 0 :=
  ULift.up (Finsupp.single initialVertex 1 ⊗ₜ[ℤ] x)

private noncomputable def binaryVertex (x : ZMod 2) :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 2) interval 0 :=
  ULift.up (Finsupp.single initialVertex 1 ⊗ₜ[ℤ] x)

private noncomputable def integerEdge :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 1 :=
  ULift.up (Finsupp.single intervalEdge 1 ⊗ₜ[ℤ] (1 : ℤ))

private noncomputable def binaryEdge :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 2) interval 1 :=
  ULift.up (Finsupp.single intervalEdge 1 ⊗ₜ[ℤ] (1 : ZMod 2))

private abbrev integerCoefficients : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ULift.{0} ℤ)
private abbrev binaryCoefficients : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ULift.{0} (ZMod 2))

private noncomputable def liftedReduction : integerCoefficients ⟶ binaryCoefficients :=
  ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
    (Int.castAddHom (ZMod 2)).toIntLinearMap ∘ₗ
      (ULift.moduleEquiv (R := ℤ)).toLinearMap)

private noncomputable def normalizedReduction :
    interval.normalizedChainComplex integerCoefficients ⟶
      interval.normalizedChainComplex binaryCoefficients :=
  (interval.splitting.map (sigmaConst.obj integerCoefficients)).nondegComplexMap
    (interval.splitting.map (sigmaConst.obj binaryCoefficients))
    (Functor.whiskerLeft interval (sigmaConst.map liftedReduction))

private theorem tensor_generator_ne_zero {D : Type} [AddCommGroup D] (n : ℕ)
    (s : interval.nonDegenerate n) (x : D) (hx : x ≠ 0) :
    (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x) :
      SSet.tensorNormalizedChainComplexX.{0, 0, 0} D interval n) ≠ 0 := by
  intro h
  have hc : Finsupp.single s (ULift.up x : ULift.{0} D) = 0 :=
    (SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_single.{0, 0, 0}
      D interval n s x).symm.trans
      ((congrArg
        (fun z : SSet.tensorNormalizedChainComplexX.{0, 0, 0} D interval n ↦
          (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0} D interval n).hom.hom z)
        h).trans
          (map_zero
            (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0} D interval n).hom.hom))
  apply hx
  simpa using congrArg
    (fun z : interval.nonDegenerate n →₀ ULift.{0} D ↦ (z s).down) hc

/-- Reduction modulo two kills a genuinely nonzero integer tensor. -/
theorem reduction_kills_nonzero_two :
    integerVertex 2 ≠ 0 ∧
      SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        (Int.castAddHom (ZMod 2)) interval 0 (integerVertex 2) = 0 := by
  constructor
  · exact tensor_generator_ne_zero (D := ℤ) 0 initialVertex 2 (by decide)
  · rw [integerVertex, SSet.tensorNormalizedCoefficientMap_single]
    have hz : Int.castAddHom (ZMod 2) 2 = 0 := by decide
    rw [hz, TensorProduct.tmul_zero]
    rfl

/-- A generator with coefficient one survives, so the degree operation is not zero. -/
theorem reduction_preserves_nonzero_one :
    SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        (Int.castAddHom (ZMod 2)) interval 0 (integerVertex 1) = binaryVertex 1 ∧
      binaryVertex 1 ≠ 0 := by
  constructor
  · exact (SSet.tensorNormalizedCoefficientMap_single.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) interval 0 initialVertex (1 : ℤ)).trans
        (congrArg binaryVertex (by decide : Int.castAddHom (ZMod 2) (1 : ℤ) = 1))
  · exact tensor_generator_ne_zero (D := ZMod 2) 0 initialVertex 1 (by decide)

/-- The chain morphism itself also preserves a nonzero coefficient-one generator.
This calculation uses its generator API, not the component statement. -/
theorem chain_reduction_preserves_nonzero_one :
    (SSet.tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
        (Int.castAddHom (ZMod 2)) interval).f 0 (integerVertex 1) = binaryVertex 1 ∧
      binaryVertex 1 ≠ 0 := by
  constructor
  · exact (SSet.tensorNormalizedChainComplexCoefficientMap_f_single.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) interval 0 initialVertex (1 : ℤ)).trans
        (congrArg binaryVertex (by decide : Int.castAddHom (ZMod 2) (1 : ℤ) = 1))
  · exact tensor_generator_ne_zero (D := ZMod 2) 0 initialVertex 1 (by decide)

private theorem terminal_ne_initial : terminalVertex ≠ initialVertex := by
  intro h
  have hv := congrArg
    (fun s : interval.nonDegenerate 0 ↦ SSet.stdSimplex.obj₀Equiv s.val) h
  have hfin : (1 : Fin 2) = 0 :=
    ((SSet.stdSimplex.obj₀Equiv.{0} (n := 1)).apply_symm_apply 1).symm.trans
      (hv.trans ((SSet.stdSimplex.obj₀Equiv.{0} (n := 1)).apply_symm_apply 0))
  exact (by decide : (1 : Fin 2) ≠ 0) hfin

/-- The reduced edge has a nonzero independently defined signed boundary. -/
theorem binary_edge_boundary_ne_zero :
    SSet.tensorNormalizedBoundary.{0, 0, 0} (ZMod 2) interval 0 binaryEdge ≠ 0 := by
  have hb : SSet.tensorNormalizedBoundary.{0, 0, 0} (ZMod 2) interval 0 binaryEdge =
      (ULift.up (Finsupp.single terminalVertex 1 ⊗ₜ[ℤ] (1 : ZMod 2)) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 2) interval 0) -
      (ULift.up (Finsupp.single initialVertex 1 ⊗ₜ[ℤ] (1 : ZMod 2)) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 2) interval 0) := by
    rw [binaryEdge, SSet.tensorNormalizedBoundary_single, Fin.sum_univ_two]
    simp only [intervalEdge, edge_face_zero, edge_face_one, sub_eq_add_neg]
    rw [interval.normalizedIntegralSimplex_of_mem_nonDegenerate (vertex 1)
      (vertex_nondegenerate 1),
      interval.normalizedIntegralSimplex_of_mem_nonDegenerate (vertex 0)
        (vertex_nondegenerate 0)]
    simp [terminalVertex, initialVertex]
    rfl
  have hcoords := (congrArg
    (fun z : SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 2) interval 0 ↦
      (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0}
        (ZMod 2) interval 0).hom.hom z) hb).trans
      ((map_sub
        (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0}
          (ZMod 2) interval 0).hom.hom _ _).trans
        (congrArg₂
          (fun z w : interval.nonDegenerate 0 →₀ ULift.{0} (ZMod 2) ↦ z - w)
          (SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_single.{0, 0, 0}
            (ZMod 2) interval 0 terminalVertex (1 : ZMod 2))
          (SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_single.{0, 0, 0}
            (ZMod 2) interval 0 initialVertex (1 : ZMod 2))))
  intro h
  have hc := congrArg
    (fun z : interval.nonDegenerate 0 →₀ ULift.{0} (ZMod 2) ↦ (z terminalVertex).down)
    hcoords
  rw [h, map_zero] at hc
  simp [terminal_ne_initial] at hc

/-- Zero coefficients annihilate the edge without a boundary-compatibility assumption. -/
theorem zero_coefficient_edge :
    SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
      (0 : ℤ →+ ZMod 2) interval 1 integerEdge = 0 := by
  rw [SSet.tensorNormalizedCoefficientMap_zero]
  rfl

/-- The all-simplex degree formula includes an elementary degenerate edge's zero class. -/
theorem degenerate_edge_reduction :
    SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0} (Int.castAddHom (ZMod 2)) interval 1
      (ULift.up (interval.normalizedIntegralSimplex
        (interval.σ (0 : Fin 1) (vertex 0)) ⊗ₜ[ℤ] (1 : ℤ))) = 0 := by
  rw [SSet.tensorNormalizedCoefficientMap_simplex,
    interval.normalizedIntegralSimplex_of_mem_degenerate _
      (interval.σ_mem_degenerate (0 : Fin 1) (vertex 0)), TensorProduct.zero_tmul]
  rfl

/-! ## Examples using the compatibility theorems -/

/-- The degree-comparison statement evaluated on the integral interval edge. -/
theorem comparison_reduction_edge :
    (SSet.tensorNormalizedChainComplexXIso.{0, 0, 0} (ZMod 2) interval 1).hom
        (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
          (Int.castAddHom (ZMod 2)) interval 1 integerEdge) =
      normalizedReduction.f 1
        ((SSet.tensorNormalizedChainComplexXIso.{0, 0, 0} ℤ interval 1).hom integerEdge) :=
  congrArg
    (fun f : SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 1 ⟶
      (interval.normalizedChainComplex binaryCoefficients).X 1 ↦ f integerEdge)
    (SSet.tensorNormalizedCoefficientMap_comparison.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) interval 1)

/-- Boundary compatibility evaluated on the integral edge, whose reduced boundary is nonzero. -/
theorem boundary_reduction_edge :
    SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0} (Int.castAddHom (ZMod 2)) interval 0
        (SSet.tensorNormalizedBoundary.{0, 0, 0} ℤ interval 0 integerEdge) =
      SSet.tensorNormalizedBoundary.{0, 0, 0} (ZMod 2) interval 0
        (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
          (Int.castAddHom (ZMod 2)) interval 1 integerEdge) :=
  congrArg
    (fun f : SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 1 ⟶
      SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 2) interval 0 ↦ f integerEdge)
    (SSet.tensorNormalizedCoefficientMap_boundary.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) interval 0)

/-- The component statement identifies the whole chain operation with the raw reduction
on a coefficient-two tensor already known independently to be nonzero. -/
theorem component_reduction_kills_two :
    (SSet.tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) interval).f 0 (integerVertex 2) = 0 := by
  rw [SSet.tensorNormalizedChainComplexCoefficientMap_f]
  exact reduction_kills_nonzero_two.2

/-- Naturality of the whole comparison evaluated on the integral edge. -/
theorem chain_comparison_reduction_edge :
    (SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 2) interval).hom.f 1
        ((SSet.tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
          (Int.castAddHom (ZMod 2)) interval).f 1 integerEdge) =
      normalizedReduction.f 1
        ((SSet.tensorNormalizedChainIso.{0, 0, 0} ℤ interval).hom.f 1 integerEdge) :=
  congrArg
    (fun f : SSet.tensorNormalizedChainComplex.{0, 0, 0} ℤ interval ⟶
      interval.normalizedChainComplex binaryCoefficients ↦ f.f 1 integerEdge)
    (SSet.tensorNormalizedChainComplexCoefficientMap_comparison.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) interval)

end SimplicialObjectsTest.TensorCoefficientMaps
