/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects.TensorCoefficientMaps
import SimplicialObjects.TensorCoefficientFunctor
public import SimplicialObjects.TensorCoefficientSequences
public import SimplicialObjectsTest.Normalization
import Mathlib.Data.ZMod.Basic

/-!
# Doubling and reduction on standard simplices

Doubling integers followed by reduction modulo two is exact. Reduction preserves
a nonzero degree-zero generator of the standard point. On the standard interval,
it kills a nonzero tensor with coefficient two, but preserves a nonzero generator
with coefficient one. The reduced edge has a nonzero boundary. The compatibility
examples evaluate the comparison, boundary and component formulas on this interval.
The degree-exactness statement is specialized to the same point in degree zero
and interval in degree one.
The coefficient-curried functor preserves the coefficient-one generator and the
nonzero reduced boundary. Doubling coefficients gives a nonzero coefficient-two
tensor, which reduction modulo two kills. The nonsplit integer doubling and
binary reduction sequence also exercises preservation of finite limits and
colimits through Mathlib's `ShortComplex.ShortExact.map_of_exact`. Its evaluated
rows are the same point and interval short complexes, including both arrows.
-/

open CategoryTheory Limits Opposite
open scoped Simplicial TensorProduct
open SimplicialObjectsTest.Normalization

namespace SimplicialObjectsTest.TensorCoefficientMaps

/-- The original integer doubling and reduction maps form an exact pair. -/
private theorem integer_doubling_reduction_exact :
    Function.Exact ((2 : ℕ) • AddMonoidHom.id ℤ) (Int.castAddHom (ZMod 2)) := by
  intro y
  change (y : ZMod 2) = 0 ↔ ∃ x : ℤ, ((2 : ℕ) • AddMonoidHom.id ℤ) x = y
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa only [AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply,
      nsmul_eq_mul, Nat.cast_ofNat] using hx.symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa only [AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply,
      nsmul_eq_mul, Nat.cast_ofNat] using hx.symm⟩

/-- The standard point has a nonzero integer vertex generator with nonzero reduced image. -/
private theorem point_reduction_nonzero_vertex_image :
    ∃ s : (Δ[0] : SSet.{0}).nonDegenerate 0,
      (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] (1 : ℤ)) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ (Δ[0] : SSet.{0}) 0) ≠ 0 ∧
      SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        (Int.castAddHom (ZMod 2)) (Δ[0] : SSet.{0}) 0
        (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] (1 : ℤ))) ≠ 0 := by
  let s : (Δ[0] : SSet.{0}).nonDegenerate 0 :=
    ⟨SSet.stdSimplex.obj₀Equiv.symm 0, by simp [SSet.nondegenerate_zero]⟩
  have himage : SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) (Δ[0] : SSet.{0}) 0
      (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] (1 : ℤ))) ≠ 0 := by
    rw [SSet.tensorNormalizedCoefficientMap_single]
    have hcast : Int.castAddHom (ZMod 2) (1 : ℤ) = 1 := by decide
    rw [hcast]
    intro hzero
    have hc := SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_tmul_apply.{0, 0, 0}
      (ZMod 2) (Δ[0] : SSet.{0}) 0 (Finsupp.single s 1) (1 : ZMod 2) s
    rw [hzero, map_zero] at hc
    exact (zero_ne_one : (0 : ZMod 2) ≠ 1) (by
      simpa using congrArg (fun x : ULift.{0} (ZMod 2) ↦ x.down) hc)
  refine ⟨s, ?_, himage⟩
  intro hzero
  apply himage
  exact (congrArg
    (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
      (Int.castAddHom (ZMod 2)) (Δ[0] : SSet.{0}) 0).hom hzero).trans
    (map_zero
      (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        (Int.castAddHom (ZMod 2)) (Δ[0] : SSet.{0}) 0).hom)

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

/-! ## The coefficient functor and doubling -/

/-- The coefficient functor preserves a nonzero coefficient-one vertex, and its
value at the reduced interval has a nonzero edge boundary. -/
private theorem coefficient_functor_reduction_preserves_nonzero_one :
    ((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}.map
        (AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2)))).app interval).f 0
        (integerVertex 1) = binaryVertex 1 ∧
      binaryVertex 1 ≠ 0 ∧
      (((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}.obj
        (AddCommGrpCat.of (ZMod 2))).obj interval).d 1 0) binaryEdge ≠ 0 := by
  constructor
  · rw [SSet.tensorNormalizedChainComplexCoefficientFunctor_map_app_f]
    exact reduction_preserves_nonzero_one.1
  · constructor
    · exact reduction_preserves_nonzero_one.2
    · intro h
      exact binary_edge_boundary_ne_zero
        ((ConcreteCategory.congr_hom
          ((SSet.tensorNormalizedChainComplex_d.{0, 0, 0} (ZMod 2) interval 1 0).trans
            (SSet.tensorNormalizedDifferential_succ.{0, 0, 0} (ZMod 2) interval 0))
          binaryEdge).symm.trans h)

/-- The sum of two coefficient identities sends one to a nonzero coefficient-two
vertex, which reduction modulo two kills. This specializes the coefficient
additivity formula corresponding to Mathlib's `LinearMap.lTensor_add`, using the
interval computations above. -/
private theorem coefficient_functor_doubling_reduction :
    ((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}.map
        (AddCommGrpCat.ofHom (AddMonoidHom.id ℤ + AddMonoidHom.id ℤ))).app interval).f 0
        (integerVertex 1) = integerVertex 2 ∧
      integerVertex 2 ≠ 0 ∧
      ((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}.map
        (AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2)))).app interval).f 0
        (integerVertex 2) = 0 := by
  refine ⟨?_, reduction_kills_nonzero_two.1, ?_⟩
  · have hadd :
        ((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}.map
          (AddCommGrpCat.ofHom (AddMonoidHom.id ℤ + AddMonoidHom.id ℤ))).app interval).f 0 =
          𝟙 (SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 0) +
            𝟙 (SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 0) := by
      exact Eq.trans
        (SSet.tensorNormalizedChainComplexCoefficientFunctor_map_app_f.{0, 0, 0}
          (AddCommGrpCat.ofHom (AddMonoidHom.id ℤ + AddMonoidHom.id ℤ)) interval 0)
        (Eq.trans
          (SSet.tensorNormalizedCoefficientMap_add.{0, 0, 0, 0} (A := ℤ) (B := ℤ)
            (AddMonoidHom.id ℤ) (AddMonoidHom.id ℤ) interval 0)
          (congrArg
            (fun f : SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 0 ⟶
              SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 0 ↦ f + f)
            (SSet.tensorNormalizedCoefficientMap_id.{0, 0, 0} (A := ℤ) interval 0)))
    calc
      _ = integerVertex 1 + integerVertex 1 :=
        (ConcreteCategory.congr_hom hadd (integerVertex 1)).trans (by rfl)
      _ = integerVertex 2 :=
        (congrArg
          (fun z : (interval.nonDegenerate 0 →₀ ℤ) ⊗[ℤ] ℤ ↦
            (ULift.up z : SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 0))
          (TensorProduct.tmul_add (Finsupp.single initialVertex 1) (1 : ℤ) (1 : ℤ))).symm
  · rw [SSet.tensorNormalizedChainComplexCoefficientFunctor_map_app_f]
    exact reduction_kills_nonzero_two.2

/-- Degree exactness on the standard point in degree zero and interval in degree one. -/
private theorem doubling_reduction_exact_on_point_and_interval :
    Function.Exact
      (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        ((2 : ℕ) • AddMonoidHom.id ℤ) (Δ[0] : SSet.{0}) 0)
      (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        (Int.castAddHom (ZMod 2)) (Δ[0] : SSet.{0}) 0) ∧
    Function.Exact
      (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        ((2 : ℕ) • AddMonoidHom.id ℤ) interval 1)
      (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        (Int.castAddHom (ZMod 2)) interval 1) := by
  constructor
  · exact SSet.tensorNormalizedCoefficientMap_exact.{0, 0, 0, 0, 0}
      ((2 : ℕ) • AddMonoidHom.id ℤ) (Int.castAddHom (ZMod 2))
      integer_doubling_reduction_exact (Δ[0] : SSet.{0}) 0
  · exact SSet.tensorNormalizedCoefficientMap_exact.{0, 0, 0, 0, 0}
      ((2 : ℕ) • AddMonoidHom.id ℤ) (Int.castAddHom (ZMod 2))
      integer_doubling_reduction_exact interval 1

/-! ## Coefficient inputs and short-complex objects -/

@[expose] public section

/-- Integer doubling is injective, independently of tensor endpoint preservation. -/
theorem integer_doubling_injective :
    Function.Injective ((2 : ℕ) • AddMonoidHom.id ℤ) := by
  intro x y h
  apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
  simpa only [AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply,
    nsmul_eq_mul, Nat.cast_ofNat] using h

/-- Reduction modulo two is surjective by Mathlib's integer representatives. -/
theorem binary_reduction_surjective :
    Function.Surjective (Int.castAddHom (ZMod 2)) :=
  ZMod.intCast_surjective

/-- The coefficient exactness input for the same doubling and reduction maps.
This reuses the integer calculation above, without any chain endpoint statement. -/
theorem integer_doubling_reduction_exact_coefficients :
    Function.Exact ((2 : ℕ) • AddMonoidHom.id ℤ) (Int.castAddHom (ZMod 2)) :=
  integer_doubling_reduction_exact

/-- The doubling and reduction short complex on the standard point. -/
noncomputable def pointDoublingReductionShortComplex :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  SSet.tensorNormalizedChainComplexCoefficientShortComplex.{0, 0, 0, 0, 0}
    ((2 : ℕ) • AddMonoidHom.id ℤ) (Int.castAddHom (ZMod 2))
    integer_doubling_reduction_exact_coefficients (Δ[0] : SSet.{0})

/-- The same doubling and reduction short complex on the standard interval. -/
noncomputable def intervalDoublingReductionShortComplex :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  SSet.tensorNormalizedChainComplexCoefficientShortComplex.{0, 0, 0, 0, 0}
    ((2 : ℕ) • AddMonoidHom.id ℤ) (Int.castAddHom (ZMod 2))
    integer_doubling_reduction_exact_coefficients interval

/-- The point short complex has a nonzero vertex with nonzero image under its second
arrow, using its component API and the same integer and binary tensors. -/
theorem point_shortComplex_nonzero_vertex_image :
    ∃ s : (Δ[0] : SSet.{0}).nonDegenerate 0,
      (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] (1 : ℤ)) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ (Δ[0] : SSet.{0}) 0) ≠ 0 ∧
      pointDoublingReductionShortComplex.g.f 0
        (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] (1 : ℤ))) ≠ 0 := by
  obtain ⟨s, hs, himage⟩ := point_reduction_nonzero_vertex_image
  refine ⟨s, hs, ?_⟩
  have himage_eq := congrArg
    (fun f : SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ (Δ[0] : SSet.{0}) 0 ⟶
      SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 2) (Δ[0] : SSet.{0}) 0 ↦
        f.hom (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] (1 : ℤ))))
    (SSet.tensorNormalizedChainComplexCoefficientShortComplex_g_f.{0, 0, 0, 0, 0}
      ((2 : ℕ) • AddMonoidHom.id ℤ) (Int.castAddHom (ZMod 2))
      integer_doubling_reduction_exact_coefficients (Δ[0] : SSet.{0}) 0)
  intro hzero
  exact himage (himage_eq.symm.trans hzero)

/-- The interval short complex preserves the same nonzero coefficient-one vertex
under its second arrow, independently of endpoint preservation. -/
theorem interval_shortComplex_preserves_nonzero_one :
    intervalDoublingReductionShortComplex.g.f 0
        (ULift.up (Finsupp.single
          (⟨vertex 0, vertex_nondegenerate 0⟩ : interval.nonDegenerate 0) 1 ⊗ₜ[ℤ] (1 : ℤ)) :
          SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 0) =
      (ULift.up (Finsupp.single
        (⟨vertex 0, vertex_nondegenerate 0⟩ : interval.nonDegenerate 0) 1 ⊗ₜ[ℤ] (1 : ZMod 2)) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 2) interval 0) ∧
      (ULift.up (Finsupp.single
        (⟨vertex 0, vertex_nondegenerate 0⟩ : interval.nonDegenerate 0) 1 ⊗ₜ[ℤ] (1 : ZMod 2)) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 2) interval 0) ≠ 0 := by
  change intervalDoublingReductionShortComplex.g.f 0 (integerVertex 1) = binaryVertex 1 ∧
    binaryVertex 1 ≠ 0
  have himage_eq := congrArg
    (fun f : SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 0 ⟶
      SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 2) interval 0 ↦
        f.hom (integerVertex 1))
    (SSet.tensorNormalizedChainComplexCoefficientShortComplex_g_f.{0, 0, 0, 0, 0}
      ((2 : ℕ) • AddMonoidHom.id ℤ) (Int.castAddHom (ZMod 2))
      integer_doubling_reduction_exact_coefficients interval 0)
  exact ⟨himage_eq.trans reduction_preserves_nonzero_one.1,
    reduction_preserves_nonzero_one.2⟩

end

/-! ## Preservation of the integer coefficient sequence -/

private noncomputable def doublingReductionCoefficientSequence :
    ShortComplex AddCommGrpCat.{0} where
  X₁ := AddCommGrpCat.of ℤ
  X₂ := AddCommGrpCat.of ℤ
  X₃ := AddCommGrpCat.of (ZMod 2)
  f := AddCommGrpCat.ofHom ((2 : ℕ) • AddMonoidHom.id ℤ)
  g := AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))
  zero := by
    apply AddCommGrpCat.int_hom_ext
    exact integer_doubling_reduction_exact_coefficients.apply_apply_eq_zero (1 : ℤ)

private theorem doublingReductionCoefficientSequence_shortExact :
    doublingReductionCoefficientSequence.ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact (ShortComplex.ab_exact_iff_function_exact _).2
      integer_doubling_reduction_exact_coefficients
  · exact (AddCommGrpCat.mono_iff_injective _).2 integer_doubling_injective
  · exact (AddCommGrpCat.epi_iff_surjective _).2 binary_reduction_surjective

private noncomputable def doublingReductionTensorRow :
    ShortComplex (SSet.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  doublingReductionCoefficientSequence.map
    (SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0})

/-- Both finite-preservation instances are used by the stock short-exact mapping theorem. -/
private theorem doublingReductionTensorRow_shortExact :
    doublingReductionTensorRow.ShortExact :=
  ShortComplex.ShortExact.map_of_exact doublingReductionCoefficientSequence_shortExact
    (SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0})

/-- The whole evaluated row identifies all three point complexes and both chain arrows. -/
private theorem doublingReductionTensorRow_point :
    doublingReductionTensorRow.map
        ((evaluation SSet.{0} (ChainComplex (ModuleCat.{0} ℤ) ℕ)).obj
          (Δ[0] : SSet.{0})) = pointDoublingReductionShortComplex :=
  SSet.tensorNormalizedChainComplexCoefficientFunctor_map_shortComplex.{0, 0, 0}
    doublingReductionCoefficientSequence integer_doubling_reduction_exact_coefficients
    (Δ[0] : SSet.{0})

/-- The interval row retains the same signed complexes and both coefficient arrows. -/
private theorem doublingReductionTensorRow_interval :
    doublingReductionTensorRow.map
        ((evaluation SSet.{0} (ChainComplex (ModuleCat.{0} ℤ) ℕ)).obj interval) =
      intervalDoublingReductionShortComplex :=
  SSet.tensorNormalizedChainComplexCoefficientFunctor_map_shortComplex.{0, 0, 0}
    doublingReductionCoefficientSequence integer_doubling_reduction_exact_coefficients interval

private theorem doublingReductionTensorRow_point_nonzero :
    ∃ s : (Δ[0] : SSet.{0}).nonDegenerate 0,
      (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] (1 : ℤ)) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ (Δ[0] : SSet.{0}) 0) ≠ 0 ∧
      (doublingReductionTensorRow.g.app (Δ[0] : SSet.{0})).f 0
        (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] (1 : ℤ))) ≠ 0 := by
  have hg : doublingReductionTensorRow.g.app (Δ[0] : SSet.{0}) =
      pointDoublingReductionShortComplex.g := rfl
  rw [hg]
  exact point_shortComplex_nonzero_vertex_image

/-- Doubling, its nonzero image killed by reduction, the surviving binary generator,
and the nonzero reduced signed edge boundary all occur in the mapped interval row. -/
private theorem doublingReductionTensorRow_interval_nonzero :
    (doublingReductionTensorRow.f.app interval).f 0 (integerVertex 1) =
        integerVertex 2 ∧
    integerVertex 2 ≠ 0 ∧
    (doublingReductionTensorRow.g.app interval).f 0 (integerVertex 2) = 0 ∧
    (doublingReductionTensorRow.g.app interval).f 0 (integerVertex 1) =
        binaryVertex 1 ∧
    binaryVertex 1 ≠ 0 ∧
    ((doublingReductionTensorRow.X₃.obj interval).d 1 0) binaryEdge ≠ 0 := by
  have hd := coefficient_functor_doubling_reduction
  have hr := coefficient_functor_reduction_preserves_nonzero_one
  refine ⟨?_, hd.2.1, hd.2.2, hr.1, hr.2.1, hr.2.2⟩
  change ((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}.map
    (AddCommGrpCat.ofHom ((2 : ℕ) • AddMonoidHom.id ℤ))).app interval).f 0
      (integerVertex 1) = integerVertex 2
  simpa only [two_smul] using hd.1

end SimplicialObjectsTest.TensorCoefficientMaps

namespace SimplicialObjectsTest.TensorCoefficientMaps

/-- The bundled comparison sends the reduced generator of the standard point
to a nonzero normalized chain. -/
private theorem coefficient_comparison_point_nonzero :
    ∃ s : (Δ[0] : SSet.{0}).nonDegenerate 0,
      let z : SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ (Δ[0] : SSet.{0}) 0 :=
        ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] (1 : ℤ))
      z ≠ 0 ∧
        (((SSet.tensorNormalizedChainComplexCoefficientNatIso.{0, 0, 0}).hom.app
            (AddCommGrpCat.of (ZMod 2))).app (Δ[0] : SSet.{0})).f 0
          ((((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}).map
            (AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2)))).app
              (Δ[0] : SSet.{0})).f 0 z) ≠ 0 := by
  obtain ⟨s, hs, himage⟩ := point_reduction_nonzero_vertex_image
  refine ⟨s, hs, ?_⟩
  rw [SSet.tensorNormalizedChainComplexCoefficientNatIso_hom_app_app,
    SSet.tensorNormalizedChainComplexCoefficientFunctor_map_app_f]
  let e := (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 0).mapIso
    (SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 2) (Δ[0] : SSet.{0}))
  intro hzero
  apply himage
  exact e.toLinearEquiv.injective (hzero.trans (map_zero e.toLinearEquiv).symm)

/-- Canonical normalized coefficient reduction kills the comparison of a
nonzero coefficient-two vertex and preserves the nonzero coefficient-one image. -/
private theorem normalized_coefficient_reduction_vertices :
    let θ := SSet.tensorNormalizedChainComplexCoefficientNatIso.{0, 0, 0}
    let r := AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))
    let n := ((AddCommGrpCat.uliftIntModuleFunctor.{0, 0} ⋙
      SSet.normalizedChainComplexFunctor (C := ModuleCat.{0} ℤ)).map r).app interval
    integerVertex 2 ≠ 0 ∧
      n.f 0 (((θ.hom.app (AddCommGrpCat.of ℤ)).app interval).f 0 (integerVertex 2)) = 0 ∧
      n.f 0 (((θ.hom.app (AddCommGrpCat.of ℤ)).app interval).f 0 (integerVertex 1)) =
        ((θ.hom.app (AddCommGrpCat.of (ZMod 2))).app interval).f 0 (binaryVertex 1) ∧
      ((θ.hom.app (AddCommGrpCat.of (ZMod 2))).app interval).f 0
        (binaryVertex 1) ≠ 0 := by
  dsimp only
  let F := SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}
  let G := AddCommGrpCat.uliftIntModuleFunctor.{0, 0} ⋙
    SSet.normalizedChainComplexFunctor (C := ModuleCat.{0} ℤ)
  let θ : F ≅ G := SSet.tensorNormalizedChainComplexCoefficientNatIso.{0, 0, 0}
  let r : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (ZMod 2) :=
    AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))
  let a : ((F.obj (AddCommGrpCat.of ℤ)).obj interval).X 0 ⟶
      ((F.obj (AddCommGrpCat.of (ZMod 2))).obj interval).X 0 :=
    ((F.map r).app interval).f 0
  let b : ((F.obj (AddCommGrpCat.of (ZMod 2))).obj interval).X 0 ⟶
      ((G.obj (AddCommGrpCat.of (ZMod 2))).obj interval).X 0 :=
    ((θ.hom.app (AddCommGrpCat.of (ZMod 2))).app interval).f 0
  let c : ((F.obj (AddCommGrpCat.of ℤ)).obj interval).X 0 ⟶
      ((G.obj (AddCommGrpCat.of ℤ)).obj interval).X 0 :=
    ((θ.hom.app (AddCommGrpCat.of ℤ)).app interval).f 0
  let d : ((G.obj (AddCommGrpCat.of ℤ)).obj interval).X 0 ⟶
      ((G.obj (AddCommGrpCat.of (ZMod 2))).obj interval).X 0 :=
    ((G.map r).app interval).f 0
  have hnat : a ≫ b = c ≫ d := by
    simpa only [NatTrans.comp_app, HomologicalComplex.comp_f] using
      (HomologicalComplex.congr_hom
        (CategoryTheory.congr_app (θ.hom.naturality r) interval) 0)
  have happ (x : ((F.obj (AddCommGrpCat.of ℤ)).obj interval).X 0) :
      b.hom (a.hom x) = d.hom (c.hom x) :=
    (ModuleCat.comp_apply (R := ℤ) a b x).symm.trans
      ((congrArg
        (fun k : ((F.obj (AddCommGrpCat.of ℤ)).obj interval).X 0 ⟶
          ((G.obj (AddCommGrpCat.of (ZMod 2))).obj interval).X 0 ↦ k.hom x)
        hnat).trans (ModuleCat.comp_apply (R := ℤ) c d x))
  have ha_two : a.hom (integerVertex 2) = 0 := by
    change (((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}).map
      (AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2)))).app interval).f 0
        (integerVertex 2) = 0
    rw [SSet.tensorNormalizedChainComplexCoefficientFunctor_map_app_f]
    exact reduction_kills_nonzero_two.2
  have ha_one : a.hom (integerVertex 1) = binaryVertex 1 := by
    change (((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}).map
      (AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2)))).app interval).f 0
        (integerVertex 1) = binaryVertex 1
    rw [SSet.tensorNormalizedChainComplexCoefficientFunctor_map_app_f]
    exact reduction_preserves_nonzero_one.1
  refine ⟨reduction_kills_nonzero_two.1, ?_, ?_, ?_⟩
  · exact (happ (integerVertex 2)).symm.trans
      ((congrArg b.hom ha_two).trans (map_zero b.hom))
  · exact (happ (integerVertex 1)).symm.trans (congrArg b.hom ha_one)
  · rw [SSet.tensorNormalizedChainComplexCoefficientNatIso_hom_app_app]
    let e := (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 0).mapIso
      (SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 2) interval)
    intro hzero
    apply reduction_preserves_nonzero_one.2
    exact e.toLinearEquiv.injective (hzero.trans (map_zero e.toLinearEquiv).symm)

/-- The coefficient-cokernel comparison has a nonzero value on the vertex class
modulo integer doubling in the original coefficient sequence. -/
private theorem coefficient_coker_doubling_vertex_nonzero :
    let projection := cokernel.π
      (((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}).map
        doublingReductionCoefficientSequence.f).app interval)
    let ψ := SSet.tensorNormalizedChainComplexCoefficientCokerNatIso.{0, 0, 0} interval
    projection.f 0 (integerVertex 1) ≠ 0 ∧
      (ψ.hom.app (Arrow.mk doublingReductionCoefficientSequence.f)).f 0
        (projection.f 0 (integerVertex 1)) ≠ 0 := by
  dsimp only
  let f := ((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}).map
    doublingReductionCoefficientSequence.f).app interval
  let g := ((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}).map
    doublingReductionCoefficientSequence.g).app interval
  have hfg : f ≫ g = 0 :=
    CategoryTheory.congr_app doublingReductionTensorRow.zero interval
  let d := cokernel.desc f g hfg
  have hd : (cokernel.π f).f 0 ≫ d.f 0 = g.f 0 :=
    HomologicalComplex.congr_hom (cokernel.π_desc f g hfg) 0
  have hd_app : d.f 0 ((cokernel.π f).f 0 (integerVertex 1)) =
      g.f 0 (integerVertex 1) :=
    (ModuleCat.comp_apply (R := ℤ)
      (M := (doublingReductionTensorRow.X₂.obj interval).X 0)
      (N := (cokernel f).X 0)
      (O := (doublingReductionTensorRow.X₃.obj interval).X 0)
      ((cokernel.π f).f 0) (d.f 0) (integerVertex 1)).symm.trans
        (congrArg
          (fun k : (doublingReductionTensorRow.X₂.obj interval).X 0 ⟶
            (doublingReductionTensorRow.X₃.obj interval).X 0 ↦
              k.hom (integerVertex 1)) hd)
  have hclass : (cokernel.π f).f 0 (integerVertex 1) ≠ 0 := by
    intro hzero
    apply reduction_preserves_nonzero_one.2
    have hg_zero : g.f 0 (integerVertex 1) = 0 :=
      hd_app.symm.trans
        ((congrArg (d.f 0).hom hzero).trans (map_zero (d.f 0).hom))
    exact coefficient_functor_reduction_preserves_nonzero_one.1.symm.trans hg_zero
  refine ⟨hclass, ?_⟩
  let e := (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 0).mapIso
    ((SSet.tensorNormalizedChainComplexCoefficientCokerNatIso.{0, 0, 0} interval).app
      (Arrow.mk doublingReductionCoefficientSequence.f))
  intro hzero
  apply hclass
  exact e.toLinearEquiv.injective (hzero.trans (map_zero e.toLinearEquiv).symm)

/-- The zero coefficient arrow kills the normalized image of the same interval edge. -/
private theorem normalized_coefficient_zero_edge :
    (((AddCommGrpCat.uliftIntModuleFunctor.{0, 0} ⋙
        SSet.normalizedChainComplexFunctor (C := ModuleCat.{0} ℤ)).map
      (0 : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (ZMod 2))).app interval).f 1
        ((((SSet.tensorNormalizedChainComplexCoefficientNatIso.{0, 0, 0}).hom.app
          (AddCommGrpCat.of ℤ)).app interval).f 1 integerEdge) = 0 := by
  let F := SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}
  let G := AddCommGrpCat.uliftIntModuleFunctor.{0, 0} ⋙
    SSet.normalizedChainComplexFunctor (C := ModuleCat.{0} ℤ)
  let θ : F ≅ G := SSet.tensorNormalizedChainComplexCoefficientNatIso.{0, 0, 0}
  let g₀ : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (ZMod 2) := 0
  let a : ((F.obj (AddCommGrpCat.of ℤ)).obj interval).X 1 ⟶
      ((F.obj (AddCommGrpCat.of (ZMod 2))).obj interval).X 1 :=
    ((F.map g₀).app interval).f 1
  let b : ((F.obj (AddCommGrpCat.of (ZMod 2))).obj interval).X 1 ⟶
      ((G.obj (AddCommGrpCat.of (ZMod 2))).obj interval).X 1 :=
    ((θ.hom.app (AddCommGrpCat.of (ZMod 2))).app interval).f 1
  let c : ((F.obj (AddCommGrpCat.of ℤ)).obj interval).X 1 ⟶
      ((G.obj (AddCommGrpCat.of ℤ)).obj interval).X 1 :=
    ((θ.hom.app (AddCommGrpCat.of ℤ)).app interval).f 1
  let d : ((G.obj (AddCommGrpCat.of ℤ)).obj interval).X 1 ⟶
      ((G.obj (AddCommGrpCat.of (ZMod 2))).obj interval).X 1 :=
    ((G.map g₀).app interval).f 1
  have hnat : a ≫ b = c ≫ d := by
    simpa only [NatTrans.comp_app, HomologicalComplex.comp_f] using
      (HomologicalComplex.congr_hom
        (CategoryTheory.congr_app (θ.hom.naturality g₀) interval) 1)
  have happ : b.hom (a.hom integerEdge) = d.hom (c.hom integerEdge) :=
    (ModuleCat.comp_apply (R := ℤ) a b integerEdge).symm.trans
      ((congrArg
        (fun k : ((F.obj (AddCommGrpCat.of ℤ)).obj interval).X 1 ⟶
          ((G.obj (AddCommGrpCat.of (ZMod 2))).obj interval).X 1 ↦ k.hom integerEdge)
        hnat).trans (ModuleCat.comp_apply (R := ℤ) c d integerEdge))
  have ha_zero : a.hom integerEdge = 0 := by
    change (((SSet.tensorNormalizedChainComplexCoefficientFunctor.{0, 0, 0}).map
      (0 : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (ZMod 2))).app interval).f 1
        integerEdge = 0
    rw [SSet.tensorNormalizedChainComplexCoefficientFunctor_map_app_f,
      AddCommGrpCat.hom_zero]
    exact zero_coefficient_edge
  exact happ.symm.trans ((congrArg b.hom ha_zero).trans (map_zero b.hom))

end SimplicialObjectsTest.TensorCoefficientMaps
