/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects.TensorMaps
import SimplicialObjects.TensorCoefficientMaps
import SimplicialObjectsTest.Normalization
import Mathlib.Data.ZMod.Basic

/-!
# Tensor maps on the standard simplicial interval

The identity retains the interval edge. The simplicial collapse to `Δ[0]` sends
that nondegenerate edge to a degenerate edge, but sends either vertex to a
nonzero tensor generator with coefficients in `ZMod 4`. The independently
specified tensor boundary is terminal vertex minus initial vertex and is nonzero.

The generator computations and boundary calculations do not use comparison
naturality. Separate specializations evaluate the comparison equations on these
same standard simplices.
-/

open CategoryTheory Opposite
open scoped Simplicial TensorProduct
open SimplicialObjectsTest.Normalization

namespace SimplicialObjectsTest.TensorMaps

universe a p

private abbrev point : SSet.{0} := Δ[0]

private def pointVertex : point _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm 0

private theorem pointVertex_nondegenerate : pointVertex ∈ point.nonDegenerate 0 := by
  simp [SSet.nondegenerate_zero]

private def pointBasis : point.nonDegenerate 0 :=
  ⟨pointVertex, pointVertex_nondegenerate⟩

private def intervalVertex (i : Fin 2) : interval.nonDegenerate 0 :=
  ⟨vertex i, vertex_nondegenerate i⟩

private def intervalEdge : interval.nonDegenerate 1 := ⟨edge, edge_nondegenerate⟩

/-- The simplicial map induced by the unique order map `[1] → [0]`. -/
private def collapse : interval ⟶ point :=
  SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1))

private theorem collapse_vertex (i : Fin 2) : collapse.app _ (vertex i) = pointVertex := by
  apply SSet.stdSimplex.ext
  intro j
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

private theorem collapse_edge :
    collapse.app _ edge = point.σ (0 : Fin 1) pointVertex := by
  apply SSet.stdSimplex.ext
  intro j
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- The source is nondegenerate, while its image under the simplicial collapse is degenerate. -/
private theorem collapse_edge_degenerate :
    edge ∈ interval.nonDegenerate 1 ∧ collapse.app _ edge ∈ point.degenerate 1 := by
  refine ⟨edge_nondegenerate, ?_⟩
  rw [collapse_edge]
  exact point.σ_mem_degenerate (0 : Fin 1) pointVertex

private theorem terminal_ne_initial : intervalVertex 1 ≠ intervalVertex 0 := by
  intro h
  have hv := congrArg
    (fun s : interval.nonDegenerate 0 ↦ SSet.stdSimplex.obj₀Equiv s.val) h
  have hfin : (1 : Fin 2) = 0 :=
    ((SSet.stdSimplex.obj₀Equiv.{0} (n := 1)).apply_symm_apply 1).symm.trans
      (hv.trans ((SSet.stdSimplex.obj₀Equiv.{0} (n := 1)).apply_symm_apply 0))
  exact (by decide : (1 : Fin 2) ≠ 0) hfin

/-- The alternating integral boundary has the terminal-minus-initial convention. -/
private theorem integral_edge_boundary :
    interval.normalizedIntegralBoundary 0 (interval.normalizedIntegralSimplex edge) =
      Finsupp.single (intervalVertex 1) 1 - Finsupp.single (intervalVertex 0) 1 := by
  rw [interval.normalizedIntegralSimplex_of_mem_nonDegenerate edge edge_nondegenerate,
    SSet.normalizedIntegralBoundary_single, Fin.sum_univ_two]
  simp [edge_face_zero, edge_face_one, intervalVertex, sub_eq_add_neg]

private noncomputable def tensorEdge :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 1 :=
  ULift.up (interval.normalizedIntegralSimplex edge ⊗ₜ[ℤ] (1 : ZMod 4))

private noncomputable def tensorVertex (i : Fin 2) :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0 :=
  ULift.up (Finsupp.single (intervalVertex i) 1 ⊗ₜ[ℤ] (1 : ZMod 4))

/-- The tensor boundary is calculated from the independent alternating integral boundary. -/
private theorem tensor_edge_boundary :
    SSet.tensorNormalizedBoundary.{0, 0, 0} (ZMod 4) interval 0 tensorEdge =
      (ULift.up (Finsupp.single (intervalVertex 1) 1 ⊗ₜ[ℤ] (1 : ZMod 4)) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0) -
      (ULift.up (Finsupp.single (intervalVertex 0) 1 ⊗ₜ[ℤ] (1 : ZMod 4)) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0) := by
  rw [tensorEdge, SSet.tensorNormalizedBoundary_tmul, integral_edge_boundary,
    TensorProduct.sub_tmul]
  rfl

/-- The terminal coefficient of the tensor boundary is one modulo four. -/
private theorem tensor_edge_boundary_terminal_coordinate :
    ((SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0} (ZMod 4) interval 0).hom
      (SSet.tensorNormalizedBoundary.{0, 0, 0} (ZMod 4) interval 0 tensorEdge)
        (intervalVertex 1)).down = (1 : ZMod 4) := by
  rw [tensorEdge, SSet.tensorNormalizedBoundary_tmul,
    SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_tmul_apply, integral_edge_boundary]
  simp [terminal_ne_initial]

/-- Torsion coefficients do not make this independently specified boundary zero. -/
private theorem tensor_edge_boundary_ne_zero :
    SSet.tensorNormalizedBoundary.{0, 0, 0} (ZMod 4) interval 0 tensorEdge ≠ 0 := by
  intro h
  have hc := tensor_edge_boundary_terminal_coordinate
  rw [h, map_zero] at hc
  exact (by decide : (0 : ZMod 4) ≠ 1) hc

private theorem tensor_edge_ne_zero : tensorEdge ≠ 0 := by
  intro h
  apply tensor_edge_boundary_ne_zero
  rw [h, map_zero]

private noncomputable def pointTensorVertex :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) point 0 :=
  ULift.up (Finsupp.single pointBasis 1 ⊗ₜ[ℤ] (1 : ZMod 4))

private theorem point_tensor_vertex_ne_zero : pointTensorVertex ≠ 0 := by
  intro h
  have hc := SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_single.{0, 0, 0}
    (ZMod 4) point 0 pointBasis (1 : ZMod 4)
  change (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0}
    (ZMod 4) point 0).hom pointTensorVertex = _ at hc
  rw [h, map_zero] at hc
  have hzero : (0 : ZMod 4) = 1 := by
    simpa using congrArg
      (fun z : point.nonDegenerate 0 →₀ ULift.{0} (ZMod 4) ↦ (z pointBasis).down) hc
  exact (by decide : (0 : ZMod 4) ≠ 1) hzero

/-! ## Generator images under the identity and collapse -/

private theorem integral_identity_edge :
    SSet.normalizedIntegralMap (𝟙 interval) 1 (Finsupp.single intervalEdge 1) =
      Finsupp.single intervalEdge 1 := by
  rw [SSet.normalizedIntegralMap_single]
  change interval.normalizedIntegralSimplex edge = _
  exact interval.normalizedIntegralSimplex_of_mem_nonDegenerate edge edge_nondegenerate

private theorem integral_collapse_edge :
    SSet.normalizedIntegralMap collapse 1 (interval.normalizedIntegralSimplex edge) = 0 := by
  rw [SSet.normalizedIntegralMap_simplex]
  exact point.normalizedIntegralSimplex_of_mem_degenerate _ collapse_edge_degenerate.2

private theorem integral_collapse_vertex (i : Fin 2) :
    SSet.normalizedIntegralMap collapse 0 (Finsupp.single (intervalVertex i) 1) =
      Finsupp.single pointBasis 1 := by
  rw [SSet.normalizedIntegralMap_single]
  change point.normalizedIntegralSimplex (collapse.app _ (vertex i)) = _
  rw [collapse_vertex]
  exact point.normalizedIntegralSimplex_of_mem_nonDegenerate pointVertex pointVertex_nondegenerate

private theorem tensor_identity_edge :
    SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) (𝟙 interval) 1 tensorEdge =
      tensorEdge := by
  have h :=
    (ConcreteCategory.congr_hom (NatTrans.id_app interval (op ⦋1⦌)) edge).trans
      (ConcreteCategory.id_apply (X := interval.obj (op ⦋1⦌)) edge)
  simpa only [tensorEdge, h] using
    (SSet.tensorNormalizedChainComplexXMap_simplex.{0, 0, 0}
      (ZMod 4) (𝟙 interval) edge (1 : ZMod 4))

/-- Collapse kills the nonzero edge tensor because its image simplex is degenerate. -/
private theorem tensor_collapse_edge :
    SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 1 tensorEdge = 0 := by
  rw [tensorEdge, SSet.tensorNormalizedChainComplexXMap_simplex,
    point.normalizedIntegralSimplex_of_mem_degenerate _ collapse_edge_degenerate.2,
    TensorProduct.zero_tmul]
  rfl

/-- The same simplicial collapse works for arbitrary coefficients and independent padding. -/
private theorem tensor_collapse_vertex (A : Type a) [AddCommGroup A] (i : Fin 2) (x : A) :
    SSet.tensorNormalizedChainComplexXMap.{a, 0, p} A collapse 0
        (ULift.up (Finsupp.single (intervalVertex i) 1 ⊗ₜ[ℤ] x)) =
      (ULift.up (Finsupp.single pointBasis 1 ⊗ₜ[ℤ] x) :
        SSet.tensorNormalizedChainComplexX.{a, 0, p} A point 0) := by
  rw [SSet.tensorNormalizedChainComplexXMap_single]
  change ULift.up (point.normalizedIntegralSimplex (collapse.app _ (vertex i)) ⊗ₜ[ℤ] x) = _
  rw [collapse_vertex,
    point.normalizedIntegralSimplex_of_mem_nonDegenerate pointVertex pointVertex_nondegenerate]
  rfl

/-- In degree zero the collapse has nonzero images with coefficients modulo four. -/
private theorem tensor_collapse_vertex_ne_zero (i : Fin 2) :
    SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 0 (tensorVertex i) ≠ 0 := by
  rw [tensorVertex, tensor_collapse_vertex]
  exact point_tensor_vertex_ne_zero

/-- A degenerate source edge has zero image as well. -/
private theorem tensor_collapse_degenerate_edge (x : ZMod 4) :
    SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 1
      (ULift.up (interval.normalizedIntegralSimplex
        (interval.σ (0 : Fin 1) (vertex 0)) ⊗ₜ[ℤ] x)) = 0 := by
  rw [SSet.tensorNormalizedChainComplexXMap_simplex,
    point.normalizedIntegralSimplex_of_mem_degenerate _
      (SSet.degenerate_app_apply (interval.σ_mem_degenerate (0 : Fin 1) (vertex 0)) collapse),
    TensorProduct.zero_tmul]
  rfl

/-- The tensor-chain functor retains the same nonzero edge under the identity. -/
private theorem identity_functor_edge :
    ((SSet.tensorNormalizedChainComplexFunctor.{0, 0, 0} (ZMod 4)).map (𝟙 interval)).f 1
      tensorEdge = tensorEdge := by
  simp only [SSet.tensorNormalizedChainComplexFunctor_map, SSet.tensorNormalizedChainComplexMap_id,
    HomologicalComplex.id_f]
  exact ConcreteCategory.id_apply
    (X := (SSet.tensorNormalizedChainComplex.{0, 0, 0} (ZMod 4) interval).X 1) tensorEdge

/-! ## Comparison equations on the same standard simplices

These specializations use the comparison and component statements. The input
geometry, raw map computations and nonzero boundary above are independent of
these equations.
-/

private abbrev coefficients : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ULift.{0} (ZMod 4))

/-- Degree comparison naturality evaluated on either nonzero vertex image of collapse. -/
private theorem collapse_degree_comparison_vertex (i : Fin 2) :
    (SSet.normalizedChainComplexMap collapse coefficients).f 0
        ((SSet.tensorNormalizedChainComplexXIso.{0, 0, 0} (ZMod 4) interval 0).hom
          (tensorVertex i)) =
      (SSet.tensorNormalizedChainComplexXIso.{0, 0, 0} (ZMod 4) point 0).hom
        (SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 0 (tensorVertex i)) := by
  have h := congrArg
    (fun k : SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0 ⟶
        (point.normalizedChainComplex coefficients).X 0 ↦ k.hom (tensorVertex i))
    (SSet.tensorNormalizedChainComplexXIso_hom_naturality.{0, 0, 0} (ZMod 4) collapse 0)
  change (SSet.normalizedChainComplexMap collapse coefficients).f 0
      ((SSet.tensorNormalizedChainComplexXIso.{0, 0, 0} (ZMod 4) interval 0).hom (tensorVertex i)) =
    (SSet.tensorNormalizedChainComplexXIso.{0, 0, 0} (ZMod 4) point 0).hom
      (SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 0 (tensorVertex i)) at h
  exact h

/-- Tensor-map compatibility with the independent signed boundary, evaluated on the edge. -/
private theorem collapse_degree_boundary :
    SSet.tensorNormalizedBoundary.{0, 0, 0} (ZMod 4) point 0
        (SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 1 tensorEdge) =
      SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 0
        (SSet.tensorNormalizedBoundary.{0, 0, 0} (ZMod 4) interval 0 tensorEdge) := by
  have h := congrArg
    (fun k : SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 1 ⟶
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) point 0 ↦ k.hom tensorEdge)
    (SSet.tensorNormalizedChainComplexXMap_d.{0, 0, 0} (ZMod 4) collapse 1 0)
  change SSet.tensorNormalizedDifferential.{0, 0, 0} (ZMod 4) point 1 0
      (SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 1 tensorEdge) =
    SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 0
      (SSet.tensorNormalizedDifferential.{0, 0, 0} (ZMod 4) interval 1 0 tensorEdge) at h
  simpa only [SSet.tensorNormalizedDifferential_succ] using h

/-- The component formula gives the same nonzero vertex image for the whole chain map. -/
private theorem collapse_chain_vertex (i : Fin 2) :
    (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4) collapse).f 0 (tensorVertex i) =
      pointTensorVertex := by
  have h := congrArg
    (fun k : SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0 ⟶
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) point 0 ↦ k.hom (tensorVertex i))
    (SSet.tensorNormalizedChainComplexMap_f.{0, 0, 0} (ZMod 4) collapse 0)
  exact h.trans (tensor_collapse_vertex (ZMod 4) i (1 : ZMod 4))

/-- Whole-chain naturality evaluated on either of the two nonzero vertex tensors. -/
private theorem collapse_chain_comparison_vertex (i : Fin 2) :
    (SSet.normalizedChainComplexMap collapse coefficients).f 0
        ((SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 4) interval).hom.f 0 (tensorVertex i)) =
      (SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 4) point).hom.f 0
        (((SSet.tensorNormalizedChainComplexFunctor.{0, 0, 0} (ZMod 4)).map collapse).f 0
          (tensorVertex i)) := by
  have h := congrArg
    (fun k : SSet.tensorNormalizedChainComplex.{0, 0, 0} (ZMod 4) interval ⟶
        point.normalizedChainComplex coefficients ↦ (k.f 0).hom (tensorVertex i))
    (SSet.tensorNormalizedChainIso_hom_naturality.{0, 0, 0} (ZMod 4) collapse)
  change (SSet.normalizedChainComplexMap collapse coefficients).f 0
      ((SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 4) interval).hom.f 0 (tensorVertex i)) =
    (SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 4) point).hom.f 0
      (((SSet.tensorNormalizedChainComplexFunctor.{0, 0, 0} (ZMod 4)).map collapse).f 0
        (tensorVertex i)) at h
  exact h

/-! ## Simultaneous collapse and coefficient change -/

/-- Collapse followed by doubling coefficients sends a coefficient-one vertex to a
nonzero coefficient-two vertex over `ZMod 4`, independently of mixed naturality. -/
private theorem collapse_coefficient_vertex_nonzero :
    SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        ((2 : ℕ) • AddMonoidHom.id (ZMod 4)) point 0
        (SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 0 (tensorVertex 0)) =
      (ULift.up (Finsupp.single pointBasis 1 ⊗ₜ[ℤ] (2 : ZMod 4)) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) point 0) ∧
    SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        ((2 : ℕ) • AddMonoidHom.id (ZMod 4)) point 0
        (SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 0 (tensorVertex 0)) ≠
      0 := by
  have himage :
      SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
          ((2 : ℕ) • AddMonoidHom.id (ZMod 4)) point 0
          (SSet.tensorNormalizedChainComplexXMap.{0, 0, 0}
            (ZMod 4) collapse 0 (tensorVertex 0)) =
        (ULift.up (Finsupp.single pointBasis 1 ⊗ₜ[ℤ] (2 : ZMod 4)) :
          SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) point 0) := by
    rw [tensorVertex, tensor_collapse_vertex, SSet.tensorNormalizedCoefficientMap_single]
    exact congrArg
      (fun x : ZMod 4 ↦ (ULift.up (Finsupp.single pointBasis 1 ⊗ₜ[ℤ] x) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) point 0))
      (by decide : ((2 : ℕ) • AddMonoidHom.id (ZMod 4)) (1 : ZMod 4) = 2)
  refine ⟨himage, ?_⟩
  rw [himage]
  intro hzero
  have hc := SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_single.{0, 0, 0}
    (ZMod 4) point 0 pointBasis (2 : ZMod 4)
  rw [hzero, map_zero] at hc
  have htwo : (0 : ZMod 4) = 2 := by
    simpa using congrArg
      (fun z : point.nonDegenerate 0 →₀ ULift.{0} (ZMod 4) ↦ (z pointBasis).down) hc
  exact (by decide : (0 : ZMod 4) ≠ 2) htwo

/-- The degree mixed square evaluated on the same coefficient-one vertex of collapse. -/
private theorem collapse_degree_coefficient_vertex :
    SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
        ((2 : ℕ) • AddMonoidHom.id (ZMod 4)) point 0
        (SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 0 (tensorVertex 0)) =
      SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) collapse 0
        (SSet.tensorNormalizedCoefficientMap.{0, 0, 0, 0}
          ((2 : ℕ) • AddMonoidHom.id (ZMod 4)) interval 0 (tensorVertex 0)) :=
  congrArg
    (fun k : SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0 ⟶
      SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) point 0 ↦ k (tensorVertex 0))
    (SSet.tensorNormalizedCoefficientMap_naturality.{0, 0, 0, 0}
      collapse ((2 : ℕ) • AddMonoidHom.id (ZMod 4)) 0)

/-- The whole mixed square evaluated on that vertex uses the same collapse and doubling. -/
private theorem collapse_chain_coefficient_vertex :
    (SSet.tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
        ((2 : ℕ) • AddMonoidHom.id (ZMod 4)) point).f 0
        ((SSet.tensorNormalizedChainComplexMap.{0, 0, 0}
          (ZMod 4) collapse).f 0 (tensorVertex 0)) =
      (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4) collapse).f 0
        ((SSet.tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, 0}
          ((2 : ℕ) • AddMonoidHom.id (ZMod 4)) interval).f 0 (tensorVertex 0)) :=
  congrArg
    (fun k : SSet.tensorNormalizedChainComplex.{0, 0, 0} (ZMod 4) interval ⟶
      SSet.tensorNormalizedChainComplex.{0, 0, 0} (ZMod 4) point ↦ k.f 0 (tensorVertex 0))
    (SSet.tensorNormalizedChainComplexCoefficientMap_naturality.{0, 0, 0, 0}
      collapse ((2 : ℕ) • AddMonoidHom.id (ZMod 4)))

end SimplicialObjectsTest.TensorMaps
