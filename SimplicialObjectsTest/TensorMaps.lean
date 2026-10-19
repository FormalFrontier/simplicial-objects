/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects.TensorMaps
import SimplicialObjects.TensorCoefficientMaps
import SimplicialObjects.TensorHomotopies
import SimplicialObjectsTest.Normalization
import Mathlib.Data.ZMod.Basic
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Products

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

universe a w p u v

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
/-! ## The point-to-interval cylinder homotopy

The point above is `Δ[0]`. The second projection of its cylinder joins the
initial and terminal vertex maps. The chosen chain homotopy sends the existing
point generator to the negative of the existing edge tensor, whereas the
independent boundary above is terminal minus initial.
-/

open MonoidalCategory

private def vertexMap (i : Fin 2) : point ⟶ interval := SSet.const (vertex i)

private theorem vertexMap_pointVertex (i : Fin 2) :
    (vertexMap i).app _ pointVertex = vertex i := by
  apply SSet.stdSimplex.ext
  intro j
  rfl

/-- The second projection is a cylinder homotopy between the distinct vertex maps. -/
private noncomputable def vertexHomotopy : SSet.Homotopy (vertexMap 0) (vertexMap 1) where
  h := CartesianMonoidalCategory.snd point interval
  h₀ := SSet.ι₀_snd point
  h₁ := SSet.ι₁_snd point
  rel := by
    ext n x
    let y : {s : point.obj n // s ∈ (⊥ : point.Subcomplex).obj n} :=
      (CartesianMonoidalCategory.fst
        ((⊥ : point.Subcomplex) : SSet) interval).app n x
    have hy : y.val ∈ (⊥ : point.Subcomplex).obj n := y.property
    simp only [Subfunctor.bot_obj, Set.mem_empty_iff_false] at hy

private theorem vertex_chain_image (i : Fin 2) :
    (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4) (vertexMap i)).f 0
      pointTensorVertex = tensorVertex i := by
  have h := congrArg
    (fun k : SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) point 0 ⟶
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0 ↦
      k.hom pointTensorVertex)
    (SSet.tensorNormalizedChainComplexMap_f.{0, 0, 0} (ZMod 4) (vertexMap i) 0)
  have hx : SSet.tensorNormalizedChainComplexXMap.{0, 0, 0}
      (ZMod 4) (vertexMap i) 0 pointTensorVertex = tensorVertex i := by
    rw [pointTensorVertex, SSet.tensorNormalizedChainComplexXMap_single]
    change ULift.up (interval.normalizedIntegralSimplex
      ((vertexMap i).app _ pointVertex) ⊗ₜ[ℤ] (1 : ZMod 4)) = _
    rw [vertexMap_pointVertex,
      interval.normalizedIntegralSimplex_of_mem_nonDegenerate _ (vertex_nondegenerate i)]
    rfl
  exact h.trans hx

/-- The endpoint chain maps differ, as detected by the existing terminal coordinate. -/
private theorem vertex_chain_images_ne :
    (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4) (vertexMap 1)).f 0
        pointTensorVertex ≠
      (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4) (vertexMap 0)).f 0
        pointTensorVertex := by
  rw [vertex_chain_image, vertex_chain_image]
  intro h
  have hc := congrArg
    (fun z : SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0 ↦
      ((SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0}
        (ZMod 4) interval 0).hom z (intervalVertex 1)).down) h
  have ht (i : Fin 2) :
      (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0}
        (ZMod 4) interval 0).hom (tensorVertex i) =
          Finsupp.single (intervalVertex i) (ULift.up (1 : ZMod 4)) :=
    SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_single.{0, 0, 0}
      (ZMod 4) interval 0 (intervalVertex i) (1 : ZMod 4)
  have hzero : (1 : ZMod 4) = 0 := by
    rw [ht, ht] at hc
    simpa [terminal_ne_initial] using hc
  exact (by decide : (1 : ZMod 4) ≠ 0) hzero

/-- The degree-zero combinatorial prism of the projection is the interval edge. -/
private theorem vertexHomotopy_h_zero :
    vertexHomotopy.toSimplicialObjectHomotopy.h (0 : Fin 1) pointVertex = edge := by
  change
    (SSet.yonedaEquiv.symm pointVertex ▷ Δ[1] ≫
      CartesianMonoidalCategory.snd point interval).app _
        (SSet.prodStdSimplex₁.nonDegenerateEquiv (0 : Fin 1)).val = edge
  rw [CartesianMonoidalCategory.whiskerRight_snd]
  have hs : (CartesianMonoidalCategory.snd (Δ[0] : SSet.{0}) Δ[1]).app (op ⦋1⦌)
      (SSet.prodStdSimplex₁.nonDegenerateEquiv (0 : Fin 1)).val =
        SSet.stdSimplex.objMk₁ (0 : Fin 1).succ.castSucc :=
    SSet.prodStdSimplex₁.nonDegenerateEquiv_snd (0 : Fin 1)
  refine hs.trans ?_
  have h₀ := congrArg (fun s : interval _⦋0⦌ ↦ s 0) edge_face_one
  have h₁ := congrArg (fun s : interval _⦋0⦌ ↦ s 0) edge_face_zero
  change edge 0 = (0 : Fin 2) at h₀
  change edge 1 = (1 : Fin 2) at h₁
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i
  · exact h₀.symm
  · exact h₁.symm

/-- The negative sign is supplied by Mathlib's negative alternating sum, not by
an assumption about the tensor homotopy or a homology equality. -/
private theorem vertexHomotopy_chain_component :
    point.ιChainComplex (R := coefficients) pointVertex ≫
        (vertexHomotopy.toSimplicialObjectHomotopy.sSetChainComplexMap coefficients).hom 0 1 =
      -interval.ιChainComplex (R := coefficients) edge := by
  change point.ιChainComplex (R := coefficients) pointVertex ≫
    CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
      (vertexHomotopy.toSimplicialObjectHomotopy.whiskerRight
        (Limits.sigmaConst.obj coefficients)) 0 1 = _
  rw [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
    Fintype.sum_subsingleton _ (0 : Fin 1)]
  simp only [Fin.val_zero, pow_zero, one_smul,
    CategoryTheory.SimplicialObject.Homotopy.whiskerRight_h, Preadditive.comp_neg]
  simp only [SSet.ιChainComplex, Limits.sigmaConst_obj_map, Limits.Sigma.ι_comp_map',
    Category.id_comp, vertexHomotopy_h_zero]

/-- The chosen tensor homotopy, evaluated through its component API, takes the
point generator to minus the edge tensor. -/
private theorem vertexHomotopy_tensor_component :
    (vertexHomotopy.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4)).hom 0 1
      pointTensorVertex = -tensorEdge := by
  have hj : point.ιNormalizedChainComplex (R := coefficients) pointVertex ≫
      (point.fromNormalizedChainComplex coefficients).f 0 =
        point.ιChainComplex (R := coefficients) pointVertex := by
    rw [SSet.ιNormalizedChainComplex_fromNormalizedChainComplex_f,
      AlgebraicTopology.DoldKan.PInfty_f_0]
    exact Category.comp_id (point.ιChainComplex (R := coefficients) pointVertex)
  have hc : point.ιNormalizedChainComplex (R := coefficients) pointVertex ≫
      (point.fromNormalizedChainComplex coefficients).f 0 ≫
        (vertexHomotopy.toSimplicialObjectHomotopy.sSetChainComplexMap coefficients).hom 0 1 ≫
          (interval.toNormalizedChainComplex coefficients).f 1 ≫
            (SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 4) interval).inv.f 1 =
      -(interval.ιNormalizedChainComplex (R := coefficients) edge ≫
        (SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 4) interval).inv.f 1) := by
    simp only [← Category.assoc, hj, vertexHomotopy_chain_component, Preadditive.neg_comp,
      SSet.ιChainComplex_toNormalizedChainComplex_f]
  have he : (SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 4) point).hom.f 0
      pointTensorVertex =
        point.ιNormalizedChainComplex (R := coefficients) pointVertex
          (ULift.up (1 : ZMod 4)) := by
    have hf := congrArg
      (fun k : SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) point 0 ⟶
          (point.normalizedChainComplex coefficients).X 0 ↦ k.hom pointTensorVertex)
      (SSet.tensorNormalizedChainIso_hom_f.{0, 0, 0} (ZMod 4) point 0)
    exact hf.trans (SSet.tensorNormalizedChainComplexXIso_hom_single.{0, 0, 0}
      (ZMod 4) point 0 pointBasis (1 : ZMod 4))
  rw [SSet.Homotopy.tensorNormalizedChainComplexMap_eq,
    CategoryTheory.SimplicialObject.Homotopy.tensorNormalizedChainComplexMap_hom]
  change (SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 4) interval).inv.f 1
    ((interval.toNormalizedChainComplex coefficients).f 1
      ((vertexHomotopy.toSimplicialObjectHomotopy.sSetChainComplexMap coefficients).hom 0 1
        ((point.fromNormalizedChainComplex coefficients).f 0
          ((SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 4) point).hom.f 0
            pointTensorVertex)))) = _
  rw [he]
  have h := congrArg
    (fun k : coefficients ⟶ SSet.tensorNormalizedChainComplexX.{0, 0, 0}
        (ZMod 4) interval 1 ↦ k.hom (ULift.up (1 : ZMod 4))) hc
  change (SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 4) interval).inv.f 1
    ((interval.toNormalizedChainComplex coefficients).f 1
      ((vertexHomotopy.toSimplicialObjectHomotopy.sSetChainComplexMap coefficients).hom 0 1
        ((point.fromNormalizedChainComplex coefficients).f 0
          (point.ιNormalizedChainComplex (R := coefficients) pointVertex
            (ULift.up (1 : ZMod 4)))))) =
      -((SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 4) interval).inv.f 1
        (interval.ιNormalizedChainComplex (R := coefficients) edge
          (ULift.up (1 : ZMod 4)))) at h
  rw [h]
  have hi := SSet.tensorNormalizedChainIso_inv_f_ι.{0, 0, 0}
    (ZMod 4) interval 1 intervalEdge (1 : ZMod 4)
  rw [tensorEdge,
    interval.normalizedIntegralSimplex_of_mem_nonDegenerate edge edge_nondegenerate]
  exact congrArg Neg.neg hi

/-- The evaluated component is nonzero, independently detected by the signed boundary. -/
private theorem vertexHomotopy_tensor_component_ne_zero :
    (vertexHomotopy.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4)).hom 0 1
      pointTensorVertex ≠ 0 := by
  intro hz
  have hneg : -tensorEdge = 0 := vertexHomotopy_tensor_component.symm.trans hz
  exact (neg_ne_zero.mpr tensor_edge_ne_zero) hneg

/-- The combinatorial homotopy equates the induced homology maps on the same
nonidentity cylinder, whose nonzero component is computed independently. -/
private theorem vertexHomotopy_combinatorial_homology (n : ℕ) :
    HomologicalComplex.homologyMap
        (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4) (vertexMap 0)) n =
      HomologicalComplex.homologyMap
        (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4) (vertexMap 1)) n :=
  vertexHomotopy.toSimplicialObjectHomotopy.congr_tensorNormalizedHomologyMap.{0, 0, 0}
    (ZMod 4) n

/-- The cylinder homotopy equates the induced homology maps even though the
original endpoint chain maps have distinct images. -/
private theorem vertexHomotopy_cylinder_homology (n : ℕ) :
    HomologicalComplex.homologyMap
        (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4) (vertexMap 0)) n =
      HomologicalComplex.homologyMap
        (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4) (vertexMap 1)) n :=
  vertexHomotopy.congr_tensorNormalizedHomologyMap.{0, 0, 0} (ZMod 4) n

/-! ## The standard interval augmentation and its source homotopies

This augmentation has constant target on its chosen terminal Type, not `Δ[0]`.
The extra degeneracy supplies the section and the source homotopy; the strict
section identity supplies the target homotopy. The degree-zero tensor
map identifies the same two distinct vertex tensors, with nonzero common image.
-/

private noncomputable abbrev intervalAugmentation : SSet.Augmented.{0} :=
  SSet.Augmented.stdSimplex.obj ⦋1⦌

private noncomputable abbrev intervalExtraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy intervalAugmentation :=
  SSet.Augmented.StandardSimplex.extraDegeneracy ⦋1⦌

private noncomputable abbrev augmentationTarget : SSet.{0} :=
  (SimplicialObject.const (Type 0)).obj intervalAugmentation.right

private noncomputable abbrev augmentation : interval ⟶ augmentationTarget :=
  intervalAugmentation.hom

private noncomputable abbrev augmentationSection : augmentationTarget ⟶ interval :=
  intervalExtraDegeneracy.section_

private noncomputable def augmentationHomotopy :
    SimplicialObject.Homotopy (augmentation ≫ augmentationSection) (𝟙 interval) :=
  intervalExtraDegeneracy.homotopy

private noncomputable def augmentationSectionHomotopy :
    SimplicialObject.Homotopy (augmentationSection ≫ augmentation) (𝟙 augmentationTarget) :=
  Eq.mp
    (congrArg (fun k : augmentationTarget ⟶ augmentationTarget ↦
      SimplicialObject.Homotopy k (𝟙 augmentationTarget))
      intervalExtraDegeneracy.section_comp_hom.symm)
    (SimplicialObject.Homotopy.refl (𝟙 augmentationTarget))

private noncomputable def augmentationTargetVertex : augmentationTarget _⦋0⦌ :=
  augmentation.app (op ⦋0⦌) (vertex 0)

private noncomputable def augmentationTargetBasis : augmentationTarget.nonDegenerate 0 :=
  ⟨augmentationTargetVertex, by simp [SSet.nondegenerate_zero]⟩

private theorem augmentation_vertex (i : Fin 2) :
    augmentation.app (op ⦋0⦌) (vertex i) = augmentationTargetVertex := by
  let : Unique (augmentationTarget _⦋0⦌) :=
    Limits.Types.isTerminalEquivUnique _ Limits.terminalIsTerminal
  apply Subsingleton.elim

private noncomputable def augmentationTargetTensor :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) augmentationTarget 0 :=
  ULift.up (Finsupp.single augmentationTargetBasis 1 ⊗ₜ[ℤ] (1 : ZMod 4))

/-- The coefficient-one common image is nonzero in the exact constant target. -/
private theorem augmentation_target_tensor_ne_zero : augmentationTargetTensor ≠ 0 := by
  intro h
  have hc := SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_single.{0, 0, 0}
    (ZMod 4) augmentationTarget 0 augmentationTargetBasis (1 : ZMod 4)
  change (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0}
    (ZMod 4) augmentationTarget 0).hom augmentationTargetTensor = _ at hc
  rw [h, map_zero] at hc
  have hzero : (0 : ZMod 4) = 1 := by
    simpa using congrArg
      (fun z : augmentationTarget.nonDegenerate 0 →₀ ULift.{0} (ZMod 4) ↦
        (z augmentationTargetBasis).down) hc
  exact (by decide : (0 : ZMod 4) ≠ 1) hzero

/-- The degree map sends either interval vertex tensor to this generator. -/
private theorem augmentation_tensor_vertex (i : Fin 2) :
    SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} (ZMod 4) augmentation 0
        (tensorVertex i) = augmentationTargetTensor := by
  rw [tensorVertex, SSet.tensorNormalizedChainComplexXMap_single]
  change ULift.up (augmentationTarget.normalizedIntegralSimplex
    (augmentation.app (op ⦋0⦌) (vertex i)) ⊗ₜ[ℤ] (1 : ZMod 4)) = _
  rw [augmentation_vertex,
    augmentationTarget.normalizedIntegralSimplex_of_mem_nonDegenerate
      augmentationTargetVertex augmentationTargetBasis.property]
  rfl

/-- The chain map has the same common image in degree zero. -/
private theorem augmentation_chain_vertex (i : Fin 2) :
    (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4) augmentation).f 0
      (tensorVertex i) = augmentationTargetTensor := by
  have h := congrArg
    (fun k : SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0 ⟶
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) augmentationTarget 0 ↦
      k.hom (tensorVertex i))
    (SSet.tensorNormalizedChainComplexMap_f.{0, 0, 0} (ZMod 4) augmentation 0)
  exact h.trans (augmentation_tensor_vertex i)

/-- Simplicial homotopy-inverse data need not yield degreewise monomorphisms of tensor chains. -/
private theorem augmentation_not_mono_zero :
    ¬ Mono ((SSet.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4) augmentation).f 0) := by
  intro hm
  have hinj := (ModuleCat.mono_iff_injective _).mp hm
  apply vertex_chain_images_ne
  rw [vertex_chain_image, vertex_chain_image]
  exact hinj ((augmentation_chain_vertex 1).trans (augmentation_chain_vertex 0).symm)

/-- The standard interval augmentation is a quasi-isomorphism on normalized
chains with lifted coefficients modulo four. -/
private theorem augmentation_normalized_quasiIso :
    QuasiIso (SSet.normalizedChainComplexMap augmentation coefficients) :=
  SSet.quasiIso_normalizedChainComplexMap_of_homotopy_inverse
    augmentation augmentationSection augmentationHomotopy augmentationSectionHomotopy coefficients

/-- The same augmentation is a quasi-isomorphism of the original tensor
complexes with coefficients modulo four. -/
private theorem augmentation_tensor_quasiIso :
    QuasiIso (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} (ZMod 4) augmentation) :=
  SSet.quasiIso_tensorNormalizedChainComplexMap_of_homotopy_inverse.{0, 0, 0}
    (ZMod 4) augmentation augmentationSection augmentationHomotopy augmentationSectionHomotopy

/-- The stock extra degeneracy supplies the normalized augmentation theorem
for every standard simplex, with arbitrary categorical coefficients. -/
private theorem standardSimplex_augmentation_normalized_quasiIso
    {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasCoproducts.{w} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    QuasiIso (SSet.normalizedChainComplexMap
      (SSet.Augmented.stdSimplex.{w}.obj ⦋n⦌).hom R) :=
  SSet.quasiIso_normalizedChainComplexMap_of_extraDegeneracy
    (SSet.Augmented.stdSimplex.{w}.obj ⦋n⦌)
    (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋n⦌) R

/-- The same stock augmentation works for arbitrary abelian coefficients and
independent coefficient, simplex and padding universes. -/
private theorem standardSimplex_augmentation_tensor_quasiIso
    (A : Type a) [AddCommGroup A] (n : ℕ) :
    QuasiIso (SSet.tensorNormalizedChainComplexMap.{a, w, p} A
      (SSet.Augmented.stdSimplex.{w}.obj ⦋n⦌).hom) :=
  SSet.quasiIso_tensorNormalizedChainComplexMap_of_extraDegeneracy.{a, w, p} A
    (SSet.Augmented.stdSimplex.{w}.obj ⦋n⦌)
    (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋n⦌)

end SimplicialObjectsTest.TensorMaps
