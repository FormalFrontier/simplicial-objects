/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects.TensorCoefficients
import SimplicialObjectsTest.Normalization
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.Data.ZMod.Basic

/-!
# Tensor coefficients on the interval and its two-sheet cover

The integral edge has boundary terminal vertex minus initial vertex. After tensoring
with `ZMod 4`, this boundary is still nonzero. The normalized-degree coordinates
also compute the pushforward of the two-sheet transfer as coefficient two.
Degenerate simplices, outgoing degree-zero maps and an empty sheet set give zero.
-/

open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial TensorProduct
open SimplicialObjectsTest.Normalization

namespace SimplicialObjectsTest.TensorCoefficients

private def intervalVertex (i : Fin 2) : interval.nonDegenerate 0 :=
  ⟨vertex i, vertex_nondegenerate i⟩

private def intervalEdge : interval.nonDegenerate 1 := ⟨edge, edge_nondegenerate⟩

private noncomputable def integralEdge : interval.nonDegenerate 1 →₀ ℤ :=
  interval.normalizedIntegralSimplex edge

/-- The independent integral boundary has the terminal-minus-initial convention. -/
private theorem integralEdge_boundary :
    interval.normalizedIntegralBoundary 0 integralEdge =
      interval.normalizedIntegralSimplex (vertex 1) -
        interval.normalizedIntegralSimplex (vertex 0) := by
  rw [integralEdge,
    interval.normalizedIntegralSimplex_of_mem_nonDegenerate edge edge_nondegenerate,
    SSet.normalizedIntegralBoundary_single, Fin.sum_univ_two]
  simp [edge_face_zero, edge_face_one, sub_eq_add_neg]

/-- The elementary degenerate edge has zero integral class. -/
private theorem degenerate_edge_class :
    interval.normalizedIntegralSimplex (interval.σ (0 : Fin 1) (vertex 0)) = 0 :=
  interval.normalizedIntegralSimplex_of_mem_degenerate _
    (interval.σ_mem_degenerate (0 : Fin 1) (vertex 0))

private noncomputable def tensorEdge :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 1 :=
  ULift.up (integralEdge ⊗ₜ[ℤ] (1 : ZMod 4))

private noncomputable def tensorEdgeBoundary :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0 :=
  SSet.tensorNormalizedBoundary (ZMod 4) interval 0 tensorEdge

/-- The tensor boundary, computed using its independent alternating definition. -/
private theorem tensorEdgeBoundary_coordinates :
    (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0} (ZMod 4) interval 0).hom
        tensorEdgeBoundary =
      Finsupp.single (intervalVertex 1) (ULift.up (1 : ZMod 4)) -
        Finsupp.single (intervalVertex 0) (ULift.up (1 : ZMod 4)) := by
  have hb : tensorEdgeBoundary =
      (ULift.up (Finsupp.single (intervalVertex 1) 1 ⊗ₜ[ℤ] (1 : ZMod 4)) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0) -
      (ULift.up (Finsupp.single (intervalVertex 0) 1 ⊗ₜ[ℤ] (1 : ZMod 4)) :
        SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0) := by
    rw [tensorEdgeBoundary, tensorEdge, SSet.tensorNormalizedBoundary_tmul,
      integralEdge_boundary,
      interval.normalizedIntegralSimplex_of_mem_nonDegenerate (vertex 1)
        (vertex_nondegenerate 1),
      interval.normalizedIntegralSimplex_of_mem_nonDegenerate (vertex 0)
        (vertex_nondegenerate 0), TensorProduct.sub_tmul]
    rfl
  exact (congrArg
    (fun z : SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0 ↦
      (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0} (ZMod 4) interval 0).hom.hom z)
    hb).trans
      ((map_sub
        (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0}
          (ZMod 4) interval 0).hom.hom _ _).trans
        (congrArg₂
          (fun z w : interval.nonDegenerate 0 →₀ ULift.{0} (ZMod 4) ↦ z - w)
          (SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_single.{0, 0, 0}
            (ZMod 4) interval 0 (intervalVertex 1) (1 : ZMod 4))
          (SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_single.{0, 0, 0}
            (ZMod 4) interval 0 (intervalVertex 0) (1 : ZMod 4))))

private theorem terminal_ne_initial : intervalVertex 1 ≠ intervalVertex 0 := by
  intro h
  have hv := congrArg
    (fun s : interval.nonDegenerate 0 ↦ SSet.stdSimplex.obj₀Equiv s.val) h
  have hfin : (1 : Fin 2) = 0 :=
    ((SSet.stdSimplex.obj₀Equiv.{0} (n := 1)).apply_symm_apply 1).symm.trans
      (hv.trans ((SSet.stdSimplex.obj₀Equiv.{0} (n := 1)).apply_symm_apply 0))
  exact (by decide : (1 : Fin 2) ≠ 0) hfin

/-- Torsion coefficients do not turn the interval boundary into the zero map. -/
private theorem tensorEdgeBoundary_ne_zero : tensorEdgeBoundary ≠ 0 := by
  intro h
  have hc := congrArg
    (fun z : interval.nonDegenerate 0 →₀ ULift.{0} (ZMod 4) ↦
      (z (intervalVertex 1)).down) tensorEdgeBoundary_coordinates
  rw [h, map_zero] at hc
  have hzero : (0 : ZMod 4) = 1 := by
    simpa [Finsupp.single_apply, terminal_ne_initial, Ne.symm terminal_ne_initial] using hc
  exact (by decide : (0 : ZMod 4) ≠ 1) hzero

private abbrev coefficients : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ULift.{0} (ZMod 4))

/-- The whole normalized cofan/direct-sum isomorphism computes the edge coordinate. -/
private theorem normalized_edge_coordinates :
    (interval.normalizedChainComplexXIsoFinsupp coefficients 1).hom
        (interval.ιNormalizedChainComplex (R := coefficients) edge (ULift.up (1 : ZMod 4))) =
      Finsupp.single intervalEdge (ULift.up (1 : ZMod 4)) :=
  interval.normalizedChainComplexXIsoFinsupp_hom_ι coefficients 1 intervalEdge _

/-- The degree comparison lands in normalized chains, not only in their coordinates. -/
private theorem degree_comparison_edge :
    (SSet.tensorNormalizedChainComplexXIso.{0, 0, 0} (ZMod 4) interval 1).hom tensorEdge =
      interval.ιNormalizedChainComplex (R := coefficients) edge (ULift.up (1 : ZMod 4)) :=
  SSet.tensorNormalizedChainComplexXIso_hom_simplex (ZMod 4) interval edge 1

/-- The inverse comparison recovers the integral generator tensored with its coefficient. -/
private theorem degree_comparison_inverse_edge :
    (SSet.tensorNormalizedChainComplexXIso.{0, 0, 0} (ZMod 4) interval 1).inv
        (interval.ιNormalizedChainComplex (R := coefficients) edge
          (ULift.up (1 : ZMod 4))) = tensorEdge := by
  rw [← degree_comparison_edge]
  exact ModuleCat.inv_hom_apply _ _

/-- The primitive differential has no outgoing degree-zero component. -/
private theorem degree_zero_differential :
    SSet.tensorNormalizedDifferential.{0, 0, 0} (ZMod 4) interval 0 0 = 0 :=
  SSet.tensorNormalizedDifferential_zero (ZMod 4) interval 0

private noncomputable def coverTransfer :
    interval.chainComplex coefficients ⟶ twoSheetInterval.chainComplex coefficients :=
  SSet.chainComplexTransfer twoSheetIntervalMap twoSheetIntervalMap_equifibered
    twoSheetIntervalMap_finite coefficients

private noncomputable def pushedTransferVertex :
    (interval.normalizedChainComplex coefficients).X 0 :=
  (interval.ιChainComplex (vertex 0) ≫
    (coverTransfer ≫ SSet.chainComplexMap twoSheetIntervalMap coefficients).f 0 ≫
      (interval.toNormalizedChainComplex coefficients).f 0) (ULift.up (1 : ZMod 4))

/-- Pushing the two-sheet transfer has coefficient two in the new normalized coordinates. -/
private theorem pushedTransferVertex_coordinates :
    (interval.normalizedChainComplexXIsoFinsupp coefficients 0).hom pushedTransferVertex =
      Finsupp.single (intervalVertex 0) (ULift.up (2 : ZMod 4)) := by
  have hcard (x : interval _⦋0⦌) :
      Nat.card {y : twoSheetInterval _⦋0⦌ // twoSheetIntervalMap.app _ y = x} = 2 :=
    (Nat.card_congr (twoSheetIntervalFiberEquiv x)).trans (Nat.card_fin 2)
  have hs := SSet.chainComplexTransfer_comp_map twoSheetIntervalMap
    twoSheetIntervalMap_equifibered twoSheetIntervalMap_finite coefficients 2 hcard
  have hp : interval.ιChainComplex (vertex 0) ≫
      (coverTransfer ≫ SSet.chainComplexMap twoSheetIntervalMap coefficients).f 0 ≫
        (interval.toNormalizedChainComplex coefficients).f 0 =
      (2 : ℕ) • interval.ιNormalizedChainComplex (R := coefficients) (vertex 0) := by
    rw [coverTransfer, hs, HomologicalComplex.nsmul_f_apply, HomologicalComplex.id_f]
    simp only [Preadditive.comp_nsmul, Category.id_comp, Preadditive.nsmul_comp,
      SSet.ιChainComplex_toNormalizedChainComplex_f]
  have hv : pushedTransferVertex =
      (2 : ℕ) • (interval.ιNormalizedChainComplex (R := coefficients) (vertex 0)).hom
        (ULift.up (1 : ZMod 4) : coefficients) :=
    congrArg (fun f : coefficients ⟶ (interval.normalizedChainComplex coefficients).X 0 ↦
      f.hom (ULift.up (1 : ZMod 4) : coefficients)) hp
  have htwo : (2 : ℕ) • (ULift.up (1 : ZMod 4) : coefficients) = ULift.up (2 : ZMod 4) := by
    decide
  calc
    _ = (interval.normalizedChainComplexXIsoFinsupp coefficients 0).hom
        ((interval.ιNormalizedChainComplex (R := coefficients) (vertex 0)).hom
          (ULift.up (2 : ZMod 4) : coefficients)) := by
      rw [hv, ← map_nsmul
        (interval.ιNormalizedChainComplex (R := coefficients) (vertex 0)).hom
        2 (ULift.up (1 : ZMod 4) : coefficients), htwo]
    _ = _ := interval.normalizedChainComplexXIsoFinsupp_hom_ι coefficients 0 (intervalVertex 0) _

private noncomputable def transferredTensorVertex :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0 :=
  (SSet.tensorNormalizedChainComplexXIsoFinsupp (ZMod 4) interval 0).inv
    ((interval.normalizedChainComplexXIsoFinsupp coefficients 0).hom pushedTransferVertex)

/-- The same transfer calculation recovers coefficient two in the independent tensor degree. -/
private theorem transferredTensorVertex_eq :
    transferredTensorVertex =
      ULift.up (Finsupp.single (intervalVertex 0) 1 ⊗ₜ[ℤ] (2 : ZMod 4)) := by
  rw [transferredTensorVertex, pushedTransferVertex_coordinates,
    SSet.tensorNormalizedChainComplexXIsoFinsupp_inv_single]

/-- Coefficient two is nonzero modulo four, so the two-sheet calculation is nontrivial. -/
private theorem transferredTensorVertex_ne_zero : transferredTensorVertex ≠ 0 := by
  intro h
  have hc := congrArg
    (fun z : SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 4) interval 0 ↦
      (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0} (ZMod 4) interval 0).hom.hom z)
    transferredTensorVertex_eq
  rw [h, map_zero,
    SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_single.{0, 0, 0}
      (ZMod 4) interval 0 (intervalVertex 0) (2 : ZMod 4)] at hc
  have hzero : (0 : ZMod 4) = 2 := by
    simpa using congrArg
      (fun z : interval.nonDegenerate 0 →₀ ULift.{0} (ZMod 4) ↦
        (z (intervalVertex 0)).down) hc
  exact (by decide : (0 : ZMod 4) ≠ 2) hzero

private abbrev emptySheetInterval : SSet.{0} :=
  ((Functor.const _).obj Empty : SSet.{0}) ⊗ interval

/-- Empty sheets give zero integral boundary in every successor degree. -/
private theorem empty_boundary (n : ℕ) (z : emptySheetInterval.nonDegenerate (n + 1) →₀ ℤ) :
    emptySheetInterval.normalizedIntegralBoundary n z = 0 := by
  ext s
  exact Empty.elim s.val.1

/-- The tensor boundary on the empty sheet model is zero as well. -/
private theorem empty_tensor_boundary (n : ℕ)
    (z : emptySheetInterval.nonDegenerate (n + 1) →₀ ℤ) (x : ZMod 4) :
    SSet.tensorNormalizedBoundary.{0, 0, 0} (ZMod 4) emptySheetInterval n
        (ULift.up (z ⊗ₜ[ℤ] x)) = 0 := by
  rw [SSet.tensorNormalizedBoundary_tmul, empty_boundary, TensorProduct.zero_tmul]
  rfl

private noncomputable abbrev intervalTensorComplex :=
  SSet.tensorNormalizedChainComplex.{0, 0, 0} (ZMod 4) interval

private noncomputable def intervalTensorComparison :
    intervalTensorComplex ≅ interval.normalizedChainComplex coefficients :=
  SSet.tensorNormalizedChainIso.{0, 0, 0} (ZMod 4) interval

/-- The specified successor differential is retained by the assembled complex. -/
private theorem complex_edge_boundary :
    intervalTensorComplex.d 1 0 tensorEdge = tensorEdgeBoundary :=
  (congrArg (fun f ↦ f tensorEdge)
    (SSet.tensorNormalizedDifferential_succ.{0, 0, 0} (ZMod 4) interval 0))

/-- The assembled complex has a nonzero edge boundary with coefficients modulo four. -/
private theorem complex_edge_boundary_ne_zero : intervalTensorComplex.d 1 0 tensorEdge ≠ 0 := by
  rw [complex_edge_boundary]
  exact tensorEdgeBoundary_ne_zero

/-- The whole chain isomorphism specializes to the same normalized interval edge. -/
private theorem chain_comparison_edge :
    intervalTensorComparison.hom.f 1 tensorEdge =
      interval.ιNormalizedChainComplex (R := coefficients) edge (ULift.up (1 : ZMod 4)) :=
  SSet.tensorNormalizedChainIso_hom_f_apply (ZMod 4) interval edge 1

/-- The image of the edge under the chain comparison has nonzero normalized coordinate. -/
private theorem chain_comparison_edge_ne_zero :
    intervalTensorComparison.hom.f 1 tensorEdge ≠ 0 := by
  intro h
  have hc := normalized_edge_coordinates
  rw [← chain_comparison_edge, h, map_zero] at hc
  have hzero : (0 : ZMod 4) = 1 := by
    simpa using congrArg
      (fun z : interval.nonDegenerate 1 →₀ ULift.{0} (ZMod 4) ↦ (z intervalEdge).down) hc
  exact (by decide : (0 : ZMod 4) ≠ 1) hzero

end SimplicialObjectsTest.TensorCoefficients
