/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorMaps
public import SimplicialObjectsTest.Normalization
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Data.ZMod.Basic

/-!
# An integral edge in a proper standard-simplex face

The face `δ₀ : Δ[1] ⟶ Δ[2]` is monic by the component criterion and cancellation
in the simplex category. Its normalized integral tensor map takes the edge `[0,1]`
to `[1,2]`. The coordinate of each tensor at its edge is one, so neither tensor
is zero. The independent alternating boundaries are terminal minus initial;
the degree-zero map sends one signed boundary to the other.

The empty subcomplex and zero coefficients give zero-group boundary cases.
The integral collapse to `Δ[0]` is not monic and kills the same nonzero source
edge. These computations use Mathlib's standard simplices and the existing raw
tensor, generator and Finsupp-coordinate operations, not general
tensor-map monicity or injectivity statements.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial TensorProduct
open SimplicialObjectsTest.Normalization

namespace SimplicialObjectsTest.TensorMonomorphisms

universe a p

/-- The standard two-simplex. -/
abbrev triangle : SSet.{0} := Δ[2]

/-- The face omitting vertex zero. -/
def face : interval ⟶ triangle :=
  SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3))

/-- Cancellation by the injective ordinal face proves monicity componentwise. -/
instance face_mono : Mono face := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  intro x y h
  apply SSet.stdSimplex.objEquiv.injective
  apply (cancel_mono (SimplexCategory.δ (0 : Fin 3))).mp
  exact congrArg SSet.stdSimplex.objEquiv h

/-- A vertex of the standard two-simplex. -/
def triangleVertex (i : Fin 3) : triangle _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm i

/-- Every vertex is nondegenerate. -/
theorem triangleVertex_nondegenerate (i : Fin 3) :
    triangleVertex i ∈ triangle.nonDegenerate 0 := by
  simp [SSet.nondegenerate_zero]

/-- The face sends the interval vertices to vertices one and two. -/
theorem face_vertex (i : Fin 2) :
    face.app (op ⦋0⦌) (vertex i) = triangleVertex i.succ := by
  apply SSet.stdSimplex.ext
  intro j
  fin_cases i <;> fin_cases j <;> rfl

/-- Vertex zero is outside the face, so the monomorphism is proper. -/
theorem face_omits_initial_vertex (x : interval _⦋0⦌) :
    face.app (op ⦋0⦌) x ≠ triangleVertex 0 := by
  obtain ⟨i, rfl⟩ := SSet.stdSimplex.obj₀Equiv.symm.surjective x
  fin_cases i <;> decide

/-- The edge `[1,2]`, specified by the ordinal face. -/
def edge12 : triangle _⦋1⦌ :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (0 : Fin 3))

/-- The face takes the normalized top interval edge to `[1,2]`. -/
theorem face_edge : face.app (op ⦋1⦌) edge = edge12 := by
  have h₀ := congrArg (fun s : interval _⦋0⦌ ↦ s 0) edge_face_one
  have h₁ := congrArg (fun s : interval _⦋0⦌ ↦ s 0) edge_face_zero
  change edge 0 = (0 : Fin 2) at h₀
  change edge 1 = (1 : Fin 2) at h₁
  apply SSet.stdSimplex.ext
  intro i
  change (SimplexCategory.δ (0 : Fin 3)).toOrderHom (edge i) = edge12 i
  fin_cases i
  · change (SimplexCategory.δ (0 : Fin 3)).toOrderHom (edge (0 : Fin 2)) = edge12 0
    rw [h₀]
    rfl
  · change (SimplexCategory.δ (0 : Fin 3)).toOrderHom (edge (1 : Fin 2)) = edge12 1
    rw [h₁]
    rfl

/-- Nondegeneracy of the image follows from the stock monomorphism criterion. -/
theorem edge12_nondegenerate : edge12 ∈ triangle.nonDegenerate 1 := by
  rw [← face_edge]
  exact (SSet.nonDegenerate_iff_of_mono face edge).2 edge_nondegenerate

/-- The zeroth face of `[1,2]` is vertex two. -/
theorem edge12_face_zero : triangle.δ (0 : Fin 2) edge12 = triangleVertex 2 := by decide

/-- The first face of `[1,2]` is vertex one. -/
theorem edge12_face_one : triangle.δ (1 : Fin 2) edge12 = triangleVertex 1 := by decide

/-- The source edge as a nondegenerate basis index. -/
def sourceEdgeBasis : interval.nonDegenerate 1 := ⟨edge, edge_nondegenerate⟩

/-- The image edge as a nondegenerate basis index. -/
def targetEdgeBasis : triangle.nonDegenerate 1 := ⟨edge12, edge12_nondegenerate⟩

/-- An interval vertex as a nondegenerate basis index. -/
def sourceVertexBasis (i : Fin 2) : interval.nonDegenerate 0 :=
  ⟨vertex i, vertex_nondegenerate i⟩

/-- A triangle vertex as a nondegenerate basis index. -/
def targetVertexBasis (i : Fin 3) : triangle.nonDegenerate 0 :=
  ⟨triangleVertex i, triangleVertex_nondegenerate i⟩

/-- The normalized lifted integral tensor on the interval edge. -/
noncomputable def sourceTensorEdge :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 1 :=
  ULift.up (Finsupp.single sourceEdgeBasis 1 ⊗ₜ[ℤ] (1 : ℤ))

/-- The normalized lifted integral tensor on the image edge. -/
noncomputable def targetTensorEdge :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ triangle 1 :=
  ULift.up (Finsupp.single targetEdgeBasis 1 ⊗ₜ[ℤ] (1 : ℤ))

/-- The normalized integral tensor on a source vertex. -/
noncomputable def sourceTensorVertex (i : Fin 2) :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ interval 0 :=
  ULift.up (Finsupp.single (sourceVertexBasis i) 1 ⊗ₜ[ℤ] (1 : ℤ))

/-- The normalized integral tensor on a target vertex. -/
noncomputable def targetTensorVertex (i : Fin 3) :
    SSet.tensorNormalizedChainComplexX.{0, 0, 0} ℤ triangle 0 :=
  ULift.up (Finsupp.single (targetVertexBasis i) 1 ⊗ₜ[ℤ] (1 : ℤ))

/-- The coordinate of the source edge tensor at its edge is one. -/
theorem sourceTensorEdge_coordinate :
    ((SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0} ℤ interval 1).hom
      sourceTensorEdge sourceEdgeBasis).down = (1 : ℤ) := by
  rw [sourceTensorEdge, SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_single]
  simp

/-- The coordinate of the target edge tensor at its edge is one. -/
theorem targetTensorEdge_coordinate :
    ((SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0} ℤ triangle 1).hom
      targetTensorEdge targetEdgeBasis).down = (1 : ℤ) := by
  rw [targetTensorEdge, SSet.tensorNormalizedChainComplexXIsoFinsupp_hom_single]
  simp

/-- The normalized integral source edge tensor is nonzero. -/
theorem sourceTensorEdge_ne_zero : sourceTensorEdge ≠ 0 := by
  intro h
  have hc := sourceTensorEdge_coordinate
  rw [h, map_zero] at hc
  exact (zero_ne_one : (0 : ℤ) ≠ 1) hc

/-- The normalized integral target edge tensor is nonzero. -/
theorem targetTensorEdge_ne_zero : targetTensorEdge ≠ 0 := by
  intro h
  have hc := targetTensorEdge_coordinate
  rw [h, map_zero] at hc
  exact (zero_ne_one : (0 : ℤ) ≠ 1) hc

/-- The existing raw degree map takes the source tensor to the target tensor. -/
theorem face_tensor_edge :
    SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} ℤ face 1 sourceTensorEdge =
      targetTensorEdge := by
  rw [sourceTensorEdge, SSet.tensorNormalizedChainComplexXMap_single]
  change ULift.up (triangle.normalizedIntegralSimplex (face.app _ edge) ⊗ₜ[ℤ] (1 : ℤ)) = _
  rw [face_edge,
    triangle.normalizedIntegralSimplex_of_mem_nonDegenerate edge12 edge12_nondegenerate]
  rfl

/-- Nonzeroness of the mapped image is detected without an injectivity premise. -/
theorem face_tensor_edge_ne_zero :
    SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} ℤ face 1 sourceTensorEdge ≠ 0 := by
  rw [face_tensor_edge]
  exact targetTensorEdge_ne_zero

/-- The normalized whole chain map has the same edge image. -/
theorem face_chain_edge :
    (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} ℤ face).f 1 sourceTensorEdge =
      targetTensorEdge := by
  rw [SSet.tensorNormalizedChainComplexMap_f]
  exact face_tensor_edge

/-- The normalized integral boundary of the source generator has its signed endpoints. -/
theorem source_integral_boundary :
    interval.normalizedIntegralBoundary 0 (Finsupp.single sourceEdgeBasis 1) =
      Finsupp.single (sourceVertexBasis 1) 1 - Finsupp.single (sourceVertexBasis 0) 1 := by
  rw [SSet.normalizedIntegralBoundary_single, Fin.sum_univ_two]
  simp [sourceEdgeBasis, edge_face_zero, edge_face_one, sourceVertexBasis, sub_eq_add_neg]

/-- The normalized integral boundary of the image generator has its signed endpoints. -/
theorem target_integral_boundary :
    triangle.normalizedIntegralBoundary 0 (Finsupp.single targetEdgeBasis 1) =
      Finsupp.single (targetVertexBasis 2) 1 - Finsupp.single (targetVertexBasis 1) 1 := by
  rw [SSet.normalizedIntegralBoundary_single, Fin.sum_univ_two]
  simp [targetEdgeBasis, edge12_face_zero, edge12_face_one, targetVertexBasis, sub_eq_add_neg]

/-- The independent source tensor boundary is terminal vertex minus initial vertex. -/
theorem source_tensor_boundary :
    SSet.tensorNormalizedBoundary.{0, 0, 0} ℤ interval 0 sourceTensorEdge =
      sourceTensorVertex 1 - sourceTensorVertex 0 := by
  rw [sourceTensorEdge, SSet.tensorNormalizedBoundary_tmul, source_integral_boundary,
    TensorProduct.sub_tmul]
  rfl

/-- The independent target tensor boundary is vertex two minus vertex one. -/
theorem target_tensor_boundary :
    SSet.tensorNormalizedBoundary.{0, 0, 0} ℤ triangle 0 targetTensorEdge =
      targetTensorVertex 2 - targetTensorVertex 1 := by
  rw [targetTensorEdge, SSet.tensorNormalizedBoundary_tmul, target_integral_boundary,
    TensorProduct.sub_tmul]
  rfl

/-- The normalized raw degree-zero operation sends each source vertex to its face image. -/
theorem face_tensor_vertex (i : Fin 2) :
    SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} ℤ face 0 (sourceTensorVertex i) =
      targetTensorVertex i.succ := by
  rw [sourceTensorVertex, SSet.tensorNormalizedChainComplexXMap_single]
  change ULift.up (triangle.normalizedIntegralSimplex (face.app _ (vertex i)) ⊗ₜ[ℤ] (1 : ℤ)) = _
  rw [face_vertex,
    triangle.normalizedIntegralSimplex_of_mem_nonDegenerate _ (triangleVertex_nondegenerate _)]
  rfl

/-- Mapping the signed source boundary gives the signed image boundary. -/
theorem face_signed_boundary :
    SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} ℤ face 0
        (SSet.tensorNormalizedBoundary.{0, 0, 0} ℤ interval 0 sourceTensorEdge) =
      targetTensorVertex 2 - targetTensorVertex 1 := by
  rw [source_tensor_boundary, map_sub, face_tensor_vertex, face_tensor_vertex]
  rfl

/-- The boundary of the mapped edge agrees with the mapped boundary. -/
theorem face_tensor_boundary_commutes :
    SSet.tensorNormalizedBoundary.{0, 0, 0} ℤ triangle 0
        (SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} ℤ face 1 sourceTensorEdge) =
      SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} ℤ face 0
        (SSet.tensorNormalizedBoundary.{0, 0, 0} ℤ interval 0 sourceTensorEdge) := by
  rw [face_tensor_edge, target_tensor_boundary, face_signed_boundary]

/-! ## Empty source and zero coefficients -/

/-- The empty simplicial subcomplex of the triangle. -/
abbrev empty : SSet.{0} := (⊥ : triangle.Subcomplex)

/-- The empty subcomplex inclusion. -/
def emptyInclusion : empty ⟶ triangle := (⊥ : triangle.Subcomplex).ι

/-- Monicity here is the stock subcomplex-inclusion instance. -/
instance emptyInclusion_mono : Mono emptyInclusion := by
  dsimp [emptyInclusion]
  infer_instance

/-- Empty nondegenerate coordinates force every normalized tensor degree to vanish. -/
theorem empty_tensor_eq_zero (A : Type a) [AddCommGroup A] (n : ℕ)
    (z : SSet.tensorNormalizedChainComplexX.{a, 0, p} A empty n) : z = 0 := by
  have hz : (SSet.tensorNormalizedChainComplexXIsoFinsupp.{a, 0, p} A empty n).hom z = 0 := by
    ext s
    have hs := s.val.property
    simp only [Subfunctor.bot_obj, Set.mem_empty_iff_false] at hs
  calc
    z = (SSet.tensorNormalizedChainComplexXIsoFinsupp.{a, 0, p} A empty n).inv
        ((SSet.tensorNormalizedChainComplexXIsoFinsupp.{a, 0, p} A empty n).hom z) :=
      (ModuleCat.inv_hom_apply _ _).symm
    _ = 0 := by rw [hz, map_zero]

/-- With the zero group `ZMod 1`, all normalized tensor degrees vanish, for any source. -/
theorem zeroCoefficient_tensor_eq_zero (S : SSet.{0}) (n : ℕ)
    (z : SSet.tensorNormalizedChainComplexX.{0, 0, 0} (ZMod 1) S n) : z = 0 := by
  have hz : (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0} (ZMod 1) S n).hom z = 0 :=
    Subsingleton.elim _ _
  calc
    z = (SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0} (ZMod 1) S n).inv
        ((SSet.tensorNormalizedChainComplexXIsoFinsupp.{0, 0, 0} (ZMod 1) S n).hom z) :=
      (ModuleCat.inv_hom_apply _ _).symm
    _ = 0 := by rw [hz, map_zero]

/-! ## Integral collapse control -/

/-- The standard point. -/
abbrev point : SSet.{0} := Δ[0]

/-- Its unique vertex. -/
def pointVertex : point _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm 0

/-- The collapse induced by the ordinal degeneracy. -/
def collapse : interval ⟶ point :=
  SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1))

/-- Both source vertices have the same image. -/
theorem collapse_vertex (i : Fin 2) : collapse.app (op ⦋0⦌) (vertex i) = pointVertex := by
  apply SSet.stdSimplex.ext
  intro j
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- The image of the source edge is the degenerate point edge. -/
theorem collapse_edge : collapse.app (op ⦋1⦌) edge = point.σ (0 : Fin 1) pointVertex := by
  apply SSet.stdSimplex.ext
  intro j
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- The simplicial collapse fails monicity already on its two vertices. -/
theorem collapse_not_mono : ¬ Mono collapse := by
  intro h
  have hi := (CategoryTheory.mono_iff_injective (collapse.app (op ⦋0⦌))).mp
    ((NatTrans.mono_iff_mono_app collapse).mp h _)
  have hv : vertex 0 = vertex 1 := hi ((collapse_vertex 0).trans (collapse_vertex 1).symm)
  have hfin : (0 : Fin 2) = 1 := by
    simpa only [vertex, Equiv.apply_symm_apply] using
      congrArg SSet.stdSimplex.obj₀Equiv hv
  exact (by decide : (0 : Fin 2) ≠ 1) hfin

/-- The integral collapse kills the same nonzero edge tensor. -/
theorem collapse_tensor_edge :
    SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} ℤ collapse 1 sourceTensorEdge = 0 := by
  rw [sourceTensorEdge, SSet.tensorNormalizedChainComplexXMap_single]
  change ULift.up (point.normalizedIntegralSimplex (collapse.app _ edge) ⊗ₜ[ℤ] (1 : ℤ)) = _
  rw [collapse_edge,
    point.normalizedIntegralSimplex_of_mem_degenerate _
      (point.σ_mem_degenerate (0 : Fin 1) pointVertex), TensorProduct.zero_tmul]
  rfl

end SimplicialObjectsTest.TensorMonomorphisms

namespace SimplicialObjectsTest.TensorMonomorphisms

example :
    Function.Injective (SSet.tensorNormalizedChainComplexXMap.{0, 0, 0} ℤ face 1).hom :=
  SSet.tensorNormalizedChainComplexXMap_injective.{0, 0, 0} ℤ face 1

example : Mono (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} ℤ face) :=
  SSet.tensorNormalizedChainComplexMap_mono.{0, 0, 0} ℤ face

end SimplicialObjectsTest.TensorMonomorphisms
