/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects.Normalization
import SimplicialObjects.FiniteFiberTransfer
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Integral chains on the standard simplicial interval

The normalized basis consists of the two vertices and the unique nondegenerate
edge. The boundary is `a ↦ (-a,a)`; collapse to a point is zero in degree one
and nonzero in degree zero. Coefficient scalars and finite-fiber transfers give
maps of coefficient-valued simplicial objects.
-/

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SimplicialObjectsTest.Normalization

private abbrev integralModule : ModuleCat ℤ := ModuleCat.of ℤ ℤ
private abbrev interval : SSet.{0} := Δ[1]
private abbrev point : SSet.{0} := Δ[0]
private noncomputable abbrev intervalComplex := interval.normalizedChainComplex integralModule
private noncomputable abbrev pointComplex := point.normalizedChainComplex integralModule
private def vertex (i : Fin 2) : interval _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm i
private def edge : interval _⦋1⦌ := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)

private theorem vertex_nondegenerate (i : Fin 2) : vertex i ∈ interval.nonDegenerate 0 := by
  simp [SSet.nondegenerate_zero]

private theorem edge_nondegenerate : edge ∈ interval.nonDegenerate 1 :=
  SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate 1

private theorem edge_unique (x : interval _⦋1⦌) (hx : x ∈ interval.nonDegenerate 1) :
    x = edge := by
  simpa only [interval, edge, SSet.stdSimplex.nonDegenerate_top_dim, Set.mem_singleton_iff] using hx

private theorem vertex_cases (x : interval _⦋0⦌) : x = vertex 0 ∨ x = vertex 1 := by
  have h : x 0 = (0 : Fin 2) ∨ x 0 = (1 : Fin 2) := by
    generalize x 0 = i
    fin_cases i <;> simp
  rcases h with h | h
  · left
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i
    exact h
  · right
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i
    exact h

private noncomputable def normalizedDesc (X : SSet.{0}) {n : ℕ} {T : ModuleCat ℤ}
    (f : X.nonDegenerate n → (integralModule ⟶ T)) :
    (X.normalizedChainComplex integralModule).X n ⟶ T :=
  Cofan.IsColimit.desc (X.isColimitCofanNormalizedChainComplex integralModule n) f

@[reassoc (attr := simp)]
private theorem ι_normalizedDesc (X : SSet.{0}) {n : ℕ} {T : ModuleCat ℤ}
    (f : X.nonDegenerate n → (integralModule ⟶ T)) (x : X.nonDegenerate n) :
    X.ιNormalizedChainComplex x.val ≫ normalizedDesc X f = f x :=
  Cofan.IsColimit.fac (X.isColimitCofanNormalizedChainComplex integralModule n) f x

private noncomputable def degreeZeroCoordinates : intervalComplex.X 0 ⟶
    integralModule ⊞ integralModule :=
  normalizedDesc interval fun x ↦ if x.val 0 = 0 then biprod.inl else biprod.inr

private noncomputable def degreeZeroGenerators : integralModule ⊞ integralModule ⟶
    intervalComplex.X 0 :=
  biprod.desc (interval.ιNormalizedChainComplex (vertex 0))
    (interval.ιNormalizedChainComplex (vertex 1))

private theorem vertex_coordinates (i : Fin 2) :
    interval.ιNormalizedChainComplex (vertex i) ≫ degreeZeroCoordinates =
      if i = 0 then biprod.inl else biprod.inr := by
  simpa [degreeZeroCoordinates, vertex, SSet.stdSimplex.obj₀Equiv, SSet.stdSimplex.const] using
    ι_normalizedDesc interval
      (fun x ↦ if x.val 0 = 0 then biprod.inl else biprod.inr)
      ⟨vertex i, vertex_nondegenerate i⟩

/-- Normalized degree zero is the binary biproduct of two copies of ℤ. -/
private noncomputable def degreeZeroIso : intervalComplex.X 0 ≅
    integralModule ⊞ integralModule where
  hom := degreeZeroCoordinates
  inv := degreeZeroGenerators
  hom_inv_id := by
    apply SSet.normalizedChainComplex_hom_ext
    intro x hx
    rcases vertex_cases x with rfl | rfl <;>
      simp [← Category.assoc, vertex_coordinates, degreeZeroGenerators]
  inv_hom_id := by
    apply biprod.hom_ext' <;>
      simp [degreeZeroGenerators, vertex_coordinates]

private noncomputable def degreeOneCoordinates : intervalComplex.X 1 ⟶ integralModule :=
  normalizedDesc interval fun _ ↦ 𝟙 _

private theorem edge_coordinates :
    interval.ιNormalizedChainComplex edge ≫ degreeOneCoordinates = 𝟙 integralModule :=
  ι_normalizedDesc interval (fun _ ↦ 𝟙 _) ⟨edge, edge_nondegenerate⟩

/-- Normalized degree one is a copy of ℤ, with the nondegenerate edge as basis. -/
private noncomputable def degreeOneIso : intervalComplex.X 1 ≅ integralModule where
  hom := degreeOneCoordinates
  inv := interval.ιNormalizedChainComplex edge
  hom_inv_id := by
    apply SSet.normalizedChainComplex_hom_ext
    intro x hx
    obtain rfl := edge_unique x hx
    simp [← Category.assoc, edge_coordinates]
  inv_hom_id := edge_coordinates

private theorem edge_boundary :
    interval.ιNormalizedChainComplex edge ≫ intervalComplex.d 1 0 =
      interval.ιNormalizedChainComplex (vertex 1) -
        interval.ιNormalizedChainComplex (vertex 0) := by
  rw [SSet.ιNormalizedChainComplex_d, Fin.sum_univ_two]
  have h₀ : interval.δ (0 : Fin 2) edge = vertex 1 := by decide
  have h₁ : interval.δ (1 : Fin 2) edge = vertex 0 := by decide
  simp [h₀, h₁, sub_eq_add_neg]

/-- In the displayed coordinates the boundary is `a ↦ (-a,a)`. -/
private theorem boundary_coordinates :
    degreeOneIso.inv ≫ intervalComplex.d 1 0 ≫ degreeZeroIso.hom =
      biprod.lift (-𝟙 integralModule) (𝟙 integralModule) := by
  change interval.ιNormalizedChainComplex edge ≫ intervalComplex.d 1 0 ≫
    degreeZeroCoordinates = _
  rw [← Category.assoc, edge_boundary, Preadditive.sub_comp]
  simp only [vertex_coordinates, ↓reduceIte, one_ne_zero]
  apply biprod.hom_ext <;> simp

/-- The edge generator is nonzero. -/
private theorem edge_generator_nonzero :
    interval.ιNormalizedChainComplex (R := integralModule) edge (1 : ℤ) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : integralModule ⟶ integralModule ↦ f (1 : ℤ)) edge_coordinates
  change degreeOneCoordinates
    (interval.ιNormalizedChainComplex (R := integralModule) edge (1 : ℤ)) = 1 at hc
  rw [h, map_zero] at hc
  exact (zero_ne_one : (0 : ℤ) ≠ 1) hc

private theorem degreeOne_nonzero : ¬ IsZero (intervalComplex.X 1) := by
  intro h
  have hz : interval.ιNormalizedChainComplex (R := integralModule) edge = 0 := h.eq_of_tgt _ _
  apply edge_generator_nonzero
  rw [hz]
  rfl

private def collapse : interval ⟶ point := SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1))
private noncomputable def collapseMap : intervalComplex ⟶ pointComplex :=
  SSet.normalizedChainComplexMap collapse integralModule

/-- The collapse kills the entire normalized degree-one map, not just one summand. -/
private theorem collapse_degreeOne : collapseMap.f 1 = 0 :=
  (point.isZero_normalizedChainComplex_X_of_hasDimensionLT integralModule 1 1).eq_of_tgt _ _

private noncomputable def pointCoordinate : pointComplex.X 0 ⟶ integralModule :=
  normalizedDesc point fun _ ↦ 𝟙 _

private theorem collapse_vertex (i : Fin 2) :
    interval.ιNormalizedChainComplex (vertex i) ≫ collapseMap.f 0 ≫ pointCoordinate =
      𝟙 integralModule := by
  rw [collapseMap, SSet.ι_normalizedChainComplexMap_f_assoc]
  exact ι_normalizedDesc point (fun _ ↦ 𝟙 _)
    ⟨collapse.app _ (vertex i), by simp [SSet.nondegenerate_zero]⟩

/-- Collapse in degree zero sends both basis vectors to 1. -/
private theorem collapse_degreeZero_coordinates :
    degreeZeroIso.inv ≫ collapseMap.f 0 ≫ pointCoordinate =
      biprod.desc (𝟙 integralModule) (𝟙 integralModule) := by
  apply biprod.hom_ext' <;>
    simp [degreeZeroIso, degreeZeroGenerators, collapse_vertex]

private theorem collapse_degreeZero_nonzero : collapseMap.f 0 ≠ 0 := by
  intro h
  have hc := collapse_vertex 0
  rw [h, zero_comp, comp_zero] at hc
  have hone := congrArg (fun f : integralModule ⟶ integralModule ↦ f (1 : ℤ)) hc
  exact (zero_ne_one : (0 : ℤ) ≠ 1) hone

/-! ## Descent of coefficient-valued morphisms -/

private noncomputable abbrev intervalSplitting :=
  interval.splitting.map (sigmaConst.obj integralModule)
private noncomputable abbrev pointSplitting :=
  point.splitting.map (sigmaConst.obj integralModule)

private noncomputable abbrev coefficientInterval :=
  ((CategoryTheory.SimplicialObject.whiskering _ _).obj (sigmaConst.obj integralModule)).obj
    interval

/-- Multiplication by a coefficient scalar on the free simplicial interval. -/
private noncomputable def coefficientScalar (m : ℕ) : coefficientInterval ⟶ coefficientInterval :=
  m • 𝟙 _

private theorem scalar_normalized_component (m n : ℕ) :
    (intervalSplitting.nondegComplexMap intervalSplitting (coefficientScalar m)).f n =
      m • 𝟙 (intervalComplex.X n) := by
  rw [intervalSplitting.nondegComplexMap_f]
  change intervalSplitting.fromNondegComplex.f n ≫ (m • 𝟙 _) ≫
    intervalSplitting.toNondegComplex.f n = m • 𝟙 (intervalSplitting.nondegComplex.X n)
  simp only [Preadditive.comp_nsmul, Category.id_comp, Preadditive.nsmul_comp]
  have h := HomologicalComplex.congr_hom
    intervalSplitting.fromNondegComplex_toNondegComplex n
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using congrArg (m • ·) h

private noncomputable abbrev splitInterval : SimplicialObject.Split (ModuleCat ℤ) :=
  .mk' intervalSplitting

/-- Coefficient scalars preserve the chosen nondegenerate summands. -/
private noncomputable def compatibleScalar (m : ℕ) : splitInterval ⟶ splitInterval where
  F := coefficientScalar m
  f := fun _ ↦ m • 𝟙 _
  comm := fun n ↦ by
    change intervalSplitting.ι n ≫ (m • 𝟙 _) = (m • 𝟙 _) ≫ intervalSplitting.ι n
    simp only [Preadditive.comp_nsmul, Category.comp_id, Preadditive.nsmul_comp, Category.id_comp]

/-- The compatible-map functor doubles the nondegenerate edge coordinate. -/
private theorem compatible_scalar_edge_coordinates :
    degreeOneIso.inv ≫
      (SimplicialObject.Split.nondegComplexFunctor.map (compatibleScalar 2)).f 1 ≫
        degreeOneCoordinates = (2 : ℕ) • 𝟙 integralModule := by
  rw [← SimplicialObject.Split.nondegComplexMap_eq_nondegComplexFunctor_map]
  change degreeOneIso.inv ≫
    (intervalSplitting.nondegComplexMap intervalSplitting (coefficientScalar 2)).f 1 ≫
      degreeOneCoordinates = _
  rw [scalar_normalized_component]
  change degreeOneIso.inv ≫ ((2 : ℕ) • 𝟙 (intervalComplex.X 1)) ≫ degreeOneIso.hom = _
  simp

private theorem compatible_scalar_edge :
    degreeOneCoordinates
      ((SimplicialObject.Split.nondegComplexFunctor.map (compatibleScalar 2)).f 1
        (interval.ιNormalizedChainComplex (R := integralModule) edge (1 : ℤ))) = 2 := by
  exact congrArg (fun f : integralModule ⟶ integralModule ↦ f (1 : ℤ))
    compatible_scalar_edge_coordinates

/-- The identity fixes the nondegenerate edge coordinate. -/
private theorem identity_edge_coordinates :
    degreeOneIso.inv ≫
      (intervalSplitting.nondegComplexMap intervalSplitting (𝟙 _)).f 1 ≫
        degreeOneCoordinates = 𝟙 integralModule := by
  rw [intervalSplitting.nondegComplexMap_id]
  change degreeOneIso.inv ≫ (𝟙 (intervalComplex.X 1)) ≫ degreeOneIso.hom = _
  simp only [Category.id_comp, Iso.inv_hom_id]

/-- Scalars two and three compose to multiplication by six on the edge. -/
private theorem scalar_composite_coordinates :
    degreeOneIso.inv ≫
      (intervalSplitting.nondegComplexMap intervalSplitting
        (coefficientScalar 2 ≫ coefficientScalar 3)).f 1 ≫ degreeOneCoordinates =
      (6 : ℕ) • 𝟙 integralModule := by
  rw [intervalSplitting.nondegComplexMap_comp intervalSplitting intervalSplitting]
  simp only [HomologicalComplex.comp_f, scalar_normalized_component]
  change degreeOneIso.inv ≫
    (((2 : ℕ) • 𝟙 (intervalComplex.X 1)) ≫ ((3 : ℕ) • 𝟙 (intervalComplex.X 1))) ≫
      degreeOneCoordinates = _
  simp [degreeOneIso, edge_coordinates, smul_smul]

private theorem scalar_composite_edge :
    degreeOneCoordinates
      ((intervalSplitting.nondegComplexMap intervalSplitting
        (coefficientScalar 2 ≫ coefficientScalar 3)).f 1
          (interval.ιNormalizedChainComplex (R := integralModule) edge (1 : ℤ))) = 6 := by
  exact congrArg (fun f : integralModule ⟶ integralModule ↦ f (1 : ℤ))
    scalar_composite_coordinates

/-- The projection equation identifies scalar descent as twice the identity. -/
private theorem scalar_characterization :
    ((2 : ℕ) • 𝟙 intervalComplex) =
      intervalSplitting.nondegComplexMap intervalSplitting (coefficientScalar 2) := by
  apply (intervalSplitting.nondegComplexMap_eq_iff intervalSplitting
    (coefficientScalar 2) _).mpr
  change intervalSplitting.toNondegComplex ≫ ((2 : ℕ) • 𝟙 intervalSplitting.nondegComplex) =
    (AlgebraicTopology.alternatingFaceMapComplex _).map ((2 : ℕ) • 𝟙 coefficientInterval) ≫
      intervalSplitting.toNondegComplex
  simp

private noncomputable def edgeCochain : coefficientInterval _⦋1⦌ ⟶ integralModule :=
  intervalSplitting.toNondegComplex.f 1 ≫ degreeOneCoordinates

private theorem edgeCochain_on_edge :
    interval.ιChainComplex edge ≫ edgeCochain = 𝟙 integralModule := by
  change interval.ιChainComplex edge ≫
    (interval.toNormalizedChainComplex integralModule).f 1 ≫ degreeOneCoordinates = _
  rw [← Category.assoc, SSet.ιChainComplex_toNormalizedChainComplex_f, edge_coordinates]

private theorem edgeCochain_vanish :
    AlgebraicTopology.DoldKan.DegeneraciesVanish (X := coefficientInterval) (n := 1)
      edgeCochain := by
  have hq : AlgebraicTopology.DoldKan.DegeneraciesVanish (X := coefficientInterval) (n := 1)
      (intervalSplitting.toNondegComplex.f 1) := by
    rw [intervalSplitting.toNondegComplex_f]
    exact (AlgebraicTopology.DoldKan.degeneraciesVanishPInfty_f coefficientInterval 1).comp _
  exact hq.comp degreeOneCoordinates

/-- The degree-one quotient recovers the edge coordinate as its unique factor. -/
private theorem degreeOne_quotient (b : intervalComplex.X 1 ⟶ integralModule) :
    intervalSplitting.toNondegComplex.f 1 ≫ b = edgeCochain ↔
      b = degreeOneCoordinates := by
  have hu := (intervalSplitting.degeneraciesVanish_iff_existsUnique 1 edgeCochain).mp
    edgeCochain_vanish
  have hs : intervalSplitting.fromNondegComplex.f 1 ≫ edgeCochain =
      degreeOneCoordinates := by
    change (interval.fromNormalizedChainComplex integralModule).f 1 ≫
      (interval.toNormalizedChainComplex integralModule).f 1 ≫ degreeOneCoordinates = _
    simp only [SSet.fromNormalizedChainComplex_f_toNormalizedChainComplex_f_assoc]
  have hf : intervalSplitting.toNondegComplex.f 1 ≫ degreeOneCoordinates = edgeCochain := by
    calc
      _ = intervalSplitting.toNondegComplex.f 1 ≫
          (intervalSplitting.fromNondegComplex.f 1 ≫ edgeCochain) :=
        congrArg (fun b : intervalComplex.X 1 ⟶ integralModule ↦
          intervalSplitting.toNondegComplex.f 1 ≫ b) hs.symm
      _ = edgeCochain :=
        intervalSplitting.toNondegComplex_f_factor 1 edgeCochain edgeCochain_vanish
  constructor
  · intro hb
    exact ExistsUnique.unique hu hb hf
  · rintro rfl
    exact hf

private noncomputable def genericCollapse : intervalComplex ⟶ pointComplex :=
  intervalSplitting.nondegComplexMap pointSplitting
    (Functor.whiskerRight collapse (sigmaConst.obj integralModule))

private theorem genericCollapse_agrees : genericCollapse = collapseMap :=
  SSet.nondegComplexMap_eq_normalizedChainComplexMap collapse integralModule

private theorem genericCollapse_degreeOne : genericCollapse.f 1 = 0 := by
  rw [genericCollapse_agrees]
  exact collapse_degreeOne

private theorem genericCollapse_degreeZero_nonzero : genericCollapse.f 0 ≠ 0 := by
  rw [genericCollapse_agrees]
  exact collapse_degreeZero_nonzero

/-- In degree zero every map has a unique factor through the normalized projection. -/
private theorem degreeZero_quotient (a :
    (((CategoryTheory.SimplicialObject.whiskering _ _).obj (sigmaConst.obj integralModule)).obj
      interval) _⦋0⦌ ⟶ integralModule) :
    ∃! b : intervalComplex.X 0 ⟶ integralModule,
      intervalSplitting.toNondegComplex.f 0 ≫ b = a := by
  apply (intervalSplitting.degeneraciesVanish_iff_existsUnique 0 a).mp
  exact (AlgebraicTopology.DoldKan.degeneraciesVanish_zero_iff_true a).mpr True.intro


/-- The very same construction accepts the coefficient-valued transfer, which
is not required to arise from a simplicial-set map. -/
private noncomputable def normalizedTransfer {F G : SSet.{0}} (p : F ⟶ G)
    (hp : NatTrans.Equifibered p)
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g}) :
    G.normalizedChainComplex integralModule ⟶ F.normalizedChainComplex integralModule :=
  (G.splitting.map (sigmaConst.obj integralModule)).nondegComplexMap
    (F.splitting.map (sigmaConst.obj integralModule))
    (equifiberedSigmaTransfer p hp (SSet.finite_fiber_of_finite_vertices p hp hf) integralModule)

/-- Normalized transfer followed by pushforward is multiplication by the sheet number. -/
private theorem normalizedTransfer_sheet {F G : SSet.{0}} (p : F ⟶ G)
    (hp : NatTrans.Equifibered p)
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g})
    (d : ℕ) (hd : ∀ g : G _⦋0⦌, Nat.card {f : F _⦋0⦌ // p.app _ f = g} = d) :
    normalizedTransfer p hp hf ≫ SSet.normalizedChainComplexMap p integralModule =
      d • 𝟙 (G.normalizedChainComplex integralModule) := by
  apply (cancel_epi (G.toNormalizedChainComplex integralModule)).mp
  have htr : G.toNormalizedChainComplex integralModule ≫ normalizedTransfer p hp hf =
      SSet.chainComplexTransfer p hp hf integralModule ≫
        F.toNormalizedChainComplex integralModule :=
    (G.splitting.map (sigmaConst.obj integralModule)).toNondegComplex_nondegComplexMap
      (F.splitting.map (sigmaConst.obj integralModule))
      (equifiberedSigmaTransfer p hp
        (SSet.finite_fiber_of_finite_vertices p hp hf) integralModule)
  rw [← Category.assoc, htr, Category.assoc,
    SSet.toNormalizedChainComplex_normalizedChainComplexMap, ← Category.assoc,
    SSet.chainComplexTransfer_comp_map p hp hf integralModule d hd]
  simp

end SimplicialObjectsTest.Normalization
