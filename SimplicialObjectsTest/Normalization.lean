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
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.Data.ZMod.Basic

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

private noncomputable def normalizedDesc (X : SSet.{0}) {R : ModuleCat ℤ} {n : ℕ}
    {T : ModuleCat ℤ} (f : X.nonDegenerate n → (R ⟶ T)) :
    (X.normalizedChainComplex R).X n ⟶ T :=
  Cofan.IsColimit.desc (X.isColimitCofanNormalizedChainComplex R n) f

@[reassoc (attr := simp)]
private theorem ι_normalizedDesc (X : SSet.{0}) {R : ModuleCat ℤ} {n : ℕ}
    {T : ModuleCat ℤ} (f : X.nonDegenerate n → (R ⟶ T)) (x : X.nonDegenerate n) :
    X.ιNormalizedChainComplex (R := R) x.val ≫ normalizedDesc X f = f x :=
  Cofan.IsColimit.fac (X.isColimitCofanNormalizedChainComplex R n) f x

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

private noncomputable def degreeOneCoordinates {R : ModuleCat ℤ} :
    (interval.normalizedChainComplex R).X 1 ⟶ R :=
  normalizedDesc interval fun _ ↦ 𝟙 _

private theorem edge_coordinates {R : ModuleCat ℤ} :
    interval.ιNormalizedChainComplex (R := R) edge ≫ degreeOneCoordinates = 𝟙 R :=
  ι_normalizedDesc interval (fun _ ↦ 𝟙 _) ⟨edge, edge_nondegenerate⟩

/-- Normalized degree one is the coefficient module via the unique nondegenerate edge. -/
private noncomputable def degreeOneIso {R : ModuleCat ℤ} :
    (interval.normalizedChainComplex R).X 1 ≅ R where
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

/-! ## Normalized coefficient comparison on the same interval -/

open MonoidalCategory
open scoped TensorProduct

private abbrev cyclicModule : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 4)
private noncomputable abbrev cyclicTensor : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℤ :=
  tensorRight cyclicModule
private noncomputable abbrev tensorCoefficient := cyclicTensor.obj integralModule
private noncomputable def tensorOne : tensorCoefficient := (1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 4)

private theorem tensorOne_unitor : (λ_ cyclicModule).hom tensorOne = (1 : ZMod 4) :=
  (ModuleCat.MonoidalCategory.leftUnitor_hom_apply (1 : ℤ) (1 : cyclicModule)).trans
    (one_smul ℤ (1 : ZMod 4))

private noncomputable def sourceEdge : cyclicTensor.obj (intervalComplex.X 1) :=
  cyclicTensor.map (interval.ιNormalizedChainComplex (R := integralModule) edge) tensorOne

private noncomputable def targetEdge :
    (interval.normalizedChainComplex tensorCoefficient).X 1 :=
  interval.ιNormalizedChainComplex (R := tensorCoefficient) edge tensorOne

/-- Tensoring the edge coordinate gives the pure tensor `1 ⊗ₜ 1`. -/
private theorem sourceEdge_coordinate :
    cyclicTensor.map degreeOneCoordinates sourceEdge = tensorOne := by
  have h := cyclicTensor.congr_map (edge_coordinates (R := integralModule))
  rw [cyclicTensor.map_comp, cyclicTensor.map_id] at h
  exact congrArg (fun k : tensorCoefficient ⟶ tensorCoefficient ↦ k tensorOne) h

/-- The normalized coproduct coordinate of the tensor-valued edge is `1 ⊗ₜ 1`. -/
private theorem targetEdge_coordinate : degreeOneCoordinates targetEdge = tensorOne :=
  congrArg (fun k : tensorCoefficient ⟶ tensorCoefficient ↦ k tensorOne)
    (edge_coordinates (R := tensorCoefficient))

private theorem sourceEdge_unitor_coordinate :
    (λ_ cyclicModule).hom (cyclicTensor.map degreeOneCoordinates sourceEdge) = (1 : ZMod 4) :=
  (congrArg (fun x ↦ (λ_ cyclicModule).hom x) sourceEdge_coordinate).trans tensorOne_unitor

private theorem targetEdge_unitor_coordinate :
    (λ_ cyclicModule).hom (degreeOneCoordinates targetEdge) = (1 : ZMod 4) :=
  (congrArg (fun x ↦ (λ_ cyclicModule).hom x) targetEdge_coordinate).trans tensorOne_unitor

private theorem sourceEdge_ne_zero : sourceEdge ≠ 0 := by
  intro h
  have hc := sourceEdge_unitor_coordinate
  rw [h, map_zero, map_zero] at hc
  exact (show (0 : ZMod 4) ≠ 1 from by decide) hc

private theorem targetEdge_ne_zero : targetEdge ≠ 0 := by
  intro h
  have hc := targetEdge_unitor_coordinate
  rw [h, map_zero, map_zero] at hc
  exact (show (0 : ZMod 4) ≠ 1 from by decide) hc

/-- Collapsing the interval annihilates its tensor-valued normalized edge. -/
private theorem sourceEdge_collapse : cyclicTensor.map (collapseMap.f 1) sourceEdge = 0 := by
  rw [collapse_degreeOne, cyclicTensor.map_zero]
  rfl

private theorem targetEdge_collapse :
    (SSet.normalizedChainComplexMap collapse tensorCoefficient).f 1 targetEdge = 0 := by
  have h : (SSet.normalizedChainComplexMap collapse tensorCoefficient).f 1 = 0 :=
    (point.isZero_normalizedChainComplex_X_of_hasDimensionLT tensorCoefficient 1 1).eq_of_tgt _ _
  rw [h]
  rfl

private noncomputable def intervalCoefficientComparison :=
  (SSet.normalizedChainComplexFunctorObjCompMapIso integralModule cyclicTensor).app interval

/-- The coefficient comparison maps the tensor-valued edge to the normalized edge. -/
private theorem comparison_sourceEdge :
    intervalCoefficientComparison.hom.f 1 sourceEdge = targetEdge :=
  congrArg (fun k : tensorCoefficient ⟶
      (interval.normalizedChainComplex tensorCoefficient).X 1 ↦ k tensorOne)
    (SSet.map_ιNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app_f
      integralModule cyclicTensor interval edge)

private theorem comparison_sourceEdge_coordinate :
    (λ_ cyclicModule).hom (degreeOneCoordinates
      (intervalCoefficientComparison.hom.f 1 sourceEdge)) = (1 : ZMod 4) := by
  rw [comparison_sourceEdge]
  exact targetEdge_unitor_coordinate

/-! ## Coefficient-valued maps and the two-sheet interval cover -/

private noncomputable def mixedCoefficientMorphism : coefficientInterval ⟶ coefficientInterval :=
  coefficientScalar 2 +
    (show coefficientInterval ⟶ coefficientInterval from
      Functor.whiskerRight (SSet.const (X := interval) (vertex 0)) (sigmaConst.obj integralModule))

private noncomputable def mixedTransportedCoefficientMorphism :
    interval ⋙ sigmaConst.obj tensorCoefficient ⟶ interval ⋙ sigmaConst.obj tensorCoefficient :=
  Functor.whiskerLeft interval (sigmaConstObjCompIso cyclicTensor integralModule).inv ≫
    Functor.whiskerRight mixedCoefficientMorphism cyclicTensor ≫
      Functor.whiskerLeft interval (sigmaConstObjCompIso cyclicTensor integralModule).hom

private theorem mixedCoefficientComparison :
  (cyclicTensor.mapHomologicalComplex (.down ℕ)).map
      (intervalSplitting.nondegComplexMap intervalSplitting mixedCoefficientMorphism) ≫
      intervalCoefficientComparison.hom =
    intervalCoefficientComparison.hom ≫
      (interval.splitting.map (sigmaConst.obj tensorCoefficient)).nondegComplexMap
        (interval.splitting.map (sigmaConst.obj tensorCoefficient))
        mixedTransportedCoefficientMorphism :=
  SSet.normalizedChainComplexFunctorObjCompMapIso_nondegComplexMap
    integralModule cyclicTensor interval interval mixedCoefficientMorphism

private abbrev twoSheetInterval : SSet.{0} :=
  ((Functor.const _).obj (Fin 2) : SSet.{0}) ⊗ interval

private def twoSheetIntervalMap : twoSheetInterval ⟶ interval :=
  CartesianMonoidalCategory.snd _ _

private def twoSheetSimplex {n : SimplexCategoryᵒᵖ} (i : Fin 2) (x : interval.obj n) :
    twoSheetInterval.obj n :=
  (i, x)

private def twoSheetIndex {n : SimplexCategoryᵒᵖ} (x : twoSheetInterval.obj n) : Fin 2 :=
  x.1

private theorem twoSheetIndex_simplex {n : SimplexCategoryᵒᵖ} (i : Fin 2)
    (x : interval.obj n) : twoSheetIndex (twoSheetSimplex i x) = i := rfl

private theorem twoSheetIntervalMap_simplex {n : SimplexCategoryᵒᵖ} (i : Fin 2)
    (x : interval.obj n) : twoSheetIntervalMap.app n (twoSheetSimplex i x) = x := rfl

private theorem twoSheetSimplex_eta {n : SimplexCategoryᵒᵖ} (x : twoSheetInterval.obj n) :
    twoSheetSimplex (twoSheetIndex x) (twoSheetIntervalMap.app n x) = x := rfl

private theorem twoSheetIntervalMap_equifibered : NatTrans.Equifibered twoSheetIntervalMap := by
  intro i j α
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · intro x y h
    exact Prod.ext (congrArg (twoSheetIndex (n := j)) h.1) h.2
  · intro y x h
    exact ⟨twoSheetSimplex (twoSheetIndex y) x, Prod.ext rfl h.symm,
      twoSheetIntervalMap_simplex _ _⟩

private def twoSheetIntervalFiberEquiv {n : ℕ} (x : interval _⦋n⦌) :
    {y : twoSheetInterval _⦋n⦌ // twoSheetIntervalMap.app _ y = x} ≃ Fin 2 where
  toFun y := twoSheetIndex y.val
  invFun i := ⟨twoSheetSimplex i x, twoSheetIntervalMap_simplex i x⟩
  left_inv y := Subtype.ext
    ((congrArg (twoSheetSimplex (twoSheetIndex y.val)) y.property.symm).trans
      (twoSheetSimplex_eta y.val))
  right_inv i := twoSheetIndex_simplex i x

private theorem twoSheetIntervalMap_finite (x : interval _⦋0⦌) :
    Finite {y : twoSheetInterval _⦋0⦌ // twoSheetIntervalMap.app _ y = x} :=
  Finite.of_equiv (Fin 2) (twoSheetIntervalFiberEquiv x).symm

private theorem twoSheetInterval_lift_nondegenerate (i : Fin 2) :
    twoSheetSimplex i edge ∈ twoSheetInterval.nonDegenerate 1 :=
  SSet.nonDegenerate_of_app_apply twoSheetIntervalMap edge_nondegenerate

private noncomputable def twoSheetIntervalNormalizedMap (R : ModuleCat ℤ) :
    interval.normalizedChainComplex R ⟶ twoSheetInterval.normalizedChainComplex R :=
  (interval.splitting.map (sigmaConst.obj R)).nondegComplexMap
    (twoSheetInterval.splitting.map (sigmaConst.obj R))
    (equifiberedSigmaTransfer twoSheetIntervalMap twoSheetIntervalMap_equifibered
      (SSet.finite_fiber_of_finite_vertices twoSheetIntervalMap
        twoSheetIntervalMap_equifibered twoSheetIntervalMap_finite) R)

private theorem twoSheetIntervalTransfer_generator (R : ModuleCat ℤ) :
    interval.ιChainComplex edge ≫
        (SSet.chainComplexTransfer twoSheetIntervalMap twoSheetIntervalMap_equifibered
          twoSheetIntervalMap_finite R).f 1 =
      twoSheetInterval.ιChainComplex (R := R) (n := 1) (twoSheetSimplex (0 : Fin 2) edge) +
        twoSheetInterval.ιChainComplex (R := R) (n := 1) (twoSheetSimplex (1 : Fin 2) edge) := by
  rw [SSet.ι_chainComplexTransfer_f]
  calc
    _ = ∑ᶠ i : Fin 2, twoSheetInterval.ιChainComplex (twoSheetSimplex i edge) :=
      finsum_eq_of_bijective (twoSheetIntervalFiberEquiv edge)
        (twoSheetIntervalFiberEquiv edge).bijective
        (fun y ↦ congrArg
          (fun z : twoSheetInterval _⦋1⦌ ↦ twoSheetInterval.ιChainComplex (R := R) z)
          ((twoSheetSimplex_eta y.val).symm.trans
            (congrArg (twoSheetSimplex (twoSheetIndex y.val)) y.property)))
    _ = _ := by rw [finsum_eq_sum_of_fintype, Fin.sum_univ_two]

private theorem twoSheetIntervalNormalizedMap_generator (R : ModuleCat ℤ) :
    interval.ιNormalizedChainComplex edge ≫ (twoSheetIntervalNormalizedMap R).f 1 =
      twoSheetInterval.ιNormalizedChainComplex (R := R) (n := 1)
          (twoSheetSimplex (0 : Fin 2) edge) +
        twoSheetInterval.ιNormalizedChainComplex (R := R) (n := 1)
          (twoSheetSimplex (1 : Fin 2) edge) := by
  have hq := HomologicalComplex.congr_hom
    ((interval.splitting.map (sigmaConst.obj R)).toNondegComplex_nondegComplexMap
      (twoSheetInterval.splitting.map (sigmaConst.obj R))
      (equifiberedSigmaTransfer twoSheetIntervalMap twoSheetIntervalMap_equifibered
        (SSet.finite_fiber_of_finite_vertices twoSheetIntervalMap
          twoSheetIntervalMap_equifibered twoSheetIntervalMap_finite) R)) 1
  change (interval.toNormalizedChainComplex R).f 1 ≫
      (twoSheetIntervalNormalizedMap R).f 1 =
    (SSet.chainComplexTransfer twoSheetIntervalMap twoSheetIntervalMap_equifibered
      twoSheetIntervalMap_finite R).f 1 ≫
        (twoSheetInterval.toNormalizedChainComplex R).f 1 at hq
  calc
    _ = interval.ιChainComplex edge ≫ (interval.toNormalizedChainComplex R).f 1 ≫
        (twoSheetIntervalNormalizedMap R).f 1 := by
      rw [← Category.assoc, SSet.ιChainComplex_toNormalizedChainComplex_f]
    _ = (interval.ιChainComplex edge ≫
        (SSet.chainComplexTransfer twoSheetIntervalMap twoSheetIntervalMap_equifibered
          twoSheetIntervalMap_finite R).f 1) ≫
            (twoSheetInterval.toNormalizedChainComplex R).f 1 := by
      simpa only [Category.assoc] using interval.ιChainComplex edge ≫= hq
    _ = _ := by
      rw [twoSheetIntervalTransfer_generator, Preadditive.add_comp,
        SSet.ιChainComplex_toNormalizedChainComplex_f,
        SSet.ιChainComplex_toNormalizedChainComplex_f]

private noncomputable def twoSheetIntervalCoordinate (i : Fin 2) {R : ModuleCat ℤ} :
    (twoSheetInterval.normalizedChainComplex R).X 1 ⟶ R :=
  normalizedDesc twoSheetInterval (n := 1) fun x ↦ if twoSheetIndex x.val = i then 𝟙 R else 0

private theorem twoSheetInterval_lift_coordinate (i j : Fin 2) {R : ModuleCat ℤ} :
    twoSheetInterval.ιNormalizedChainComplex (R := R) (twoSheetSimplex j edge) ≫
        twoSheetIntervalCoordinate i = if j = i then 𝟙 R else 0 := by
  have h :
      twoSheetInterval.ιNormalizedChainComplex (R := R) (n := 1)
          (twoSheetSimplex j edge) ≫ twoSheetIntervalCoordinate (R := R) i =
        if twoSheetIndex (twoSheetSimplex j edge) = i then 𝟙 R else 0 :=
    ι_normalizedDesc twoSheetInterval (R := R) (n := 1) (T := R)
      (fun (x : twoSheetInterval.nonDegenerate 1) ↦
        (if twoSheetIndex x.val = i then 𝟙 R else 0 : R ⟶ R))
      ⟨twoSheetSimplex j edge, twoSheetInterval_lift_nondegenerate j⟩
  exact h.trans
    (congrArg (fun k : Fin 2 ↦ if k = i then (𝟙 R : R ⟶ R) else 0)
      (twoSheetIndex_simplex j edge))

private theorem twoSheetIntervalNormalizedMap_coordinate (i : Fin 2) {R : ModuleCat ℤ} :
    interval.ιNormalizedChainComplex edge ≫ (twoSheetIntervalNormalizedMap R).f 1 ≫
        twoSheetIntervalCoordinate i = 𝟙 R := by
  rw [← Category.assoc, twoSheetIntervalNormalizedMap_generator, Preadditive.add_comp,
    twoSheetInterval_lift_coordinate, twoSheetInterval_lift_coordinate]
  fin_cases i <;> simp

private noncomputable def transferredSourceEdge :
    cyclicTensor.obj ((twoSheetInterval.normalizedChainComplex integralModule).X 1) :=
  cyclicTensor.map ((twoSheetIntervalNormalizedMap integralModule).f 1) sourceEdge

private noncomputable def transferredTargetEdge :
    (twoSheetInterval.normalizedChainComplex tensorCoefficient).X 1 :=
  (twoSheetIntervalNormalizedMap tensorCoefficient).f 1 targetEdge

private noncomputable def coverCoefficientComparison :=
  (SSet.normalizedChainComplexFunctorObjCompMapIso integralModule cyclicTensor).app
    twoSheetInterval

private noncomputable def coverCoefficientComparisonOne :
    cyclicTensor.obj ((twoSheetInterval.normalizedChainComplex integralModule).X 1) ⟶
      (twoSheetInterval.normalizedChainComplex tensorCoefficient).X 1 :=
  coverCoefficientComparison.hom.f 1

private theorem coverCoefficientComparisonOne_generator (x : twoSheetInterval _⦋1⦌) :
    cyclicTensor.map (twoSheetInterval.ιNormalizedChainComplex (R := integralModule) x) ≫
        coverCoefficientComparisonOne =
      twoSheetInterval.ιNormalizedChainComplex (R := tensorCoefficient) x :=
  SSet.map_ιNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app_f
    integralModule cyclicTensor twoSheetInterval x

private noncomputable def comparedTransferredSourceEdge :
    (twoSheetInterval.normalizedChainComplex tensorCoefficient).X 1 :=
  coverCoefficientComparisonOne transferredSourceEdge

private theorem transferredSourceEdge_coordinate_one (i : Fin 2) :
    (λ_ cyclicModule).hom
      (cyclicTensor.map (twoSheetIntervalCoordinate i) transferredSourceEdge) = (1 : ZMod 4) := by
  have h := cyclicTensor.congr_map
    (twoSheetIntervalNormalizedMap_coordinate i (R := integralModule))
  rw [cyclicTensor.map_comp, cyclicTensor.map_comp, cyclicTensor.map_id] at h
  exact (congrArg (fun x ↦ (λ_ cyclicModule).hom x)
    (congrArg (fun k : tensorCoefficient ⟶ tensorCoefficient ↦ k tensorOne) h)).trans
      tensorOne_unitor

private theorem transferredTargetEdge_coordinate_one (i : Fin 2) :
    (λ_ cyclicModule).hom (twoSheetIntervalCoordinate i transferredTargetEdge) = (1 : ZMod 4) :=
  (congrArg (fun x ↦ (λ_ cyclicModule).hom x)
    (congrArg (fun k : tensorCoefficient ⟶ tensorCoefficient ↦ k tensorOne)
      (twoSheetIntervalNormalizedMap_coordinate i (R := tensorCoefficient)))).trans
    tensorOne_unitor

private theorem comparedTransfer_generator :
    cyclicTensor.map (interval.ιNormalizedChainComplex (R := integralModule) edge) ≫
        cyclicTensor.map ((twoSheetIntervalNormalizedMap integralModule).f 1) ≫
        coverCoefficientComparisonOne =
      twoSheetInterval.ιNormalizedChainComplex (R := tensorCoefficient) (n := 1)
          (twoSheetSimplex (0 : Fin 2) edge) +
        twoSheetInterval.ιNormalizedChainComplex (R := tensorCoefficient) (n := 1)
          (twoSheetSimplex (1 : Fin 2) edge) := by
  have h := HomologicalComplex.congr_hom
    (SSet.normalizedChainComplexFunctorObjCompMapIso_finiteFiberTransfer
      integralModule cyclicTensor twoSheetIntervalMap twoSheetIntervalMap_equifibered
      twoSheetIntervalMap_finite) 1
  change cyclicTensor.map ((twoSheetIntervalNormalizedMap integralModule).f 1) ≫
      coverCoefficientComparisonOne = intervalCoefficientComparison.hom.f 1 ≫
        (twoSheetIntervalNormalizedMap tensorCoefficient).f 1 at h
  have hι :=
    SSet.map_ιNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app_f
      integralModule cyclicTensor interval edge
  change cyclicTensor.map (interval.ιNormalizedChainComplex (R := integralModule) edge) ≫
    intervalCoefficientComparison.hom.f 1 =
      interval.ιNormalizedChainComplex (R := tensorCoefficient) edge at hι
  calc
    _ = cyclicTensor.map (interval.ιNormalizedChainComplex (R := integralModule) edge) ≫
        (intervalCoefficientComparison.hom.f 1 ≫
          (twoSheetIntervalNormalizedMap tensorCoefficient).f 1) :=
      congrArg (fun k : cyclicTensor.obj ((interval.normalizedChainComplex integralModule).X 1) ⟶
          (twoSheetInterval.normalizedChainComplex tensorCoefficient).X 1 ↦
        cyclicTensor.map (interval.ιNormalizedChainComplex (R := integralModule) edge) ≫ k) h
    _ = (cyclicTensor.map (interval.ιNormalizedChainComplex (R := integralModule) edge) ≫
        intervalCoefficientComparison.hom.f 1) ≫
          (twoSheetIntervalNormalizedMap tensorCoefficient).f 1 :=
      (Category.assoc _ _ _).symm
    _ = interval.ιNormalizedChainComplex (R := tensorCoefficient) edge ≫
        (twoSheetIntervalNormalizedMap tensorCoefficient).f 1 :=
      congrArg (fun k : tensorCoefficient ⟶
          (interval.normalizedChainComplex tensorCoefficient).X 1 ↦
        k ≫ (twoSheetIntervalNormalizedMap tensorCoefficient).f 1) hι
    _ = _ := twoSheetIntervalNormalizedMap_generator tensorCoefficient

private theorem comparedTransferredSourceEdge_coordinate_one (i : Fin 2) :
    (λ_ cyclicModule).hom (twoSheetIntervalCoordinate i comparedTransferredSourceEdge) =
      (1 : ZMod 4) := by
  have h : (cyclicTensor.map (interval.ιNormalizedChainComplex (R := integralModule) edge) ≫
        cyclicTensor.map ((twoSheetIntervalNormalizedMap integralModule).f 1) ≫
        coverCoefficientComparisonOne) ≫
          twoSheetIntervalCoordinate (R := tensorCoefficient) i = 𝟙 tensorCoefficient := by
    rw [comparedTransfer_generator]
    rw [Preadditive.add_comp, twoSheetInterval_lift_coordinate, twoSheetInterval_lift_coordinate]
    fin_cases i <;> simp
  exact (congrArg (fun x ↦ (λ_ cyclicModule).hom x)
    (congrArg (fun k : tensorCoefficient ⟶ tensorCoefficient ↦ k tensorOne) h)).trans
      tensorOne_unitor

private theorem twoSheetInterval_lifts_push_coordinate (R : ModuleCat ℤ) :
    (twoSheetInterval.ιNormalizedChainComplex (R := R) (n := 1) (twoSheetSimplex (0 : Fin 2) edge) +
        twoSheetInterval.ιNormalizedChainComplex (R := R) (n := 1)
          (twoSheetSimplex (1 : Fin 2) edge)) ≫
      (SSet.normalizedChainComplexMap twoSheetIntervalMap R).f 1 ≫ degreeOneCoordinates =
        (2 : ℕ) • 𝟙 R := by
  rw [Preadditive.add_comp, SSet.ι_normalizedChainComplexMap_f_assoc,
    SSet.ι_normalizedChainComplexMap_f_assoc,
    twoSheetIntervalMap_simplex, twoSheetIntervalMap_simplex]
  simp only [edge_coordinates, two_nsmul]

private theorem transferredEdges_push_coordinate :
    (λ_ cyclicModule).hom (degreeOneCoordinates
      ((SSet.normalizedChainComplexMap twoSheetIntervalMap tensorCoefficient).f 1
        transferredTargetEdge)) = (2 : ZMod 4) ∧
    (λ_ cyclicModule).hom (degreeOneCoordinates
      ((SSet.normalizedChainComplexMap twoSheetIntervalMap tensorCoefficient).f 1
        comparedTransferredSourceEdge)) = (2 : ZMod 4) ∧ (2 : ZMod 4) ≠ 0 := by
  have htarget := twoSheetIntervalNormalizedMap_generator tensorCoefficient
  have hsource := comparedTransfer_generator
  have evaluate (k : tensorCoefficient ⟶
      (twoSheetInterval.normalizedChainComplex tensorCoefficient).X 1)
      (hk : k = twoSheetInterval.ιNormalizedChainComplex (R := tensorCoefficient) (n := 1)
          (twoSheetSimplex (0 : Fin 2) edge) +
        twoSheetInterval.ιNormalizedChainComplex (R := tensorCoefficient) (n := 1)
          (twoSheetSimplex (1 : Fin 2) edge)) :
      (λ_ cyclicModule).hom (degreeOneCoordinates
        ((SSet.normalizedChainComplexMap twoSheetIntervalMap tensorCoefficient).f 1
          (k tensorOne))) = (2 : ZMod 4) := by
    have hcomp : k ≫
        (SSet.normalizedChainComplexMap twoSheetIntervalMap tensorCoefficient).f 1 ≫
          degreeOneCoordinates = (2 : ℕ) • 𝟙 tensorCoefficient := by
      rw [hk]
      exact twoSheetInterval_lifts_push_coordinate tensorCoefficient
    have h := congrArg (fun f : tensorCoefficient ⟶ tensorCoefficient ↦ f tensorOne) hcomp
    calc
      _ = (λ_ cyclicModule).hom ((2 : ℕ) • tensorOne) :=
        congrArg (fun x ↦ (λ_ cyclicModule).hom x) h
      _ = (2 : ℕ) • (1 : ZMod 4) :=
        (map_nsmul (λ_ cyclicModule).hom.hom 2 tensorOne).trans
          (congrArg (fun x ↦ (2 : ℕ) • x) tensorOne_unitor)
      _ = 2 := by decide
  exact ⟨evaluate _ htarget, evaluate _ hsource, by decide⟩

/-! ## Changing the tensor coefficient by multiplication by two -/

private noncomputable def cyclicDouble : cyclicModule ⟶ cyclicModule :=
  (2 : ℕ) • 𝟙 cyclicModule

/-- The stock tensoring functor turns a coefficient morphism into a natural transformation. -/
private noncomputable def tensorDouble : cyclicTensor ⟶ cyclicTensor :=
  (tensoringRight (ModuleCat.{0} ℤ)).map cyclicDouble

private theorem tensorDouble_tensorOne :
    (tensorDouble.app integralModule) tensorOne = (1 : ℤ) ⊗ₜ[ℤ] (2 : ZMod 4) := by
  change (integralModule ◁ cyclicDouble) ((1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 4)) = _
  rw [ModuleCat.MonoidalCategory.whiskerLeft_apply]
  change (1 : ℤ) ⊗ₜ[ℤ] ((2 : ℕ) • (1 : ZMod 4)) = _
  exact congrArg (fun a : ZMod 4 ↦ (1 : ℤ) ⊗ₜ[ℤ] a)
    (show (2 : ℕ) • (1 : ZMod 4) = (2 : ZMod 4) from by decide)

private theorem tensorDouble_tensorOne_unitor :
    (λ_ cyclicModule).hom ((tensorDouble.app integralModule) tensorOne) = (2 : ZMod 4) := by
  rw [tensorDouble_tensorOne]
  exact (ModuleCat.MonoidalCategory.leftUnitor_hom_apply (1 : ℤ) (2 : cyclicModule)).trans
    (one_smul ℤ (2 : ZMod 4))

private theorem tensorDouble_ne_id : tensorDouble ≠ 𝟙 cyclicTensor := by
  intro h
  have hc := tensorDouble_tensorOne_unitor
  rw [h] at hc
  change (λ_ cyclicModule).hom tensorOne = (2 : ZMod 4) at hc
  rw [tensorOne_unitor] at hc
  exact (show (1 : ZMod 4) ≠ 2 from by decide) hc

private noncomputable def doubledSourceEdge : cyclicTensor.obj (intervalComplex.X 1) :=
  (tensorDouble.app (intervalComplex.X 1)) sourceEdge

private noncomputable def doubledTargetEdge :
    (interval.normalizedChainComplex tensorCoefficient).X 1 :=
  interval.ιNormalizedChainComplex (R := tensorCoefficient) edge
    ((tensorDouble.app integralModule) tensorOne)

/-- The changed source coordinate is computed from naturality of the stock tensor map. -/
private theorem doubledSourceEdge_coordinate :
    cyclicTensor.map degreeOneCoordinates doubledSourceEdge =
      (tensorDouble.app integralModule) tensorOne := by
  have h := congrArg
    (fun k : cyclicTensor.obj (intervalComplex.X 1) ⟶ tensorCoefficient ↦ k sourceEdge)
    (tensorDouble.naturality degreeOneCoordinates).symm
  change cyclicTensor.map degreeOneCoordinates doubledSourceEdge =
    (tensorDouble.app integralModule) (cyclicTensor.map degreeOneCoordinates sourceEdge) at h
  exact h.trans (congrArg (fun x ↦ (tensorDouble.app integralModule) x) sourceEdge_coordinate)

private theorem doubledTargetEdge_coordinate :
    degreeOneCoordinates doubledTargetEdge = (tensorDouble.app integralModule) tensorOne :=
  congrArg (fun k : tensorCoefficient ⟶ tensorCoefficient ↦
    k ((tensorDouble.app integralModule) tensorOne))
      (edge_coordinates (R := tensorCoefficient))

private theorem doubledSourceEdge_unitor_coordinate :
    (λ_ cyclicModule).hom (cyclicTensor.map degreeOneCoordinates doubledSourceEdge) =
      (2 : ZMod 4) :=
  (congrArg (fun x ↦ (λ_ cyclicModule).hom x) doubledSourceEdge_coordinate).trans
    tensorDouble_tensorOne_unitor

private theorem doubledTargetEdge_unitor_coordinate :
    (λ_ cyclicModule).hom (degreeOneCoordinates doubledTargetEdge) = (2 : ZMod 4) :=
  (congrArg (fun x ↦ (λ_ cyclicModule).hom x) doubledTargetEdge_coordinate).trans
    tensorDouble_tensorOne_unitor

private theorem doubledSourceEdge_ne_zero : doubledSourceEdge ≠ 0 := by
  intro h
  have hc := doubledSourceEdge_unitor_coordinate
  rw [h, map_zero, map_zero] at hc
  exact (show (0 : ZMod 4) ≠ 2 from by decide) hc

private theorem doubledTargetEdge_ne_zero : doubledTargetEdge ≠ 0 := by
  intro h
  have hc := doubledTargetEdge_unitor_coordinate
  rw [h, map_zero, map_zero] at hc
  exact (show (0 : ZMod 4) ≠ 2 from by decide) hc

/-- The coefficient-functor naturality equation on the standard normalized interval. -/
private theorem tensorDoubleComparisonNaturality :
  (tensorDouble.mapHomologicalComplex (.down ℕ)).app intervalComplex ≫
      intervalCoefficientComparison.hom =
    intervalCoefficientComparison.hom ≫
      (interval.splitting.map (sigmaConst.obj tensorCoefficient)).nondegComplexMap
        (interval.splitting.map (sigmaConst.obj tensorCoefficient))
        (Functor.whiskerLeft interval (sigmaConst.map (tensorDouble.app integralModule))) :=
  SSet.normalizedChainComplexFunctorObjCompMapIso_naturality
    integralModule cyclicTensor cyclicTensor tensorDouble interval

/-- The same naturality square sends the changed original edge to its
coefficientwise changed normalized edge, of coordinate two modulo four. -/
private theorem comparison_doubledSourceEdge :
    intervalCoefficientComparison.hom.f 1 doubledSourceEdge = doubledTargetEdge := by
  have h := congrArg
    (fun k : cyclicTensor.obj (intervalComplex.X 1) ⟶
        (interval.normalizedChainComplex tensorCoefficient).X 1 ↦ k sourceEdge)
    (HomologicalComplex.congr_hom tensorDoubleComparisonNaturality 1)
  change intervalCoefficientComparison.hom.f 1 doubledSourceEdge =
    ((interval.splitting.map (sigmaConst.obj tensorCoefficient)).nondegComplexMap
      (interval.splitting.map (sigmaConst.obj tensorCoefficient))
      (Functor.whiskerLeft interval (sigmaConst.map (tensorDouble.app integralModule)))).f 1
        (intervalCoefficientComparison.hom.f 1 sourceEdge) at h
  rw [comparison_sourceEdge] at h
  exact h.trans (congrArg
    (fun k : tensorCoefficient ⟶
        (interval.normalizedChainComplex tensorCoefficient).X 1 ↦ k tensorOne)
    (SSet.ιNormalizedChainComplex_nondegComplexMap_coefficient
      tensorCoefficient interval (tensorDouble.app integralModule) edge))

private theorem comparison_doubledSourceEdge_unitor_coordinate :
    (λ_ cyclicModule).hom (degreeOneCoordinates
      (intervalCoefficientComparison.hom.f 1 doubledSourceEdge)) = (2 : ZMod 4) := by
  rw [comparison_doubledSourceEdge]
  exact doubledTargetEdge_unitor_coordinate

private theorem coefficientScalar_app (m n : ℕ) :
    (coefficientScalar m).app (op ⦋n⦌) = m • 𝟙 (coefficientInterval _⦋n⦌) := by
  simpa only [coefficientScalar, NatTrans.id_app] using
    (NatTrans.app_nsmul (op ⦋n⦌) (𝟙 coefficientInterval) m)

private noncomputable def intervalCoefficientSimplex {n : ℕ} (x : interval _⦋n⦌) :
    integralModule ⟶ coefficientInterval _⦋n⦌ :=
  Sigma.ι (fun _ : interval _⦋n⦌ ↦ integralModule) x

private noncomputable def intervalRawBasis (x : interval.splitting.N 1) :
    integralModule ⟶ intervalSplitting.N 1 :=
  Sigma.ι (fun _ : interval.splitting.N 1 ↦ integralModule) x

private theorem intervalRawBasis_ι (x : interval.splitting.N 1) :
    intervalRawBasis x ≫ intervalSplitting.ι 1 =
      intervalCoefficientSimplex (interval.splitting.ι 1 x) :=
  (Sigma.ι_comp_map'
    (f := fun _ : interval.splitting.N 1 ↦ integralModule)
    (g := fun _ : interval _⦋1⦌ ↦ integralModule)
    (interval.splitting.ι 1) (fun _ ↦ 𝟙 integralModule) x).trans (Category.id_comp _)

/-- The mixed coefficient map does not preserve the raw nondegenerate summand in degree one. -/
private theorem mixedCoefficientMorphism_not_compatible :
    ¬ ∃ f : intervalSplitting.N 1 ⟶ intervalSplitting.N 1,
      intervalSplitting.ι 1 ≫ mixedCoefficientMorphism.app (op ⦋1⦌) =
        f ≫ intervalSplitting.ι 1 := by
  let c : coefficientInterval _⦋1⦌ ⟶ integralModule :=
    Sigma.desc fun x : interval _⦋1⦌ ↦ if x 1 = 0 then 𝟙 integralModule else 0
  have hb (x : interval _⦋1⦌) : intervalCoefficientSimplex x ≫ c =
      if x 1 = 0 then 𝟙 integralModule else 0 :=
    Sigma.ι_desc (fun x : interval _⦋1⦌ ↦ if x 1 = 0 then 𝟙 integralModule else 0) x
  have hι : intervalSplitting.ι 1 ≫ c = 0 := by
    apply Sigma.hom_ext (f := fun _ : interval.splitting.N 1 ↦ integralModule)
    intro x
    change intervalRawBasis x ≫ (intervalSplitting.ι 1 ≫ c) =
      intervalRawBasis x ≫ (0 : intervalSplitting.N 1 ⟶ integralModule)
    calc
      _ = (intervalRawBasis x ≫ intervalSplitting.ι 1) ≫ c :=
        (Category.assoc _ _ _).symm
      _ = intervalCoefficientSimplex (interval.splitting.ι 1 x) ≫ c :=
        congrArg (fun k : integralModule ⟶ coefficientInterval _⦋1⦌ ↦ k ≫ c)
          (intervalRawBasis_ι x)
      _ = 0 := by
        have hx : interval.splitting.ι 1 x ∈ interval.nonDegenerate 1 := x.property
        rw [hb, edge_unique _ hx]
        rfl
      _ = _ := (comp_zero (f := intervalRawBasis x)).symm
  have hm : intervalCoefficientSimplex edge ≫
      mixedCoefficientMorphism.app (op ⦋1⦌) ≫ c = 𝟙 integralModule := by
    let d : coefficientInterval _⦋1⦌ ⟶ coefficientInterval _⦋1⦌ :=
      (Functor.whiskerRight (SSet.const (X := interval) (vertex 0))
        (sigmaConst.obj integralModule)).app (op ⦋1⦌)
    have hd : intervalCoefficientSimplex edge ≫ d =
        intervalCoefficientSimplex
          ((SSet.const (X := interval) (vertex 0)).app (op ⦋1⦌) edge) :=
      (Sigma.ι_comp_map'
        (f := fun _ : interval _⦋1⦌ ↦ integralModule)
        (g := fun _ : interval _⦋1⦌ ↦ integralModule)
        ((SSet.const (X := interval) (vertex 0)).app (op ⦋1⦌))
        (fun _ ↦ 𝟙 integralModule) edge).trans (Category.id_comp _)
    change intervalCoefficientSimplex edge ≫
      ((coefficientScalar 2).app (op ⦋1⦌) + d) ≫ c = _
    rw [coefficientScalar_app, Preadditive.add_comp, Preadditive.comp_add,
      Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
      ← Category.assoc, hd, hb, hb]
    change (2 : ℕ) • (0 : integralModule ⟶ integralModule) + 𝟙 integralModule = _
    rw [smul_zero, zero_add]
  let e : integralModule ⟶ intervalSplitting.N 1 :=
    intervalRawBasis ⟨edge, edge_nondegenerate⟩
  have he : e ≫ intervalSplitting.ι 1 = intervalCoefficientSimplex edge :=
    intervalRawBasis_ι ⟨edge, edge_nondegenerate⟩
  rintro ⟨f, hf⟩
  have hpost := congrArg
    (fun k : intervalSplitting.N 1 ⟶ coefficientInterval _⦋1⦌ ↦ e ≫ k ≫ c) hf
  have hleft : e ≫ (intervalSplitting.ι 1 ≫ mixedCoefficientMorphism.app (op ⦋1⦌)) ≫ c =
      𝟙 integralModule := by
    calc
      _ = e ≫ intervalSplitting.ι 1 ≫ mixedCoefficientMorphism.app (op ⦋1⦌) ≫ c :=
        congrArg (fun k : intervalSplitting.N 1 ⟶ integralModule ↦ e ≫ k)
          (Category.assoc (intervalSplitting.ι 1) (mixedCoefficientMorphism.app (op ⦋1⦌)) c)
      _ = (e ≫ intervalSplitting.ι 1) ≫ mixedCoefficientMorphism.app (op ⦋1⦌) ≫ c :=
        (Category.assoc e (intervalSplitting.ι 1)
          (mixedCoefficientMorphism.app (op ⦋1⦌) ≫ c)).symm
      _ = intervalCoefficientSimplex edge ≫ mixedCoefficientMorphism.app (op ⦋1⦌) ≫ c :=
        congrArg (fun k : integralModule ⟶ coefficientInterval _⦋1⦌ ↦
          k ≫ mixedCoefficientMorphism.app (op ⦋1⦌) ≫ c) he
      _ = _ := hm
  have hright : e ≫ (f ≫ intervalSplitting.ι 1) ≫ c = 0 := by
    calc
      _ = e ≫ f ≫ (intervalSplitting.ι 1 ≫ c) :=
        congrArg (fun k : intervalSplitting.N 1 ⟶ integralModule ↦ e ≫ k)
          (Category.assoc f (intervalSplitting.ι 1) c)
      _ = e ≫ f ≫ (0 : intervalSplitting.N 1 ⟶ integralModule) :=
        congrArg (fun k : intervalSplitting.N 1 ⟶ integralModule ↦ e ≫ f ≫ k) hι
      _ = 0 := by simp only [comp_zero]
  have hc : 𝟙 integralModule = 0 := hleft.symm.trans (hpost.trans hright)
  exact (one_ne_zero : (1 : ℤ) ≠ 0)
    (congrArg (fun k : integralModule ⟶ integralModule ↦ k (1 : ℤ)) hc)

end SimplicialObjectsTest.Normalization
