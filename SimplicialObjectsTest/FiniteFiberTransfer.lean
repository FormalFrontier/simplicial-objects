/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift

/-! Integral constant-sheet, composite and empty-sheet clients for finite-fiber transfer. -/

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SimplicialObjectsTest.FiniteFiberTransfer

private abbrev twoSheets : SSet.{0} := (Functor.const _).obj (Fin 2)
private abbrev point : SSet.{0} := (Functor.const _).obj PUnit

private def twoSheetMap : twoSheets ⟶ point :=
  (Functor.const _).map (↾fun _ : Fin 2 ↦ PUnit.unit)

private theorem twoSheetMap_equifibered : NatTrans.Equifibered twoSheetMap := by
  intro i j α
  change IsPullback (𝟙 (Fin 2)) _ _ (𝟙 PUnit)
  exact IsPullback.of_horiz_isIso ⟨rfl⟩

private theorem twoSheetMap_finite (g : point _⦋0⦌) :
    Finite {f : twoSheets _⦋0⦌ // twoSheetMap.app _ f = g} := by
  change Finite {f : Fin 2 // _}
  infer_instance

private theorem twoSheets_distinct : (0 : Fin 2) ≠ 1 := by decide

private abbrev integralModule : ModuleCat ℤ := ModuleCat.of ℤ ℤ

private noncomputable def twoSheetTransfer :
    point.chainComplex integralModule ⟶ twoSheets.chainComplex integralModule :=
  SSet.chainComplexTransfer twoSheetMap twoSheetMap_equifibered twoSheetMap_finite integralModule

private def twoSheetFiberEquiv :
    {f : twoSheets _⦋0⦌ // twoSheetMap.app _ f = PUnit.unit} ≃ Fin 2 where
  toFun := Subtype.val
  invFun i := ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Both distinct coprojections occur in the image under the constructed transfer. -/
private theorem twoSheetTransfer_generator :
    point.ιChainComplex PUnit.unit ≫ twoSheetTransfer.f 0 =
      twoSheets.ιChainComplex (0 : Fin 2) + twoSheets.ιChainComplex (1 : Fin 2) := by
  rw [twoSheetTransfer, SSet.ι_chainComplexTransfer_f]
  calc
    _ = ∑ᶠ i : Fin 2, twoSheets.ιChainComplex i :=
      finsum_eq_of_bijective twoSheetFiberEquiv twoSheetFiberEquiv.bijective (fun _ ↦ rfl)
    _ = _ := by rw [finsum_eq_sum_of_fintype, Fin.sum_univ_two]

/-- Coordinates are coproduct eliminators; no identification of a coproduct with pairs
is presumed. -/
private noncomputable def coordinate (i : Fin 2) :
    (twoSheets.chainComplex integralModule).X 0 ⟶ integralModule :=
  Sigma.desc fun j : Fin 2 ↦ if j = i then 𝟙 _ else 0

private theorem twoSheetTransfer_coordinate (i : Fin 2) :
    point.ιChainComplex PUnit.unit ≫ twoSheetTransfer.f 0 ≫ coordinate i =
      𝟙 integralModule := by
  rw [← Category.assoc, twoSheetTransfer_generator, Preadditive.add_comp]
  fin_cases i <;> simp [coordinate, SSet.ιChainComplex, Cofan.mk_ι_app]

/-- Each of the two coordinates of the transferred integral generator is one. -/
private theorem twoSheetTransfer_coordinate_one (i : Fin 2) :
    (coordinate i) (twoSheetTransfer.f 0
      (point.ιChainComplex (R := integralModule) (n := 0) PUnit.unit (1 : ℤ))) = 1 := by
  have h := congrArg (fun k : integralModule ⟶ integralModule ↦ k (1 : ℤ))
    (twoSheetTransfer_coordinate i)
  exact h

private noncomputable def foldPoint :
    (point.chainComplex integralModule).X 0 ⟶ integralModule :=
  Sigma.desc fun _ : PUnit ↦ 𝟙 _

private theorem twoSheetTransfer_push_generator :
    point.ιChainComplex PUnit.unit ≫ twoSheetTransfer.f 0 ≫
        (SSet.chainComplexMap twoSheetMap integralModule).f 0 =
      (2 : ℕ) • point.ιChainComplex PUnit.unit := by
  rw [← Category.assoc, twoSheetTransfer_generator, Preadditive.add_comp]
  simp [SSet.ι_chainComplexMap_f, twoSheetMap, twoSheets, point, two_nsmul]

/-- Pushing the transferred one gives the integer two, which is nonzero. -/
private theorem twoSheetTransfer_push_one :
    foldPoint ((SSet.chainComplexMap twoSheetMap integralModule).f 0
      (twoSheetTransfer.f 0
        (point.ιChainComplex (R := integralModule) (n := 0) PUnit.unit (1 : ℤ)))) = 2 ∧
        (2 : ℤ) ≠ 0 := by
  constructor
  · have h := congrArg (fun k : integralModule ⟶ integralModule ↦ k (1 : ℤ))
      (congrArg (fun k ↦ k ≫ foldPoint) twoSheetTransfer_push_generator)
    simpa [foldPoint, SSet.ιChainComplex, Preadditive.nsmul_comp, Cofan.mk_ι_app] using h
  · decide

private theorem twoSheetMap_card (g : point _⦋0⦌) :
    Nat.card {f : twoSheets _⦋0⦌ // twoSheetMap.app _ f = g} = 2 := by
  cases g
  exact (Nat.card_congr twoSheetFiberEquiv).trans (Nat.card_fin 2)

private theorem twoSheetTransfer_fixed_sheets :
    twoSheetTransfer ≫ SSet.chainComplexMap twoSheetMap integralModule =
      (2 : ℕ) • 𝟙 (point.chainComplex integralModule) :=
  SSet.chainComplexTransfer_comp_map twoSheetMap twoSheetMap_equifibered
    twoSheetMap_finite integralModule 2 twoSheetMap_card

private theorem twoSheetHomologyTransfer_fixed_sheets :
    SSet.homologyTransfer twoSheetMap twoSheetMap_equifibered
        twoSheetMap_finite integralModule 0 ≫ SSet.homologyMap twoSheetMap integralModule 0 =
      (2 : ℕ) • 𝟙 (point.homology integralModule 0) :=
  SSet.homologyTransfer_comp_map twoSheetMap twoSheetMap_equifibered
    twoSheetMap_finite integralModule 2 0 twoSheetMap_card

private abbrev emptySheets : SSet.{0} := (Functor.const _).obj Empty
private def emptySheetMap : emptySheets ⟶ point :=
  (Functor.const _).map (↾Empty.elim)

private theorem emptySheetMap_equifibered : NatTrans.Equifibered emptySheetMap := by
  intro i j α
  change IsPullback (𝟙 Empty) _ _ (𝟙 PUnit)
  exact IsPullback.of_horiz_isIso ⟨rfl⟩

private theorem emptySheetMap_finite (g : point _⦋0⦌) :
    Finite {f : emptySheets _⦋0⦌ // emptySheetMap.app _ f = g} := by
  change Finite {f : Empty // _}
  infer_instance

private theorem emptySheetTransfer_zero :
    SSet.chainComplexTransfer emptySheetMap emptySheetMap_equifibered
      emptySheetMap_finite integralModule = 0 := by
  ext n : 1
  apply SSet.chainComplex_hom_ext
  intro g
  rw [SSet.ι_chainComplexTransfer_f]
  let _ : IsEmpty {f : emptySheets _⦋n⦌ // emptySheetMap.app _ f = g} :=
    ⟨fun f ↦ Empty.elim f.val⟩
  simpa using finsum_of_isEmpty
    (fun f : {f : emptySheets _⦋n⦌ // emptySheetMap.app _ f = g} ↦
      emptySheets.ιChainComplex (R := integralModule) f.val)

private theorem emptySheetTransfer_comp_map :
    SSet.chainComplexTransfer emptySheetMap emptySheetMap_equifibered
        emptySheetMap_finite integralModule ≫ SSet.chainComplexMap emptySheetMap integralModule =
      (0 : ℕ) • 𝟙 (point.chainComplex integralModule) := by
  rw [emptySheetTransfer_zero]
  simp

private abbrev zeroModule : ModuleCat ℤ := ModuleCat.of ℤ (Fin 0 → ℤ)

private theorem zeroCoefficientTransfer_zero :
    SSet.chainComplexTransfer twoSheetMap twoSheetMap_equifibered
      twoSheetMap_finite zeroModule = 0 := by
  ext n : 1
  apply SSet.chainComplex_hom_ext
  intro g
  have h (k : twoSheets _⦋n⦌) :
      twoSheets.ιChainComplex (R := zeroModule) k = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  rw [SSet.ι_chainComplexTransfer_f]
  simp [h]

private theorem zeroCoefficientTransfer_comp_map :
    SSet.chainComplexTransfer twoSheetMap twoSheetMap_equifibered
        twoSheetMap_finite zeroModule ≫ SSet.chainComplexMap twoSheetMap zeroModule = 0 := by
  rw [zeroCoefficientTransfer_zero, zero_comp]

private abbrev threeSheets : SSet.{0} := (Functor.const _).obj (Fin 3)
private abbrev sixSheets : SSet.{0} := (Functor.const _).obj (Fin 2 × Fin 3)

private def projectionMap : sixSheets ⟶ threeSheets :=
  (Functor.const _).map (↾Prod.snd)

private def threeSheetMap : threeSheets ⟶ point :=
  (Functor.const _).map (↾fun _ : Fin 3 ↦ PUnit.unit)

private theorem projectionMap_equifibered : NatTrans.Equifibered projectionMap := by
  intro i j α
  change IsPullback (𝟙 (Fin 2 × Fin 3)) _ _ (𝟙 (Fin 3))
  exact IsPullback.of_horiz_isIso ⟨rfl⟩

private theorem threeSheetMap_equifibered : NatTrans.Equifibered threeSheetMap := by
  intro i j α
  change IsPullback (𝟙 (Fin 3)) _ _ (𝟙 PUnit)
  exact IsPullback.of_horiz_isIso ⟨rfl⟩

private theorem projectionMap_finite (g : threeSheets _⦋0⦌) :
    Finite {f : sixSheets _⦋0⦌ // projectionMap.app _ f = g} := by
  change Finite {f : Fin 2 × Fin 3 // _}
  infer_instance

private theorem threeSheetMap_finite (g : point _⦋0⦌) :
    Finite {f : threeSheets _⦋0⦌ // threeSheetMap.app _ f = g} := by
  change Finite {f : Fin 3 // _}
  infer_instance

private noncomputable def projectionTransfer :
    threeSheets.chainComplex integralModule ⟶ sixSheets.chainComplex integralModule :=
  SSet.chainComplexTransfer projectionMap projectionMap_equifibered
    projectionMap_finite integralModule

private noncomputable def threeSheetTransfer :
    point.chainComplex integralModule ⟶ threeSheets.chainComplex integralModule :=
  SSet.chainComplexTransfer threeSheetMap threeSheetMap_equifibered
    threeSheetMap_finite integralModule

private def projectionFiberEquiv (j : Fin 3) :
    {f : sixSheets _⦋0⦌ // projectionMap.app _ f = j} ≃ Fin 2 where
  toFun f := f.val.1
  invFun i := ⟨(i, j), rfl⟩
  left_inv := by rintro ⟨⟨i, j'⟩, h⟩; cases h; rfl
  right_inv _ := rfl

private def threeSheetFiberEquiv :
    {f : threeSheets _⦋0⦌ // threeSheetMap.app _ f = PUnit.unit} ≃ Fin 3 where
  toFun := Subtype.val
  invFun j := ⟨j, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem projectionTransfer_generator (j : Fin 3) :
    threeSheets.ιChainComplex j ≫ projectionTransfer.f 0 =
      ∑ i : Fin 2, sixSheets.ιChainComplex (i, j) := by
  rw [projectionTransfer, SSet.ι_chainComplexTransfer_f]
  calc
    _ = ∑ᶠ i : Fin 2, sixSheets.ιChainComplex (i, j) :=
      finsum_eq_of_bijective (projectionFiberEquiv j) (projectionFiberEquiv j).bijective
        (fun f ↦ by congr 1; exact Prod.ext rfl f.property)
    _ = _ := finsum_eq_sum_of_fintype _

private theorem threeSheetTransfer_generator :
    point.ιChainComplex PUnit.unit ≫ threeSheetTransfer.f 0 =
      ∑ j : Fin 3, threeSheets.ιChainComplex j := by
  rw [threeSheetTransfer, SSet.ι_chainComplexTransfer_f]
  calc
    _ = ∑ᶠ j : Fin 3, threeSheets.ιChainComplex j :=
      finsum_eq_of_bijective threeSheetFiberEquiv threeSheetFiberEquiv.bijective (fun _ ↦ rfl)
    _ = _ := finsum_eq_sum_of_fintype _

private noncomputable def sixCoordinate (k : Fin 2 × Fin 3) :
    (sixSheets.chainComplex integralModule).X 0 ⟶ integralModule :=
  Sigma.desc fun l : Fin 2 × Fin 3 ↦ if l = k then 𝟙 _ else 0

/-- Each coordinate is computed from the two separate generator equations. -/
private theorem twoStepTransfer_coordinate (k : Fin 2 × Fin 3) :
    point.ιChainComplex PUnit.unit ≫ (threeSheetTransfer ≫ projectionTransfer).f 0 ≫
        sixCoordinate k = 𝟙 integralModule := by
  calc
    _ = (∑ j : Fin 3, ∑ i : Fin 2, sixSheets.ιChainComplex (i, j)) ≫ sixCoordinate k := by
      rw [HomologicalComplex.comp_f, ← Category.assoc, ← Category.assoc,
        threeSheetTransfer_generator, Preadditive.sum_comp]
      simp_rw [projectionTransfer_generator]
    _ = _ := by
      rcases k with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;>
        simp [sixCoordinate, SSet.ιChainComplex, Cofan.mk_ι_app, Fin.sum_univ_succ]

/-- All six coordinates of the two-step transfer of the integral generator are one. -/
private theorem twoStepTransfer_coordinate_one (k : Fin 2 × Fin 3) :
    (sixCoordinate k) ((threeSheetTransfer ≫ projectionTransfer).f 0
      (point.ιChainComplex (R := integralModule) (n := 0) PUnit.unit (1 : ℤ))) = 1 := by
  exact congrArg (fun f : integralModule ⟶ integralModule ↦ f (1 : ℤ))
    (twoStepTransfer_coordinate k)

private theorem integralCoproductTransfer_id :
    sigmaConstTransfer (𝟙 (Fin 2 × Fin 3)) (fun _ ↦ inferInstance) integralModule = 𝟙 _ :=
  sigmaConstTransfer_id _ _

private theorem integralCoproductTransfer_comp :
    sigmaConstTransfer (projectionMap.app (op ⦋0⦌) ≫ threeSheetMap.app (op ⦋0⦌))
        (Types.finite_fiber_comp (projectionMap.app (op ⦋0⦌)) (threeSheetMap.app (op ⦋0⦌))
          projectionMap_finite threeSheetMap_finite) integralModule =
      sigmaConstTransfer (threeSheetMap.app (op ⦋0⦌)) threeSheetMap_finite integralModule ≫
        sigmaConstTransfer (projectionMap.app (op ⦋0⦌)) projectionMap_finite integralModule :=
  sigmaConstTransfer_comp _ _ _ _ _

private theorem integralDiagramTransfer_comp :
    equifiberedSigmaTransfer (projectionMap ≫ threeSheetMap)
        (projectionMap_equifibered.comp threeSheetMap_equifibered)
        (fun j ↦ Types.finite_fiber_comp (projectionMap.app j) (threeSheetMap.app j)
          (SSet.finite_fiber_of_finite_vertices projectionMap projectionMap_equifibered
            projectionMap_finite j)
          (SSet.finite_fiber_of_finite_vertices threeSheetMap threeSheetMap_equifibered
            threeSheetMap_finite j)) integralModule =
      equifiberedSigmaTransfer threeSheetMap threeSheetMap_equifibered
          (SSet.finite_fiber_of_finite_vertices threeSheetMap threeSheetMap_equifibered
            threeSheetMap_finite) integralModule ≫
        equifiberedSigmaTransfer projectionMap projectionMap_equifibered
          (SSet.finite_fiber_of_finite_vertices projectionMap projectionMap_equifibered
            projectionMap_finite) integralModule :=
  equifiberedSigmaTransfer_comp _ _ _ _ _ _ _

private theorem integralChainTransfer_comp :
    SSet.chainComplexTransfer (projectionMap ≫ threeSheetMap)
        (projectionMap_equifibered.comp threeSheetMap_equifibered)
        (Types.finite_fiber_comp (projectionMap.app (op ⦋0⦌)) (threeSheetMap.app (op ⦋0⦌))
          projectionMap_finite threeSheetMap_finite) integralModule =
      threeSheetTransfer ≫ projectionTransfer :=
  SSet.chainComplexTransfer_comp _ _ _ _ _ _ _

private theorem integralHomologyTransfer_comp :
    SSet.homologyTransfer (projectionMap ≫ threeSheetMap)
        (projectionMap_equifibered.comp threeSheetMap_equifibered)
        (Types.finite_fiber_comp (projectionMap.app (op ⦋0⦌)) (threeSheetMap.app (op ⦋0⦌))
          projectionMap_finite threeSheetMap_finite) integralModule 0 =
      SSet.homologyTransfer threeSheetMap threeSheetMap_equifibered
          threeSheetMap_finite integralModule 0 ≫
        SSet.homologyTransfer projectionMap projectionMap_equifibered
          projectionMap_finite integralModule 0 :=
  SSet.homologyTransfer_comp _ _ _ _ _ _ _ _

universe u

/-- The coefficient's carrier and hom universes need not equal the simplex universe. -/
private noncomputable def liftedIntegralTransfer :
    point.chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ)) ⟶
      twoSheets.chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ)) :=
  SSet.chainComplexTransfer twoSheetMap twoSheetMap_equifibered twoSheetMap_finite _

private theorem liftedIntegralTransfer_generator :
    point.ιChainComplex PUnit.unit ≫ liftedIntegralTransfer.{u}.f 0 =
      twoSheets.ιChainComplex (0 : Fin 2) + twoSheets.ιChainComplex (1 : Fin 2) := by
  rw [liftedIntegralTransfer, SSet.ι_chainComplexTransfer_f]
  calc
    _ = ∑ᶠ i : Fin 2, twoSheets.ιChainComplex i :=
      finsum_eq_of_bijective twoSheetFiberEquiv twoSheetFiberEquiv.bijective (fun _ ↦ rfl)
    _ = _ := by rw [finsum_eq_sum_of_fintype, Fin.sum_univ_two]

end SimplicialObjectsTest.FiniteFiberTransfer
