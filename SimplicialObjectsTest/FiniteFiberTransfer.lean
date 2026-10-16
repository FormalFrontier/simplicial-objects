/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift

/-! Integral constant two-sheet and empty-sheet clients for finite-fiber transfer. -/

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
