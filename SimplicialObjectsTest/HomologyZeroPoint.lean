/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Module.ULift
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
import Mathlib.Data.ZMod.Basic
import SimplicialObjects.HomologyZero

/-!
# A point class and reduction modulo two

The integer vertex class in the simplicial homology of the standard point is
nonzero, detected by the existing augmentation. The same coefficient reduction
modulo two kills the lifted integer two and preserves the lifted integer one.

The forward comparison is evaluated on the integer vertex class. The inverse
comparison is evaluated on the corresponding coefficient-one component generator.
Both use the same reduction map as the scalar calculations.

## References

* Mathlib's simplicial vertex-class and augmentation API, by Joël Riou and
  Andrew Yang, supplies the homology class and its detector.
* Mathlib supplies the category of integer modules, lifted module equivalences,
  integer reduction and categorical coproducts.
-/

open CategoryTheory Limits
open scoped Simplicial

namespace SSet

private abbrev homologyPoint : SSet.{0} := Δ[0]

private abbrev pointIntegerCoefficients : ModuleCat.{0} ℤ :=
  ModuleCat.of ℤ (ULift.{0} ℤ)

private abbrev pointModTwoCoefficients : ModuleCat.{0} ℤ :=
  ModuleCat.of ℤ (ULift.{0} (ZMod 2))

private def homologyPointVertex : homologyPoint _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)

/-- The integer coefficient-one vertex class of the standard simplicial point. -/
private noncomputable def pointIntegerClass :
    homologyPoint.homology (C := ModuleCat.{0} ℤ) pointIntegerCoefficients 0 :=
  ((homologyPoint.chainComplex pointIntegerCoefficients).liftCycles
      (k := homologyPoint.ιChainComplex homologyPointVertex) 0 (by simp) (by simp) ≫
    (homologyPoint.chainComplex pointIntegerCoefficients).homologyπ 0)
      (ULift.up (1 : ℤ))

private theorem pointIntegerClass_augmentation :
    homologyPoint.homology₀ε pointIntegerCoefficients pointIntegerClass =
      (ULift.up (1 : ℤ) : ULift.{0} ℤ) := by
  have h := congrArg
    (fun f : pointIntegerCoefficients ⟶ pointIntegerCoefficients =>
      f (ULift.up (1 : ℤ)))
    (SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
      homologyPoint pointIntegerCoefficients homologyPointVertex)
  simpa only [pointIntegerClass, CategoryTheory.ConcreteCategory.comp_apply,
    CategoryTheory.ConcreteCategory.id_apply] using h

private theorem pointIntegerClass_ne_zero : pointIntegerClass ≠ 0 := by
  intro h
  have hScalar := pointIntegerClass_augmentation
  rw [h, map_zero] at hScalar
  have hInt := congrArg (fun z : ULift.{0} ℤ => z.down) hScalar
  simp at hInt

/-- Integer reduction modulo two, conjugated by the lifted module equivalences. -/
private def pointCoefficientReduction :
    pointIntegerCoefficients ⟶ pointModTwoCoefficients :=
  ModuleCat.ofHom
    ((ULift.moduleEquiv (R := ℤ) : ULift.{0} (ZMod 2) ≃ₗ[ℤ] ZMod 2).symm.toLinearMap ∘ₗ
      (Int.castAddHom (ZMod 2)).toIntLinearMap ∘ₗ
      (ULift.moduleEquiv (R := ℤ) : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toLinearMap)

private theorem pointCoefficientReduction_two :
    pointCoefficientReduction (ULift.up (2 : ℤ)) = 0 := by
  change (ULift.up (((2 : ℤ) : ZMod 2)) : ULift.{0} (ZMod 2)) = 0
  decide

private theorem pointCoefficientReduction_one :
    pointCoefficientReduction (ULift.up (1 : ℤ)) =
      (ULift.up (1 : ZMod 2) : ULift.{0} (ZMod 2)) := by
  change (ULift.up (((1 : ℤ) : ZMod 2)) : ULift.{0} (ZMod 2)) = ULift.up (1 : ZMod 2)
  rw [Int.cast_one]

/-- Reduction commutes with the forward comparison on the integer vertex class. -/
private theorem pointIntegerClass_reduction_naturality :
    (homologyPoint.homology₀Iso pointModTwoCoefficients).hom
        ((HomologicalComplex.homologyMap
          (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map pointCoefficientReduction).app
            homologyPoint) 0) pointIntegerClass) =
      (CategoryTheory.Limits.Sigma.map
        (fun _ : SSet.π₀ homologyPoint => pointCoefficientReduction))
        ((homologyPoint.homology₀Iso pointIntegerCoefficients).hom pointIntegerClass) := by
  have h := congrArg
    (fun f : homologyPoint.homology (C := ModuleCat.{0} ℤ) pointIntegerCoefficients 0 ⟶
        ∐ (fun _ : SSet.π₀ homologyPoint => pointModTwoCoefficients) =>
      f pointIntegerClass)
    (SSet.homology₀Iso_hom_coefficient_naturality homologyPoint
      pointIntegerCoefficients pointModTwoCoefficients pointCoefficientReduction)
  simpa only [CategoryTheory.ConcreteCategory.comp_apply] using h

/-- Reduction commutes with the inverse comparison on the coefficient-one component generator. -/
private theorem pointComponentGenerator_inverse_reduction_naturality :
    (homologyPoint.homology₀Iso pointModTwoCoefficients).inv
        ((CategoryTheory.Limits.Sigma.map
          (fun _ : SSet.π₀ homologyPoint => pointCoefficientReduction))
          (SSet.π₀.fromChainComplexXZero homologyPoint pointIntegerCoefficients
            (homologyPoint.ιChainComplex (C := ModuleCat.{0} ℤ) (R := pointIntegerCoefficients)
              homologyPointVertex (ULift.up (1 : ℤ))))) =
      (HomologicalComplex.homologyMap
        (((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map pointCoefficientReduction).app
          homologyPoint) 0)
        ((homologyPoint.homology₀Iso pointIntegerCoefficients).inv
          (SSet.π₀.fromChainComplexXZero homologyPoint pointIntegerCoefficients
            (homologyPoint.ιChainComplex (C := ModuleCat.{0} ℤ) (R := pointIntegerCoefficients)
              homologyPointVertex (ULift.up (1 : ℤ))))) := by
  have h := congrArg
    (fun f : (∐ (fun _ : SSet.π₀ homologyPoint => pointIntegerCoefficients)) ⟶
        homologyPoint.homology (C := ModuleCat.{0} ℤ) pointModTwoCoefficients 0 =>
      f (SSet.π₀.fromChainComplexXZero homologyPoint pointIntegerCoefficients
        (homologyPoint.ιChainComplex (C := ModuleCat.{0} ℤ) (R := pointIntegerCoefficients)
          homologyPointVertex (ULift.up (1 : ℤ)))))
    (SSet.homology₀Iso_inv_coefficient_naturality homologyPoint
      pointIntegerCoefficients pointModTwoCoefficients pointCoefficientReduction)
  simpa only [CategoryTheory.ConcreteCategory.comp_apply] using h

end SSet
