/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.SingularHomologyZero
public import SimplicialObjects.TensorHomologyZeroCoefficientMaps

/-!
# Coefficient naturality of singular normalized tensor homology in degree zero

The path-component description of degree-zero normalized tensor homology commutes
with additive coefficient homomorphisms, and simultaneously with continuous maps
of spaces. The coefficient universes are independent: source padding `max b p`
and target padding `max a p` place both sides in the same module category without
changing either lifted coefficient object.

The forward squares combine the simplicial coefficient and mixed naturality
squares with coproduct reindexing along the singular-component equivalence. The
map on topological path components is the direct quotient map
`ZerothHomotopy.map`. The inverse squares follow by isomorphism cancellation.

## References and attribution

Mathlib's coproduct functors and its Dold–Kan and degree-zero homology
constructions, notably by Joël Riou, underlie these comparisons. The integral
normalized tensor comparison and its coefficient and mixed naturality squares
are supplied by the prior formalizations in `SimplicialObjects.TensorHomologyZero`
and `SimplicialObjects.TensorHomologyZeroCoefficientMaps`.
-/

@[expose] public section

universe a b w p

open CategoryTheory Limits
open scoped Simplicial TensorProduct

namespace TopCat

/-- The forward path-component isomorphism commutes with an additive coefficient
homomorphism, with balanced independent coefficient universes. -/
theorem tensorNormalizedHomologyZeroIsoPathComponents_hom_coefficient_naturality
    (A : Type a) (B : Type b) [AddCommGroup A] [AddCommGroup B]
    (X : TopCat.{w}) (g : A →+ B) :
    let S := TopCat.toSSet.obj X
    let RA := ModuleCat.of ℤ (ULift.{max w b p} A)
    let RB := ModuleCat.of ℤ (ULift.{max w a p} B)
    let eA := tensorNormalizedHomologyZeroIsoPathComponents.{a, w, max b p} A X
    let eB := tensorNormalizedHomologyZeroIsoPathComponents.{b, w, max a p} B X
    let k : RA ⟶ RB := ModuleCat.ofHom
      ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
        g.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap)
    let q := Sigma.map' (f := fun _ : ZerothHomotopy X => RA)
      (g := fun _ : ZerothHomotopy X => RB) id (fun _ => k)
    let h := HomologicalComplex.homologyMap
      (SSet.tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S) 0
    h ≫ eB.hom = eA.hom ≫ q := by
  dsimp only
  let RA := ModuleCat.of ℤ (ULift.{max w b p} A)
  let RB := ModuleCat.of ℤ (ULift.{max w a p} B)
  let k : RA ⟶ RB := ModuleCat.ofHom
    ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
      g.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap)
  rw [tensorNormalizedHomologyZeroIsoPathComponents_hom,
    tensorNormalizedHomologyZeroIsoPathComponents_hom]
  calc
    _ = (SSet.tensorNormalizedHomologyZeroIsoComponents.{a, w, max b p} A
          (TopCat.toSSet.obj X)).hom ≫
        (CategoryTheory.Limits.Sigma.map (f := fun _ : (TopCat.toSSet.obj X).π₀ => RA)
          (g := fun _ : (TopCat.toSSet.obj X).π₀ => RB) (fun _ => k) ≫
          (sigmaConst.{w}.obj RB).map (TopCat.zerothHomotopyEquiv (X := X)).toIso.inv) := by
      simpa only [Category.assoc] using
        congrArg
          (fun t => t ≫ (sigmaConst.{w}.obj RB).map
            (TopCat.zerothHomotopyEquiv (X := X)).toIso.inv)
          (SSet.tensorNormalizedHomologyZeroIsoComponents_hom_coefficient_naturality.{a, b, w, p}
            g (TopCat.toSSet.obj X))
    _ = _ := by
      simpa only [Category.assoc, Sigma.map'_id,
        CategoryTheory.Limits.sigmaConst_map_app, RA, RB, k] using
        congrArg
          (fun t =>
            (SSet.tensorNormalizedHomologyZeroIsoComponents.{a, w, max b p} A
              (TopCat.toSSet.obj X)).hom ≫ t)
          ((sigmaConst.{w}.map k).naturality
            (TopCat.zerothHomotopyEquiv (X := X)).toIso.inv).symm

/-- The inverse path-component isomorphism commutes with the same balanced
coefficient map; no inverse naturality assumption is needed. -/
theorem tensorNormalizedHomologyZeroIsoPathComponents_inv_coefficient_naturality
    (A : Type a) (B : Type b) [AddCommGroup A] [AddCommGroup B]
    (X : TopCat.{w}) (g : A →+ B) :
    let S := TopCat.toSSet.obj X
    let RA := ModuleCat.of ℤ (ULift.{max w b p} A)
    let RB := ModuleCat.of ℤ (ULift.{max w a p} B)
    let eA := tensorNormalizedHomologyZeroIsoPathComponents.{a, w, max b p} A X
    let eB := tensorNormalizedHomologyZeroIsoPathComponents.{b, w, max a p} B X
    let k : RA ⟶ RB := ModuleCat.ofHom
      ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
        g.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap)
    let q := Sigma.map' (f := fun _ : ZerothHomotopy X => RA)
      (g := fun _ : ZerothHomotopy X => RB) id (fun _ => k)
    let h := HomologicalComplex.homologyMap
      (SSet.tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S) 0
    eA.inv ≫ h = q ≫ eB.inv := by
  dsimp only
  apply (cancel_mono
    (tensorNormalizedHomologyZeroIsoPathComponents.{b, w, max a p} B X).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using
    congrArg
      (fun t =>
        (tensorNormalizedHomologyZeroIsoPathComponents.{a, w, max b p} A X).inv ≫ t)
      (tensorNormalizedHomologyZeroIsoPathComponents_hom_coefficient_naturality.{a, b, w, p}
        A B X g)

/-- Simultaneous forward naturality for a continuous map and an additive
coefficient homomorphism. The homology map first changes the space and then
changes coefficients at the target space. -/
theorem tensorNormalizedHomologyZeroIsoPathComponents_hom_mixed_naturality
    (A : Type a) (B : Type b) [AddCommGroup A] [AddCommGroup B]
    (X Y : TopCat.{w}) (f : C(X, Y)) (g : A →+ B) :
    let S := TopCat.toSSet.obj X
    let T := TopCat.toSSet.obj Y
    let RA := ModuleCat.of ℤ (ULift.{max w b p} A)
    let RB := ModuleCat.of ℤ (ULift.{max w a p} B)
    let eX := tensorNormalizedHomologyZeroIsoPathComponents.{a, w, max b p} A X
    let eY := tensorNormalizedHomologyZeroIsoPathComponents.{b, w, max a p} B Y
    let k : RA ⟶ RB := ModuleCat.ofHom
      ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
        g.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap)
    let q := Sigma.map' (f := fun _ : ZerothHomotopy X => RA)
      (g := fun _ : ZerothHomotopy Y => RB)
      (ZerothHomotopy.map f) (fun _ => k)
    let h := HomologicalComplex.homologyMap
        (SSet.tensorNormalizedChainComplexMap.{a, w, max b p} A
          (TopCat.toSSet.map (TopCat.ofHom f))) 0 ≫
      HomologicalComplex.homologyMap
        (SSet.tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g T) 0
    h ≫ eY.hom = eX.hom ≫ q := by
  dsimp only
  let RA := ModuleCat.of ℤ (ULift.{max w b p} A)
  let RB := ModuleCat.of ℤ (ULift.{max w a p} B)
  let k : RA ⟶ RB := ModuleCat.ofHom
    ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
      g.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap)
  have hi :
      (fun z : (TopCat.toSSet.obj X).π₀ =>
        (TopCat.zerothHomotopyEquiv (X := Y)).symm
          (SSet.mapπ₀ (TopCat.toSSet.map (TopCat.ofHom f)) z)) =
      (fun z : (TopCat.toSSet.obj X).π₀ =>
        ZerothHomotopy.map f ((TopCat.zerothHomotopyEquiv (X := X)).symm z)) := by
    funext z
    exact (TopCat.zerothHomotopyEquiv_symm_naturality f z).symm
  have ht :
      Sigma.map' (f := fun _ : (TopCat.toSSet.obj X).π₀ => RA)
          (g := fun _ : (TopCat.toSSet.obj Y).π₀ => RB)
          (SSet.mapπ₀ (TopCat.toSSet.map (TopCat.ofHom f))) (fun _ => k) ≫
        (sigmaConst.{w}.obj RB).map (TopCat.zerothHomotopyEquiv (X := Y)).toIso.inv =
      (sigmaConst.{w}.obj RA).map (TopCat.zerothHomotopyEquiv (X := X)).toIso.inv ≫
        Sigma.map' (f := fun _ : ZerothHomotopy X => RA)
          (g := fun _ : ZerothHomotopy Y => RB) (ZerothHomotopy.map f) (fun _ => k) := by
    change
      Sigma.map' (f := fun _ : (TopCat.toSSet.obj X).π₀ => RA)
          (g := fun _ : (TopCat.toSSet.obj Y).π₀ => RB)
          (SSet.mapπ₀ (TopCat.toSSet.map (TopCat.ofHom f))) (fun _ => k) ≫
        Sigma.map' (f := fun _ : (TopCat.toSSet.obj Y).π₀ => RB)
          (g := fun _ : ZerothHomotopy Y => RB)
          (TopCat.zerothHomotopyEquiv (X := Y)).symm (fun _ => 𝟙 RB) =
      Sigma.map' (f := fun _ : (TopCat.toSSet.obj X).π₀ => RA)
          (g := fun _ : ZerothHomotopy X => RA)
          (TopCat.zerothHomotopyEquiv (X := X)).symm (fun _ => 𝟙 RA) ≫
        Sigma.map' (f := fun _ : ZerothHomotopy X => RA)
          (g := fun _ : ZerothHomotopy Y => RB) (ZerothHomotopy.map f) (fun _ => k)
    rw [Sigma.map'_comp_map', Sigma.map'_comp_map']
    simp only [Category.comp_id, Category.id_comp]
    exact congrArg
      (fun t => Sigma.map' (f := fun _ : (TopCat.toSSet.obj X).π₀ => RA)
        (g := fun _ : ZerothHomotopy Y => RB) t (fun _ => k)) hi
  rw [tensorNormalizedHomologyZeroIsoPathComponents_hom,
    tensorNormalizedHomologyZeroIsoPathComponents_hom]
  calc
    _ = (SSet.tensorNormalizedHomologyZeroIsoComponents.{a, w, max b p} A
          (TopCat.toSSet.obj X)).hom ≫
        (Sigma.map' (f := fun _ : (TopCat.toSSet.obj X).π₀ => RA)
          (g := fun _ : (TopCat.toSSet.obj Y).π₀ => RB)
          (SSet.mapπ₀ (TopCat.toSSet.map (TopCat.ofHom f))) (fun _ => k) ≫
          (sigmaConst.{w}.obj RB).map (TopCat.zerothHomotopyEquiv (X := Y)).toIso.inv) := by
      simpa only [Category.assoc] using
        congrArg
          (fun t => t ≫ (sigmaConst.{w}.obj RB).map
            (TopCat.zerothHomotopyEquiv (X := Y)).toIso.inv)
          (SSet.tensorNormalizedHomologyZeroIsoComponents_hom_mixed_naturality.{a, b, w, p}
            (TopCat.toSSet.map (TopCat.ofHom f)) g)
    _ = _ := by
      rw [ht]
      simp only [RA, RB, k, Category.assoc]

/-- Simultaneous inverse naturality for the same space-then-coefficient map and
the direct map on topological path components. -/
theorem tensorNormalizedHomologyZeroIsoPathComponents_inv_mixed_naturality
    (A : Type a) (B : Type b) [AddCommGroup A] [AddCommGroup B]
    (X Y : TopCat.{w}) (f : C(X, Y)) (g : A →+ B) :
    let S := TopCat.toSSet.obj X
    let T := TopCat.toSSet.obj Y
    let RA := ModuleCat.of ℤ (ULift.{max w b p} A)
    let RB := ModuleCat.of ℤ (ULift.{max w a p} B)
    let eX := tensorNormalizedHomologyZeroIsoPathComponents.{a, w, max b p} A X
    let eY := tensorNormalizedHomologyZeroIsoPathComponents.{b, w, max a p} B Y
    let k : RA ⟶ RB := ModuleCat.ofHom
      ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
        g.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap)
    let q := Sigma.map' (f := fun _ : ZerothHomotopy X => RA)
      (g := fun _ : ZerothHomotopy Y => RB)
      (ZerothHomotopy.map f) (fun _ => k)
    let h := HomologicalComplex.homologyMap
        (SSet.tensorNormalizedChainComplexMap.{a, w, max b p} A
          (TopCat.toSSet.map (TopCat.ofHom f))) 0 ≫
      HomologicalComplex.homologyMap
        (SSet.tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g T) 0
    eX.inv ≫ h = q ≫ eY.inv := by
  dsimp only
  apply (cancel_mono
    (tensorNormalizedHomologyZeroIsoPathComponents.{b, w, max a p} B Y).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using
    congrArg
      (fun t =>
        (tensorNormalizedHomologyZeroIsoPathComponents.{a, w, max b p} A X).inv ≫ t)
      (tensorNormalizedHomologyZeroIsoPathComponents_hom_mixed_naturality.{a, b, w, p}
        A B X Y f g)

end TopCat
