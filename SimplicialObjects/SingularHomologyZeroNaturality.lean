/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.SingularHomologyZero
public import SimplicialObjects.TensorHomologyZeroNaturality

/-!
# Space naturality of degree-zero singular tensor homology

The component isomorphism for normalized tensor homology of singular simplices
commutes with every continuous map. On the coproduct of lifted coefficients,
the induced map uses the direct map of topological path components and the
identity on each coefficient object. Both the forward and inverse squares are
available without assumptions on the path components or the coefficient group.

## References and attribution

* Mathlib's degree-zero simplicial homology and normalization constructions,
  notably the work of Joël Riou, underlie the component isomorphism.
* `SimplicialObjects.TensorHomologyZeroNaturality` supplies naturality for the
  normalized integral tensor complex under arbitrary simplicial morphisms.
* `SimplicialObjects.PathComponents` supplies the natural comparison between
  singular simplicial components and topological path components. Applying
  Mathlib's coproduct functor `sigmaConst` transports that comparison square.
-/

@[expose] public section

universe a w p

open CategoryTheory Limits
open scoped Simplicial TensorProduct

namespace TopCat

/-- The forward singular tensor homology component isomorphism commutes with
any continuous map, using its direct action on topological path components. -/
theorem tensorNormalizedHomologyZeroIsoPathComponents_hom_naturality
    (A : Type a) [AddCommGroup A] (X Y : TopCat.{w}) (f : C(X, Y)) :
    let R := ModuleCat.of ℤ (ULift.{max w p} A)
    let eX := tensorNormalizedHomologyZeroIsoPathComponents.{a, w, p} A X
    let eY := tensorNormalizedHomologyZeroIsoPathComponents.{a, w, p} A Y
    let q := Sigma.map' (f := fun _ : ZerothHomotopy X => R)
      (g := fun _ : ZerothHomotopy Y => R)
      (ZerothHomotopy.map f) (fun _ => 𝟙 R)
    let h := HomologicalComplex.homologyMap
      (SSet.tensorNormalizedChainComplexMap.{a, w, p} A
        (TopCat.toSSet.map (TopCat.ofHom f))) 0
    h ≫ eY.hom = eX.hom ≫ q := by
  dsimp only
  let R := ModuleCat.of ℤ (ULift.{max w p} A)
  have hi :
      (fun z : (toSSet.obj X).π₀ =>
        (zerothHomotopyEquiv (X := Y)).symm
          (SSet.mapπ₀ (toSSet.map (ofHom f)) z)) =
      (fun z : (toSSet.obj X).π₀ =>
        ZerothHomotopy.map f ((zerothHomotopyEquiv (X := X)).symm z)) := by
    funext z
    exact (zerothHomotopyEquiv_symm_naturality f z).symm
  have hq :
      Sigma.map' (f := fun _ : (toSSet.obj X).π₀ => R)
          (g := fun _ : (toSSet.obj Y).π₀ => R)
          (SSet.mapπ₀ (toSSet.map (ofHom f))) (fun _ => 𝟙 R) ≫
          (sigmaConst.{w}.obj R).map (zerothHomotopyEquiv (X := Y)).toIso.inv =
        (sigmaConst.{w}.obj R).map (zerothHomotopyEquiv (X := X)).toIso.inv ≫
          Sigma.map' (f := fun _ : ZerothHomotopy X => R)
            (g := fun _ : ZerothHomotopy Y => R)
            (ZerothHomotopy.map f) (fun _ => 𝟙 R) := by
    simp only [CategoryTheory.Limits.sigmaConst_obj_map]
    rw [Sigma.map'_comp_map', Sigma.map'_comp_map']
    simp only [Category.id_comp]
    exact congrArg
      (fun t => Sigma.map' (f := fun _ : (toSSet.obj X).π₀ => R)
        (g := fun _ : ZerothHomotopy Y => R) t (fun _ => 𝟙 R)) hi
  calc
    _ = (SSet.tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A
          (toSSet.obj X)).hom ≫
        Sigma.map' (f := fun _ : (toSSet.obj X).π₀ => R)
          (g := fun _ : (toSSet.obj Y).π₀ => R)
          (SSet.mapπ₀ (toSSet.map (ofHom f))) (fun _ => 𝟙 R) ≫
        (sigmaConst.{w}.obj R).map (zerothHomotopyEquiv (X := Y)).toIso.inv := by
      rw [tensorNormalizedHomologyZeroIsoPathComponents_hom]
      simpa only [Category.assoc] using
        congrArg
          (fun k => k ≫
            (sigmaConst.{w}.obj R).map (zerothHomotopyEquiv (X := Y)).toIso.inv)
          (SSet.tensorNormalizedHomologyZeroIsoComponents_hom_naturality.{a, w, p}
            A (toSSet.map (ofHom f)))
    _ = _ := by
      rw [hq, tensorNormalizedHomologyZeroIsoPathComponents_hom]
      simp only [R, Category.assoc]

/-- The inverse singular tensor homology component isomorphism commutes with
any continuous map, with the same direct path-component coproduct map. -/
theorem tensorNormalizedHomologyZeroIsoPathComponents_inv_naturality
    (A : Type a) [AddCommGroup A] (X Y : TopCat.{w}) (f : C(X, Y)) :
    let R := ModuleCat.of ℤ (ULift.{max w p} A)
    let eX := tensorNormalizedHomologyZeroIsoPathComponents.{a, w, p} A X
    let eY := tensorNormalizedHomologyZeroIsoPathComponents.{a, w, p} A Y
    let q := Sigma.map' (f := fun _ : ZerothHomotopy X => R)
      (g := fun _ : ZerothHomotopy Y => R)
      (ZerothHomotopy.map f) (fun _ => 𝟙 R)
    let h := HomologicalComplex.homologyMap
      (SSet.tensorNormalizedChainComplexMap.{a, w, p} A
        (TopCat.toSSet.map (TopCat.ofHom f))) 0
    eX.inv ≫ h = q ≫ eY.inv := by
  dsimp only
  apply (cancel_mono
    (tensorNormalizedHomologyZeroIsoPathComponents.{a, w, p} A Y).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using
    congrArg
      (fun k => (tensorNormalizedHomologyZeroIsoPathComponents.{a, w, p} A X).inv ≫ k)
      (tensorNormalizedHomologyZeroIsoPathComponents_hom_naturality.{a, w, p} A X Y f)

end TopCat
