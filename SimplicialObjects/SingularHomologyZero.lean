/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.PathComponents
public import SimplicialObjects.TensorHomologyZero

/-!
# Degree-zero normalized tensor homology of singular simplices

For an abelian group `A` and a topological space `X`,
`TopCat.tensorNormalizedHomologyZeroIsoPathComponents` identifies degree-zero
homology of the integral normalized tensor complex of singular simplices with
the coproduct of lifted copies of `A` indexed by the path components of `X`.

The construction composes the simplicial component isomorphism with the stock
comparison between singular simplicial components and topological path
components. Its source is the normalized integral tensor complex, and its
coefficient object is `ModuleCat.of ℤ (ULift.{max w p} A)`, independently of the
outer lift on the tensor chain groups. No nonemptiness or local path
connectedness assumption on the space is needed.

## References and attribution

* Mathlib's Dold–Kan normalization and degree-zero simplicial homology
  constructions, notably by Joël Riou, supply the normalization and component
  isomorphisms. The prior integral normalized tensor formalizations in
  `SimplicialObjects.TensorCoefficients` and `SimplicialObjects.TensorHomologyZero`
  supply the tensor comparison and its vertex formula.
* J. P. May, *A Concise Course in Algebraic Topology*, explains the description
  of degree-zero homology by path components.
-/

@[expose] public section

universe a w p

open CategoryTheory Limits
open scoped Simplicial TensorProduct

namespace TopCat

/-- Degree-zero homology of the normalized integral tensor complex of singular
simplices is the coproduct of lifted coefficients over topological path components. -/
noncomputable def tensorNormalizedHomologyZeroIsoPathComponents
    (A : Type a) [AddCommGroup A] (X : TopCat.{w}) :
    (SSet.tensorNormalizedChainComplex.{a, w, p} A
      (TopCat.toSSet.obj X)).homology 0 ≅
      ∐ (fun _ : ZerothHomotopy X => ModuleCat.of ℤ (ULift.{max w p} A)) :=
  SSet.tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A
      (TopCat.toSSet.obj X) ≪≫
    (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w p} A))).mapIso
      (TopCat.zerothHomotopyEquiv (X := X)).toIso.symm

/-- The forward map first takes simplicial components, then reindexes the
coproduct along the comparison with topological path components. -/
theorem tensorNormalizedHomologyZeroIsoPathComponents_hom
    (A : Type a) [AddCommGroup A] (X : TopCat.{w}) :
    (tensorNormalizedHomologyZeroIsoPathComponents.{a, w, p} A X).hom =
      (SSet.tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A
        (TopCat.toSSet.obj X)).hom ≫
        (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w p} A))).map
          (TopCat.zerothHomotopyEquiv (X := X)).toIso.inv := rfl

/-- The inverse map reindexes topological path components as singular
simplicial components before applying the inverse simplicial isomorphism. -/
theorem tensorNormalizedHomologyZeroIsoPathComponents_inv
    (A : Type a) [AddCommGroup A] (X : TopCat.{w}) :
    (tensorNormalizedHomologyZeroIsoPathComponents.{a, w, p} A X).inv =
      (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w p} A))).map
          (TopCat.zerothHomotopyEquiv (X := X)).toIso.hom ≫
        (SSet.tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A
          (TopCat.toSSet.obj X)).inv := rfl

/-- A singular vertex tensor maps to its lifted coefficient in the summand
indexed by the topological path component of the corresponding point. -/
theorem tensorNormalizedHomologyZeroIsoPathComponents_hom_class
    (A : Type a) [AddCommGroup A] (X : TopCat.{w})
    (v : (TopCat.toSSet.obj X) _⦋0⦌) (x : A) :
    (tensorNormalizedHomologyZeroIsoPathComponents.{a, w, p} A X).hom
      ((SSet.tensorNormalizedChainComplex.{a, w, p} A
        (TopCat.toSSet.obj X)).homologyπ₀
        (ULift.up ((TopCat.toSSet.obj X).normalizedIntegralSimplex v ⊗ₜ[ℤ] x))) =
      Sigma.ι (fun _ : ZerothHomotopy X => ModuleCat.of ℤ (ULift.{max w p} A))
        (ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv v)) (ULift.up x) := by
  let S := TopCat.toSSet.obj X
  let R := ModuleCat.of ℤ (ULift.{max w p} A)
  let c : SSet.π₀ S → ZerothHomotopy X :=
    (TopCat.zerothHomotopyEquiv (X := X)).symm
  rw [tensorNormalizedHomologyZeroIsoPathComponents_hom, ModuleCat.comp_apply,
    SSet.tensorNormalizedHomologyZeroIsoComponents_hom_class]
  change (Sigma.map' (f := fun _ : SSet.π₀ S => R)
    (g := fun _ : ZerothHomotopy X => R) c (fun _ => 𝟙 R))
      (Sigma.ι (fun _ : SSet.π₀ S => R) (SSet.π₀.mk v) (ULift.up x)) = _
  simpa only [Category.id_comp, ModuleCat.comp_apply, c, TopCat.zerothHomotopyEquiv_symm_mk] using
    (ConcreteCategory.congr_hom
      (Sigma.ι_comp_map' (f := fun _ : SSet.π₀ S => R)
        (g := fun _ : ZerothHomotopy X => R)
        c (fun _ => 𝟙 R) (SSet.π₀.mk v)) (ULift.up x))

end TopCat
