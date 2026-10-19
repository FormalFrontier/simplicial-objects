/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero

/-!
# Coefficient naturality of zeroth simplicial homology

Changing coefficients acts coefficientwise on simplicial chain generators.
In degree zero, `SSet.homology₀Iso` intertwines this coefficient chain map with
the fixed-index coproduct map on path components, both for the isomorphism and
for its inverse.

## References

* Mathlib's simplicial homology and zeroth-homology isomorphism API, by Joël Riou
  and Andrew Yang, and its categorical coproduct API.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] (S : SSet.{w}) (R R' : C) (a : R ⟶ R')

omit [CategoryWithHomology C] in
open scoped Simplicial in
/-- Changing coefficients acts coefficientwise on each simplicial chain generator. -/
@[reassoc (attr := simp)]
theorem ιChainComplex_coefficient_naturality {n : ℕ} (x : S _⦋n⦌) :
    S.ιChainComplex (R := R) x ≫ (((chainComplexFunctor C).map a).app S).f n =
      a ≫ S.ιChainComplex (R := R') x := by
  change Sigma.ι (fun _ : S _⦋n⦌ => R) x ≫
      CategoryTheory.Limits.Sigma.map (fun _ : S _⦋n⦌ => a) =
    a ≫ Sigma.ι (fun _ : S _⦋n⦌ => R') x
  exact Sigma.ι_map (fun _ : S _⦋n⦌ => a) x

/-- The forward zeroth-homology isomorphism commutes with change of coefficients. -/
theorem homology₀Iso_hom_coefficient_naturality :
    HomologicalComplex.homologyMap (((SSet.chainComplexFunctor C).map a).app S) 0 ≫
        (S.homology₀Iso R').hom =
      (S.homology₀Iso R).hom ≫
        CategoryTheory.Limits.Sigma.map (fun _ : SSet.π₀ S => a) := by
  apply (cancel_epi ((S.chainComplex R).homologyπ 0)).1
  apply (cancel_epi (S.chainComplex R).cycles₀Iso.inv).1
  apply SSet.chainComplex_hom_ext
  intro x
  have hι : S.ιChainComplex (R := R) x ≫ (S.chainComplex R).cycles₀Iso.inv =
      (S.chainComplex R).liftCycles (S.ιChainComplex x) 0 (by simp) (by simp) := by
    apply (cancel_mono ((S.chainComplex R).iCycles 0)).1
    simp
  simp only [← Category.assoc, hι]
  simp only [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    ιChainComplex_coefficient_naturality]
  rw [← HomologicalComplex.comp_liftCycles_assoc] <;> simp

/-- The inverse zeroth-homology isomorphism commutes with change of coefficients.
This follows from forward coefficient naturality by cancellation with the isomorphisms. -/
theorem homology₀Iso_inv_coefficient_naturality :
    CategoryTheory.Limits.Sigma.map (fun _ : SSet.π₀ S => a) ≫
        (S.homology₀Iso R').inv =
      (S.homology₀Iso R).inv ≫
        HomologicalComplex.homologyMap (((SSet.chainComplexFunctor C).map a).app S) 0 := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (homology₀Iso_hom_coefficient_naturality S R R' a).symm

end SSet
