/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero

/-!
# Zeroth simplicial homology and its naturality

The canonical projection `ChainComplex.homologyπ₀` sends degree-zero chains to
homology. The component isomorphism `SSet.homology₀Iso` is natural for every
simplicial morphism in a preadditive category with coproducts and homology.

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

namespace ChainComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- The canonical projection from degree-zero chains to degree-zero homology.
All degree-zero chains are cycles in a chain complex indexed by `ℕ`. -/
noncomputable def homologyπ₀ (K : ChainComplex C ℕ) [K.HasHomology 0] :
    K.X 0 ⟶ K.homology 0 :=
  (cycles₀Iso K).inv ≫ K.homologyπ 0

instance (K : ChainComplex C ℕ) [K.HasHomology 0] : Epi K.homologyπ₀ := by
  dsimp only [homologyπ₀]
  infer_instance

/-- On cycles, the degree-zero projection is the usual homology projection. -/
@[reassoc (attr := simp)]
lemma iCycles_homologyπ₀ (K : ChainComplex C ℕ) [K.HasHomology 0] :
    K.iCycles 0 ≫ K.homologyπ₀ = K.homologyπ 0 := by
  change (cycles₀Iso K).hom ≫ (cycles₀Iso K).inv ≫ K.homologyπ 0 = _
  simp

/-- The projection agrees with the standard lift of a degree-zero cycle. -/
@[reassoc]
lemma comp_homologyπ₀ (K : ChainComplex C ℕ) [K.HasHomology 0]
    {T : C} (k : T ⟶ K.X 0) :
    k ≫ K.homologyπ₀ =
      K.liftCycles k 0 (by simp) (by simp) ≫ K.homologyπ 0 := by
  have h : k ≫ (cycles₀Iso K).inv =
      K.liftCycles k 0 (by simp) (by simp) := by
    apply (cancel_mono (K.iCycles 0)).mp
    simp only [Category.assoc, HomologicalComplex.iCyclesIso_inv_hom_id,
      Category.comp_id, HomologicalComplex.liftCycles_i]
  dsimp only [homologyπ₀]
  rw [← Category.assoc, h]

/-- A boundary has zero image in degree-zero homology. -/
@[reassoc (attr := simp)]
lemma d_homologyπ₀ (K : ChainComplex C ℕ) [K.HasHomology 0] (i : ℕ) :
    K.d i 0 ≫ K.homologyπ₀ = 0 := by
  have h : K.d i 0 ≫ (cycles₀Iso K).inv = K.toCycles i 0 := by
    apply (cancel_mono (K.iCycles 0)).mp
    simp only [Category.assoc, HomologicalComplex.iCyclesIso_inv_hom_id,
      Category.comp_id, HomologicalComplex.toCycles_i]
  dsimp only [homologyπ₀]
  rw [← Category.assoc, h, HomologicalComplex.toCycles_comp_homologyπ]

/-- The degree-zero projection is natural for chain maps. -/
@[reassoc]
lemma homologyπ₀_naturality {K L : ChainComplex C ℕ}
    [K.HasHomology 0] [L.HasHomology 0] (φ : K ⟶ L) :
    K.homologyπ₀ ≫ HomologicalComplex.homologyMap φ 0 =
      φ.f 0 ≫ L.homologyπ₀ := by
  have h : (cycles₀Iso K).inv ≫ HomologicalComplex.cyclesMap φ 0 =
      φ.f 0 ≫ (cycles₀Iso L).inv := by
    apply (cancel_mono (L.iCycles 0)).mp
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.iCyclesIso_inv_hom_id,
      HomologicalComplex.iCyclesIso_inv_hom_id_assoc, Category.comp_id]
  dsimp only [homologyπ₀]
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, h, Category.assoc]

end ChainComplex

namespace SSet

section General

open scoped Simplicial

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C]
  {S T : SSet.{w}}

private lemma ι_homologyπ₀_homology₀Iso_hom
    (S : SSet.{w}) (R : C) (x : S _⦋0⦌) :
    S.ιChainComplex x ≫ (S.chainComplex R).homologyπ₀ ≫
        (S.homology₀Iso R).hom =
      Sigma.ι (fun _ : π₀ S ↦ R) (π₀.mk x) := by
  rw [ChainComplex.comp_homologyπ₀_assoc]
  exact S.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom R x

/-- Mathlib's degree-zero component isomorphism is natural for every simplicial
morphism, with the identity coefficient map on each component summand. -/
@[reassoc]
theorem homology₀Iso_hom_naturality (f : S ⟶ T) (R : C) :
    SSet.homologyMap f R 0 ≫ (T.homology₀Iso R).hom =
      (S.homology₀Iso R).hom ≫
        Sigma.map' (mapπ₀ f) (fun _ : π₀ S ↦ 𝟙 R) := by
  apply (cancel_epi (S.chainComplex R).homologyπ₀).mp
  apply chainComplex_hom_ext (X := S) (R := R) (n := 0)
  intro x
  calc
    _ = (S.ιChainComplex x ≫ (chainComplexMap f R).f 0) ≫
        (T.chainComplex R).homologyπ₀ ≫ (T.homology₀Iso R).hom := by
      simpa only [SSet.homologyMap, Category.assoc] using
        congrArg (fun q ↦ S.ιChainComplex x ≫ q ≫ (T.homology₀Iso R).hom)
          (ChainComplex.homologyπ₀_naturality (chainComplexMap f R))
    _ = Sigma.ι (fun _ : π₀ T ↦ R) (π₀.mk (f.app _ x)) := by
      rw [ι_chainComplexMap_f]
      exact ι_homologyπ₀_homology₀Iso_hom T R (f.app _ x)
    _ = Sigma.ι (fun _ : π₀ S ↦ R) (π₀.mk x) ≫
        Sigma.map' (mapπ₀ f) (fun _ : π₀ S ↦ 𝟙 R) := by
      simp only [Sigma.ι_comp_map', Category.id_comp, mapπ₀_mk]
    _ = _ := by
      symm
      simpa only [Category.assoc] using
        congrArg
          (fun q ↦ q ≫ CategoryTheory.Limits.Sigma.map'
            (f := fun _ : π₀ S ↦ R) (g := fun _ : π₀ T ↦ R)
            (mapπ₀ f) (fun _ : π₀ S ↦ 𝟙 R))
          (ι_homologyπ₀_homology₀Iso_hom S R x)

end General

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
