/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.Free
public import SimplicialObjects.ChainBoundaryCoordinates

/-!
# Ordinary finitely supported coordinates for simplicial chain complexes

`AlgebraicTopology.finsuppChainComplexFunctor R` first applies
`ModuleCat.freeOn R` to a simplicial set and then takes its alternating-face-map
complex. Its degree-`n` object is the ordinary module `X _⦋n⦌ →₀ R`.
The coefficient ring and simplex types may lie in independent universes.

A simplicial map acts on every finitely supported chain by
`Finsupp.mapDomain`. Thus coefficients with the same image are added; no
injectivity or finite-fiber assumption is needed. The differential is the
alternating sum of these pushforwards along the face maps, with integer signs
acting by additive scalar multiplication. Unrelated degree pairs have zero
differential by `HomologicalComplex.shape`.

## References

* Mathlib's alternating-face-map complex, by Joël Riou, Adam Topaz and Johan
  Commelin, and right whiskering, by Kim Morrison, supply the composite
  construction.
* `ModuleCat.freeOn`, supplied by Formal Frontier Agents, generalizes
  Mathlib's free-module functor, by Kim Morrison and Johan Commelin, to
  independent universes using ordinary finitely supported functions.
* The integral coordinate and boundary formulas used for comparison are the
  Formal Frontier Agents' formalization, including Prism's work.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe r s u

namespace AlgebraicTopology

/-- The alternating-face-map complex of the ordinary free modules on a
simplicial set, with independently sized coefficient ring and simplex types. -/
noncomputable def finsuppChainComplexFunctor (R : Type r) [Ring R] :
    SSet.{s} ⥤ ChainComplex (ModuleCat.{max r s} R) ℕ :=
  ((SimplicialObject.whiskering (Type s) (ModuleCat.{max r s} R)).obj
    (ModuleCat.freeOn R : Type s ⥤ ModuleCat.{max r s} R)) ⋙
      alternatingFaceMapComplex (ModuleCat.{max r s} R)

section

variable (R : Type r) [Ring R]

/-- The degree object is the ordinary finitely supported module on simplices. -/
@[simp]
theorem finsuppChainComplexFunctor_obj_X (X : SSet.{s}) (n : ℕ) :
    ((finsuppChainComplexFunctor R).obj X).X n =
      ModuleCat.of R (X _⦋n⦌ →₀ R) := by
  rfl

/-- A simplicial map acts degreewise by the linear pushforward of finitely
supported functions on simplices. -/
theorem finsuppChainComplexFunctor_map_f {X Y : SSet.{s}} (f : X ⟶ Y) (n : ℕ) :
    ((finsuppChainComplexFunctor R).map f).f n =
      ModuleCat.ofHom (Finsupp.lmapDomain R R
        (fun x : X _⦋n⦌ => f.app (Opposite.op ⦋n⦌) x)) := by
  rfl

/-- On every chain, the induced map sums coefficients over the fibers of the
simplex map, restricted to that chain's finite support. -/
@[simp]
theorem finsuppChainComplexFunctor_map_f_apply {X Y : SSet.{s}}
    (f : X ⟶ Y) (n : ℕ) (c : X _⦋n⦌ →₀ R) :
    (((finsuppChainComplexFunctor R).map f).f n).hom c =
      Finsupp.mapDomain (fun x : X _⦋n⦌ => f.app (Opposite.op ⦋n⦌) x) c := by
  rw [finsuppChainComplexFunctor_map_f]
  rfl

/-- The adjacent differential is the alternating sum of the linear face
pushforwards. Its signs act by integer scalar multiplication. -/
@[simp]
theorem finsuppChainComplexFunctor_obj_d (X : SSet.{s}) (n : ℕ) :
    ((finsuppChainComplexFunctor R).obj X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ModuleCat.ofHom (Finsupp.lmapDomain R R
          (fun x : X _⦋n + 1⦌ => X.δ i x)) := by
  change (AlternatingFaceMapComplex.obj (X ⋙ ModuleCat.freeOn R)).d (n + 1) n = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  rfl

/-- The boundary of any finitely supported chain is the signed sum of its
pushforwards along the face maps. Coincident faces contribute additively. -/
theorem finsuppChainComplexFunctor_obj_d_apply (X : SSet.{s}) (n : ℕ)
    (c : X _⦋n + 1⦌ →₀ R) :
    (((finsuppChainComplexFunctor R).obj X).d (n + 1) n).hom c =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        Finsupp.mapDomain (fun x : X _⦋n + 1⦌ => X.δ i x) c := by
  have h := congrArg
    (fun f : ModuleCat.of R (X _⦋n + 1⦌ →₀ R) ⟶
        ModuleCat.of R (X _⦋n⦌ →₀ R) => f.hom c)
    (finsuppChainComplexFunctor_obj_d R X n)
  rw [ModuleCat.hom_sum
    (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val •
      ModuleCat.ofHom (Finsupp.lmapDomain R R
        (fun x : X _⦋n + 1⦌ => X.δ i x))) Finset.univ] at h
  simp only [ModuleCat.hom_zsmul, ModuleCat.hom_ofHom] at h
  refine h.trans ?_
  simpa only [LinearMap.evalAddMonoidHom_apply, LinearMap.smul_apply,
    Finsupp.lmapDomain_apply] using
    map_sum (LinearMap.evalAddMonoidHom c)
      (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val •
        Finsupp.lmapDomain R R (fun x : X _⦋n + 1⦌ => X.δ i x)) Finset.univ

end

/-- The original integral simplicial chain-complex functor is naturally
isomorphic to the ordinary finitely supported coordinate complex. Its
isomorphism in every degree is the existing integral coordinate isomorphism. -/
noncomputable def chainComplexIsoFinsupp :
    ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}) ≅
      (finsuppChainComplexFunctor ℤ :
        SSet.{u} ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  NatIso.ofComponents
    (fun X => HomologicalComplex.Hom.isoOfComponents
      (fun n => chainGroupIsoFinsupp X n)
      (by
        intro i j hij
        rw [ComplexShape.down_Rel] at hij
        subst i
        rw [finsuppChainComplexFunctor_obj_d ℤ X j]
        have hsum :
            ModuleCat.ofHom
                (∑ k : Fin (j + 2), (-1 : ℤ) ^ k.val •
                  Finsupp.lmapDomain ℤ ℤ (fun x : X _⦋j + 1⦌ => X.δ k x)) =
              ∑ k : Fin (j + 2), (-1 : ℤ) ^ k.val •
                ModuleCat.ofHom
                  (Finsupp.lmapDomain ℤ ℤ (fun x : X _⦋j + 1⦌ => X.δ k x)) := by
          apply ModuleCat.hom_injective
          rw [ModuleCat.hom_ofHom]
          rw [ModuleCat.hom_sum
            (fun k : Fin (j + 2) => (-1 : ℤ) ^ k.val •
              ModuleCat.ofHom
                (Finsupp.lmapDomain ℤ ℤ (fun x : X _⦋j + 1⦌ => X.δ k x)))
            Finset.univ]
          simp only [ModuleCat.hom_zsmul, ModuleCat.hom_ofHom]
        rw [← hsum]
        exact (chainGroupIsoFinsupp_d X j).symm))
    (by
      intro X Y f
      apply HomologicalComplex.hom_ext
      intro n
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      change (SSet.chainComplexMap f integerCoefficients.{u}).f n ≫
          (chainGroupIsoFinsupp Y n).hom =
        (chainGroupIsoFinsupp X n).hom ≫
          ((finsuppChainComplexFunctor ℤ).map f).f n
      rw [finsuppChainComplexFunctor_map_f ℤ f n]
      exact chainGroupIsoFinsupp_naturality f n)

/-- The forward comparison in each degree is the original coordinate map. -/
@[simp]
theorem chainComplexIsoFinsupp_hom_f (X : SSet.{u}) (n : ℕ) :
    (chainComplexIsoFinsupp.hom.app X).f n = (chainGroupIsoFinsupp X n).hom :=
  rfl

/-- The inverse comparison in each degree is the inverse original coordinate map. -/
@[simp]
theorem chainComplexIsoFinsupp_inv_f (X : SSet.{u}) (n : ℕ) :
    (chainComplexIsoFinsupp.inv.app X).f n = (chainGroupIsoFinsupp X n).inv :=
  rfl

/-- Degree evaluation of a comparison component gives the original coordinate
isomorphism, with both its forward and inverse maps. -/
@[simp]
theorem chainComplexIsoFinsupp_isoApp (X : SSet.{u}) (n : ℕ) :
    HomologicalComplex.Hom.isoApp (chainComplexIsoFinsupp.app X) n =
      chainGroupIsoFinsupp X n := by
  apply Iso.ext
  change (chainComplexIsoFinsupp.hom.app X).f n = (chainGroupIsoFinsupp X n).hom
  exact chainComplexIsoFinsupp_hom_f X n

/-- Applying the degree-evaluation functor to the comparison gives exactly the
original coordinate isomorphism. -/
@[simp]
theorem chainComplexIsoFinsupp_eval (X : SSet.{u}) (n : ℕ) :
    (HomologicalComplex.eval (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n).mapIso
      (chainComplexIsoFinsupp.app X) = chainGroupIsoFinsupp X n := by
  simpa only [HomologicalComplex.Hom.isoApp] using
    chainComplexIsoFinsupp_isoApp X n

/-- Right-whiskering the natural comparison by degree evaluation retains the
original integral coordinate isomorphism at every simplicial set. -/
@[simp]
theorem chainComplexIsoFinsupp_eval_app (X : SSet.{u}) (n : ℕ) :
    (Functor.isoWhiskerRight chainComplexIsoFinsupp
      (HomologicalComplex.eval (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n)).app X =
        chainGroupIsoFinsupp X n := by
  apply Iso.ext
  change (chainComplexIsoFinsupp.hom.app X).f n = (chainGroupIsoFinsupp X n).hom
  exact chainComplexIsoFinsupp_hom_f X n

/-- The comparison sends every original chain to its original coordinates. -/
theorem chainComplexIsoFinsupp_hom_f_apply (X : SSet.{u}) (n : ℕ)
    (c : (X.chainComplex integerCoefficients.{u}).X n) :
    ((chainComplexIsoFinsupp.hom.app X).f n).hom c =
      (chainGroupIsoFinsupp X n).hom.hom c := by
  rfl

/-- The inverse comparison sends every finite coordinate function to the chain
specified by the original inverse coordinate isomorphism. -/
theorem chainComplexIsoFinsupp_inv_f_apply (X : SSet.{u}) (n : ℕ)
    (c : X _⦋n⦌ →₀ ℤ) :
    ((chainComplexIsoFinsupp.inv.app X).f n).hom c =
      (chainGroupIsoFinsupp X n).inv.hom c := by
  rfl

/-- For any simplicial map and any original chain, the natural comparison
identifies the induced chain map with pushforward of its coordinates.
Coefficients of colliding simplices are added. -/
theorem chainComplexIsoFinsupp_naturality_apply {X Y : SSet.{u}} (f : X ⟶ Y)
    (n : ℕ) (c : (X.chainComplex integerCoefficients.{u}).X n) :
    ((chainComplexIsoFinsupp.hom.app Y).f n).hom
        (((SSet.chainComplexMap f integerCoefficients.{u}).f n).hom c) =
      Finsupp.mapDomain (fun x : X _⦋n⦌ => f.app (Opposite.op ⦋n⦌) x)
        (((chainComplexIsoFinsupp.hom.app X).f n).hom c) := by
  have h := HomologicalComplex.congr_hom (chainComplexIsoFinsupp.hom.naturality f) n
  change (SSet.chainComplexMap f integerCoefficients.{u}).f n ≫
      (chainComplexIsoFinsupp.hom.app Y).f n =
    (chainComplexIsoFinsupp.hom.app X).f n ≫
      ((finsuppChainComplexFunctor ℤ).map f).f n at h
  have hc := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) c
  change ((chainComplexIsoFinsupp.hom.app Y).f n).hom
      (((SSet.chainComplexMap f integerCoefficients.{u}).f n).hom c) =
    (((finsuppChainComplexFunctor ℤ).map f).f n).hom
      (((chainComplexIsoFinsupp.hom.app X).f n).hom c) at hc
  exact hc.trans (finsuppChainComplexFunctor_map_f_apply ℤ f n _)

/-- The inverse natural comparison intertwines every finite coordinate
pushforward with the original induced chain map. -/
theorem chainComplexIsoFinsupp_inv_naturality_apply {X Y : SSet.{u}} (f : X ⟶ Y)
    (n : ℕ) (c : X _⦋n⦌ →₀ ℤ) :
    ((SSet.chainComplexMap f integerCoefficients.{u}).f n).hom
        (((chainComplexIsoFinsupp.inv.app X).f n).hom c) =
      ((chainComplexIsoFinsupp.inv.app Y).f n).hom
        (Finsupp.mapDomain (fun x : X _⦋n⦌ => f.app (Opposite.op ⦋n⦌) x) c) := by
  have h := HomologicalComplex.congr_hom (chainComplexIsoFinsupp.inv.naturality f) n
  change ((finsuppChainComplexFunctor ℤ).map f).f n ≫
      (chainComplexIsoFinsupp.inv.app Y).f n =
    (chainComplexIsoFinsupp.inv.app X).f n ≫
      (SSet.chainComplexMap f integerCoefficients.{u}).f n at h
  have hc := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h.symm) c
  change ((SSet.chainComplexMap f integerCoefficients.{u}).f n).hom
      (((chainComplexIsoFinsupp.inv.app X).f n).hom c) =
    ((chainComplexIsoFinsupp.inv.app Y).f n).hom
      ((((finsuppChainComplexFunctor ℤ).map f).f n).hom c) at hc
  exact hc.trans (congrArg ((chainComplexIsoFinsupp.inv.app Y).f n).hom
    (finsuppChainComplexFunctor_map_f_apply ℤ f n c))

end AlgebraicTopology
