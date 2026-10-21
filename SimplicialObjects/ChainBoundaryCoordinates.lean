/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.ChainCoordinates

/-!
# Integral coordinates of simplicial boundaries

The differential of the simplicial chain complex becomes the alternating sum
of face pushforwards under `AlgebraicTopology.chainGroupIsoFinsupp`. Each
pushforward is `Finsupp.lmapDomain`, so coefficients of coincident faces are
added. No finiteness or injectivity assumption on the simplex types or face
maps is needed.

`AlgebraicTopology.chainGroupIsoFinsupp_d` is the morphism equation, with
reassociation supplied by `@[reassoc]`.
`AlgebraicTopology.chainGroupIsoFinsupp_d_apply` computes the coordinates of
the boundary of any chain, not only of a simplex generator. These statements
use the existing chain complex and integral coordinate isomorphisms; they
introduce no additional chain model or free-module functor.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 16, provides
  the mathematical background for integral simplicial chains.
* Mathlib's alternating-face-map complex, by Joël Riou, Adam Topaz and Johan
  Commelin, and its simplicial chain coproducts, by Joël Riou and Andrew Yang,
  supply the differential and its summand characterization.
* The integral coordinate isomorphisms and their summand and naturality API
  are the Formal Frontier Agents' formalization, including Prism's work.
  Mathlib supplies `Finsupp.lmapDomain` and `Finsupp.mapDomain`.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace AlgebraicTopology

/-- On a simplex summand with any lifted integer coefficient, the coordinate
map is the singleton with that integer as coefficient. -/
theorem chainGroupIsoFinsupp_hom_ι_apply (X : SSet.{u}) {n : ℕ}
    (x : X _⦋n⦌) (a : integerCoefficients.{u}) :
    (chainGroupIsoFinsupp X n).hom.hom
        ((X.ιChainComplex (R := integerCoefficients.{u}) x).hom a) =
      Finsupp.single x (ULift.moduleEquiv (R := ℤ) (M := ℤ) a) := by
  have h := ι_chainGroupIsoFinsupp_hom X x
  have ha := congr($h a)
  change (chainGroupIsoFinsupp X n).hom.hom
      ((X.ιChainComplex (R := integerCoefficients.{u}) x).hom a) =
        Finsupp.single x (ULift.moduleEquiv (R := ℤ) (M := ℤ) a) at ha
  exact ha

/-- Integral coordinates carry the simplicial differential to the alternating
sum of linear pushforwards along the face maps. -/
@[reassoc]
theorem chainGroupIsoFinsupp_d (X : SSet.{u}) (n : ℕ) :
    (X.chainComplex integerCoefficients.{u}).d (n + 1) n ≫
        (chainGroupIsoFinsupp X n).hom =
      (chainGroupIsoFinsupp X (n + 1)).hom ≫
        ModuleCat.ofHom
          (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
            Finsupp.lmapDomain ℤ ℤ (fun x : X _⦋n + 1⦌ => X.δ i x)) := by
  apply SSet.chainComplex_hom_ext (X := X) (R := integerCoefficients.{u})
  intro x
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  suffices
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          (chainGroupIsoFinsupp X n).hom.hom
            ((X.ιChainComplex (R := integerCoefficients.{u}) (X.δ i x)).hom a)) =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          Finsupp.mapDomain (fun y : X _⦋n + 1⦌ ↦ X.δ i y)
            ((chainGroupIsoFinsupp X (n + 1)).hom.hom
              ((X.ιChainComplex (R := integerCoefficients.{u}) x).hom a)) by
    simpa [ModuleCat.hom_sum, ModuleCat.hom_comp] using this
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun b : X _⦋n⦌ →₀ ℤ ↦ (-1 : ℤ) ^ i.val • b)
  calc
    _ = Finsupp.single (X.δ i x) (ULift.moduleEquiv (R := ℤ) (M := ℤ) a) :=
      chainGroupIsoFinsupp_hom_ι_apply X (X.δ i x) a
    _ = _ := by
      simpa only [Finsupp.mapDomain_single] using
        congrArg (Finsupp.mapDomain (fun y : X _⦋n + 1⦌ ↦ X.δ i y))
          (chainGroupIsoFinsupp_hom_ι_apply X x a).symm

/-- The coordinates of the boundary of an arbitrary integral chain are the
alternating sum of the pushforwards of its coordinates along the face maps.
Each pushforward sums over the chain's finite support, even if a face map has
infinite fibers. -/
theorem chainGroupIsoFinsupp_d_apply (X : SSet.{u}) (n : ℕ)
    (c : (X.chainComplex integerCoefficients.{u}).X (n + 1)) :
    (chainGroupIsoFinsupp X n).hom.hom
        (((X.chainComplex integerCoefficients.{u}).d (n + 1) n).hom c) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        Finsupp.mapDomain (fun x : X _⦋n + 1⦌ => X.δ i x)
          ((chainGroupIsoFinsupp X (n + 1)).hom.hom c) := by
  have h := congrArg ModuleCat.Hom.hom (chainGroupIsoFinsupp_d X n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  simpa using LinearMap.congr_fun h c

end AlgebraicTopology
