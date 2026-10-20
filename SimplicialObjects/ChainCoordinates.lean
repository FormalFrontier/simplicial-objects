/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism.
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Integral coordinates for simplicial chains

For every simplicial set `X : SSet.{u}` and degree `n : ℕ`,
`AlgebraicTopology.chainGroupIsoFinsupp X n` identifies its all-simplex chain
module with finitely supported integer functions on `X _⦋n⦌`.
The coefficient object `AlgebraicTopology.integerCoefficients` is the image of
`ModuleCat.of ℤ ℤ` under `ModuleCat.uliftFunctor.{u} ℤ`; the coordinate map
removes this coefficient lift using `ULift.moduleEquiv`.

The morphism-level summand law computes the map on every lifted integer, and
`AlgebraicTopology.chainGroupIsoFinsupp_hom_ι` computes the unit basis chain.
These are degreewise module isomorphisms; no chain or natural isomorphism is
constructed here.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 16, provides
  the mathematical background for integral simplicial and singular chains.
* Mathlib's simplicial chain coproducts, by Joël Riou and Andrew Yang, and its
  module-category colimits, by Kim Morrison and Joël Riou, supply the two
  colimit cofans. Mathlib also supplies the lifted module functor and the
  `Finsupp.mapRange.linearEquiv` and `ULift.moduleEquiv` comparisons.
* Formal Frontier Agents, including Prism, supplied the integral-coordinate
  formalization used here.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

/-- Integer coefficients lifted into the universe of the singular simplices.
The underlying module is canonically linearly equivalent to `ℤ`. -/
abbrev integerCoefficients : ModuleCat.{u} ℤ :=
  (ModuleCat.uliftFunctor.{u} ℤ).obj (ModuleCat.of ℤ ℤ)

/-- Identify the degree-`n` integer-coefficient simplicial chain group with
finitely supported integer functions on the `n`-simplices. The construction
also removes the coefficient `ULift` used to accommodate the universe of `X`. -/
noncomputable def chainGroupIsoFinsupp (X : SSet.{u}) (n : ℕ) :
    (X.chainComplex integerCoefficients).X n ≅
      ModuleCat.of ℤ (X _⦋n⦌ →₀ ℤ) := by
  let e₁ := (X.isColimitChainComplexXCofan integerCoefficients n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℤ (ULift ℤ) (X _⦋n⦌))
  let e₂ : ModuleCat.of ℤ (X _⦋n⦌ →₀ ULift.{u} ℤ) ≅
      ModuleCat.of ℤ (X _⦋n⦌ →₀ ℤ) :=
    (Finsupp.mapRange.linearEquiv (ULift.moduleEquiv (R := ℤ) (M := ℤ))).toModuleIso
  exact e₁ ≪≫ e₂

set_option backward.isDefEq.respectTransparency false in
/-- On each simplex summand, integral coordinates remove the coefficient lift and
include the resulting integer as a finitely supported function. -/
theorem ι_chainGroupIsoFinsupp_hom (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌) :
    X.ιChainComplex (R := integerCoefficients) x ≫ (chainGroupIsoFinsupp X n).hom =
      ModuleCat.ofHom ((Finsupp.lsingle x).comp ULift.moduleEquiv.toLinearMap) := by
  let e₂ : ModuleCat.of ℤ (X _⦋n⦌ →₀ ULift.{u} ℤ) ≅
      ModuleCat.of ℤ (X _⦋n⦌ →₀ ℤ) :=
    (Finsupp.mapRange.linearEquiv (ULift.moduleEquiv (R := ℤ) (M := ℤ))).toModuleIso
  have h := (X.isColimitChainComplexXCofan integerCoefficients n)
    |>.comp_coconePointUniqueUpToIso_hom
      (ModuleCat.finsuppCoconeIsColimit ℤ (ULift ℤ) (X _⦋n⦌)) ⟨x⟩
  have h' := congrArg (fun f ↦ f ≫ e₂.hom) h
  calc
    _ = (ModuleCat.finsuppCocone ℤ (ULift ℤ) (X _⦋n⦌)).ι.app ⟨x⟩ ≫ e₂.hom := by
      rw [chainGroupIsoFinsupp, Iso.trans_hom, ← Category.assoc]
      exact h'
    _ = ModuleCat.ofHom ((Finsupp.lsingle x).comp ULift.moduleEquiv.toLinearMap) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      simp [e₂, ModuleCat.finsuppCocone]

/-- The lifted integer one in a simplex summand has the corresponding unit basis coordinate. -/
@[simp]
theorem chainGroupIsoFinsupp_hom_ι (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌) :
    (chainGroupIsoFinsupp X n).hom.hom
        ((X.ιChainComplex (R := integerCoefficients) x).hom (ULift.up (1 : ℤ))) =
      Finsupp.single x 1 := by
  have h := ι_chainGroupIsoFinsupp_hom X x
  have h1 := congr($h (ULift.up (1 : ℤ)))
  change (chainGroupIsoFinsupp X n).hom.hom
      ((X.ιChainComplex (R := integerCoefficients) x).hom (ULift.up (1 : ℤ))) =
        Finsupp.single x 1 at h1
  exact h1

end AlgebraicTopology
