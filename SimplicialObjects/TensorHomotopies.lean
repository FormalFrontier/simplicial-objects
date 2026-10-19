/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorMaps
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Homotopies of normalized integral tensor maps

A combinatorial simplicial homotopy gives a chain homotopy between the original
integral tensor chain maps. The construction surrounds Mathlib's all-simplex
chain homotopy with the normalization section and projection and the tensor
comparison isomorphisms. Its components, off-shape vanishing and homotopy equation
are those of the stock composition operations. Cylinder homotopies use the
existing conversion to combinatorial simplicial homotopies.

The coefficient, simplex and padding universes are independent. The coefficient
object is exactly `ModuleCat.of ℤ (ULift.{max w p} A)`, with the canonical integer
module structure, and only `AddCommGroup A` is required.

## Limitations

The constructed chain homotopies give equality of the induced homology maps
by Mathlib's `Homotopy.homologyMap_eq`. Their component formulas are independent
of this consequence. The scope is absolute simplicial sets and
natural-number-graded homology, not
relative topological singular homology or a comparison of categories of spaces.
The orientation is `f - g = dH + Hd`; for the initial-to-terminal interval
homotopy this gives the negative of the standard simplicial edge.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, revised edition, §12.1–2
  (chain homotopies and equality on homology) and §16.1 (normalized integral
  chains with abelian coefficients).
* Mathlib's chain-homotopy composition and homology-invariance API is due to
  Kim Morrison. The
  simplicial-to-chain constructions are due to Fabian Odermatt and Joël Riou;
  the normalized-chain and cylinder-to-combinatorial constructions are due to
  Joël Riou. These existing constructions supply the homotopy used here.
* The tensor comparison and the present assembly are AI-assisted formalizations
  by Formal Frontier Agents, separate from the cited mathematics and Mathlib.
-/

@[expose] public section

universe a w p

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.Homotopy

variable {S T : SSet.{w}} {f g : S ⟶ T}

/-- The chain homotopy of integral tensor maps induced by a combinatorial
simplicial homotopy, with orientation `f - g = dH + Hd`. It uses the existing
normalization section and projection and does not change the tensor boundary. -/
noncomputable def tensorNormalizedChainComplexMap
    (H : CategoryTheory.SimplicialObject.Homotopy f g) (A : Type a) [AddCommGroup A] :
    _root_.Homotopy (SSet.tensorNormalizedChainComplexMap.{a, w, p} A f)
      (SSet.tensorNormalizedChainComplexMap.{a, w, p} A g) := by
  let R := ModuleCat.of ℤ (ULift.{max w p} A)
  let K := ((H.sSetChainComplexMap R).compLeft
    ((SSet.tensorNormalizedChainIso.{a, w, p} A S).hom ≫
      S.fromNormalizedChainComplex R)).compRight
        (T.toNormalizedChainComplex R ≫
          (SSet.tensorNormalizedChainIso.{a, w, p} A T).inv)
  refine (_root_.Homotopy.ofEq ?_).trans (K.trans (_root_.Homotopy.ofEq ?_))
  · simp only [R, SSet.tensorNormalizedChainComplexMap_eq,
      SSet.normalizedChainComplexMap, Category.assoc]
  · simp only [R, SSet.tensorNormalizedChainComplexMap_eq,
      SSet.normalizedChainComplexMap, Category.assoc]

/-- Each component is the all-simplex chain homotopy between the four supplied
comparison, section and projection maps. Equality homotopies at the endpoints
contribute zero components. -/
theorem tensorNormalizedChainComplexMap_hom
    (H : CategoryTheory.SimplicialObject.Homotopy f g) (A : Type a) [AddCommGroup A]
    (i j : ℕ) :
    (H.tensorNormalizedChainComplexMap.{a, w, p} A).hom i j =
      (SSet.tensorNormalizedChainIso.{a, w, p} A S).hom.f i ≫
        (S.fromNormalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).f i ≫
          (H.sSetChainComplexMap (ModuleCat.of ℤ (ULift.{max w p} A))).hom i j ≫
            (T.toNormalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).f j ≫
              (SSet.tensorNormalizedChainIso.{a, w, p} A T).inv.f j := by
  simp only [tensorNormalizedChainComplexMap, _root_.Homotopy.trans_hom,
    _root_.Homotopy.ofEq_hom, _root_.Homotopy.compRight_hom,
    _root_.Homotopy.compLeft_hom, HomologicalComplex.comp_f, Pi.zero_apply, zero_add, add_zero,
    SSet.tensorNormalizedChainIso_hom_f, SSet.tensorNormalizedChainIso_inv_f]
  exact Category.assoc
    (SSet.tensorNormalizedChainComplexXIso.{a, w, p} A S i).hom
    ((S.fromNormalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).f i)
    ((H.sSetChainComplexMap (ModuleCat.of ℤ (ULift.{max w p} A))).hom i j ≫
      (T.toNormalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).f j ≫
        (SSet.tensorNormalizedChainComplexXIso.{a, w, p} A T j).inv)

/-- In degree zero the homotopy equation has no incoming lower-degree term.
The general equations and off-shape vanishing are also accessible as the
`comm` and `zero` fields of the constructed `Homotopy`. -/
theorem tensorNormalizedChainComplexMap_comm_zero
    (H : CategoryTheory.SimplicialObject.Homotopy f g) (A : Type a) [AddCommGroup A] :
    (SSet.tensorNormalizedChainComplexMap.{a, w, p} A f).f 0 =
      (H.tensorNormalizedChainComplexMap.{a, w, p} A).hom 0 1 ≫
        (SSet.tensorNormalizedChainComplex.{a, w, p} A T).d 1 0 +
          (SSet.tensorNormalizedChainComplexMap.{a, w, p} A g).f 0 := by
  simpa only [_root_.Homotopy.dNext_zero_chainComplex,
    _root_.Homotopy.prevD_chainComplex, zero_add] using
      (H.tensorNormalizedChainComplexMap.{a, w, p} A).comm 0

/-- Combinatorially homotopic simplicial maps induce equal maps on the homology
of the original normalized integral tensor complexes. This is the absolute
simplicial, natural-number-graded instance of May's chain-homotopy principle
(*A Concise Course in Algebraic Topology*, revised edition, §12.2), with
orientation `f - g = dH + Hd`. -/
theorem congr_tensorNormalizedHomologyMap
    (H : CategoryTheory.SimplicialObject.Homotopy f g) (A : Type a) [AddCommGroup A]
    (n : ℕ) :
    HomologicalComplex.homologyMap (SSet.tensorNormalizedChainComplexMap.{a, w, p} A f) n =
      HomologicalComplex.homologyMap (SSet.tensorNormalizedChainComplexMap.{a, w, p} A g) n := by
  exact (H.tensorNormalizedChainComplexMap.{a, w, p} A).homologyMap_eq n

end CategoryTheory.SimplicialObject.Homotopy

namespace SSet.Homotopy

variable {S T : SSet.{w}} {f g : S ⟶ T}

/-- A cylinder homotopy gives a homotopy of the original normalized integral
tensor maps through its combinatorial simplicial homotopy. -/
noncomputable def tensorNormalizedChainComplexMap
    (H : SSet.Homotopy f g) (A : Type a) [AddCommGroup A] :
    _root_.Homotopy (SSet.tensorNormalizedChainComplexMap.{a, w, p} A f)
      (SSet.tensorNormalizedChainComplexMap.{a, w, p} A g) :=
  H.toSimplicialObjectHomotopy.tensorNormalizedChainComplexMap.{a, w, p} A

/-- The cylinder construction is the combinatorial construction applied to the
existing cylinder-to-simplicial conversion. -/
@[simp]
theorem tensorNormalizedChainComplexMap_eq
    (H : SSet.Homotopy f g) (A : Type a) [AddCommGroup A] :
    H.tensorNormalizedChainComplexMap.{a, w, p} A =
      H.toSimplicialObjectHomotopy.tensorNormalizedChainComplexMap.{a, w, p} A := rfl

/-- Cylinder-homotopic simplicial maps induce equal maps on homology of the
original normalized integral tensor complexes. This is the absolute simplicial,
natural-number-graded form of the chain-homotopy principle in May's
*A Concise Course in Algebraic Topology*, revised edition, §12.2; the chosen
chain homotopy is oriented by `f - g = dH + Hd`. -/
theorem congr_tensorNormalizedHomologyMap
    (H : SSet.Homotopy f g) (A : Type a) [AddCommGroup A] (n : ℕ) :
    HomologicalComplex.homologyMap (SSet.tensorNormalizedChainComplexMap.{a, w, p} A f) n =
      HomologicalComplex.homologyMap (SSet.tensorNormalizedChainComplexMap.{a, w, p} A g) n := by
  exact (H.tensorNormalizedChainComplexMap.{a, w, p} A).homologyMap_eq n

end SSet.Homotopy

namespace SSet

/-- A simplicial map with a two-sided combinatorial homotopy inverse induces a
quasi-isomorphism of normalized integral tensor complexes. The tensor comparison
transports the categorical normalized-chain analogue of the chain-homotopy
invariance argument in May, *A Concise Course in Algebraic Topology*, revised
edition, §§12.2 and 13.3. The coefficient, simplex and padding universes are
independent. -/
theorem quasiIso_tensorNormalizedChainComplexMap_of_homotopy_inverse
    (A : Type a) [AddCommGroup A]
    {S T : SSet.{w}} (f : S ⟶ T) (g : T ⟶ S)
    (Hfg : CategoryTheory.SimplicialObject.Homotopy (f ≫ g) (𝟙 S))
    (Hgf : CategoryTheory.SimplicialObject.Homotopy (g ≫ f) (𝟙 T)) :
    QuasiIso (tensorNormalizedChainComplexMap.{a, w, p} A f) := by
  have : QuasiIso
      (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A))) :=
    quasiIso_normalizedChainComplexMap_of_homotopy_inverse f g Hfg Hgf
      (ModuleCat.of ℤ (ULift.{max w p} A))
  rw [tensorNormalizedChainComplexMap_eq]
  infer_instance

end SSet
