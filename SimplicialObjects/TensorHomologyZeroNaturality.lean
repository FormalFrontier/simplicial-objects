/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorHomologyZero

/-!
# Simplicial naturality of degree-zero tensor homology

The component isomorphism for normalized tensor homology commutes with every
simplicial morphism. On components the map is the stock coproduct map induced
by `SSet.mapπ₀`, with the identity on coefficients. In particular, a morphism
may send a nondegenerate simplex to a degenerate simplex.

The proof uses the general preadditive-category naturality theorem from
`SimplicialObjects.HomologyZero` and the homology-level normalization naturality
theorem from `SimplicialObjects.Normalization`, together with the tensor chain
comparison. No choice of component representatives is required.

## References and attribution

* Mathlib's simplicial homology and degree-zero component isomorphism,
  notably the formalization by Joël Riou, provide the all-simplex chain
  generators, normalization homotopy equivalence and vertex characteristic law.
* `SimplicialObjects.TensorMaps` provides the integral tensor chain comparison
  and its naturality for arbitrary simplicial morphisms.
-/

@[expose] public section

universe a w p

open CategoryTheory Limits
open scoped Simplicial

namespace SSet

variable {S T : SSet.{w}}

/-- The normalized tensor component isomorphism is natural for every
simplicial morphism. The map on the component coproduct is the stock
`Sigma.map'` induced by `mapπ₀ f`, with identity coefficients. -/
@[reassoc]
theorem tensorNormalizedHomologyZeroIsoComponents_hom_naturality
    (A : Type a) [AddCommGroup A] (f : S ⟶ T) :
    HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexMap.{a, w, p} A f) 0 ≫
        (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A T).hom =
      (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom ≫
        Sigma.map' (mapπ₀ f)
          (fun _ : π₀ S ↦ 𝟙 (ModuleCat.of ℤ (ULift.{max w p} A))) := by
  let R := ModuleCat.of ℤ (ULift.{max w p} A)
  have h : HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexMap.{a, w, p} A f) 0 ≫
        HomologicalComplex.homologyMap (tensorNormalizedChainIso.{a, w, p} A T).hom 0 =
      HomologicalComplex.homologyMap (tensorNormalizedChainIso.{a, w, p} A S).hom 0 ≫
        HomologicalComplex.homologyMap (normalizedChainComplexMap f R) 0 := by
    have hchain :
        tensorNormalizedChainComplexMap.{a, w, p} A f ≫
            (tensorNormalizedChainIso.{a, w, p} A T).hom =
          (tensorNormalizedChainIso.{a, w, p} A S).hom ≫
            normalizedChainComplexMap f R := by
      exact (tensorNormalizedChainIso_hom_naturality.{a, w, p} A f).symm
    calc
      _ = HomologicalComplex.homologyMap
          (tensorNormalizedChainComplexMap.{a, w, p} A f ≫
            (tensorNormalizedChainIso.{a, w, p} A T).hom) 0 :=
        (HomologicalComplex.homologyMap_comp
          (tensorNormalizedChainComplexMap.{a, w, p} A f)
          (tensorNormalizedChainIso.{a, w, p} A T).hom 0).symm
      _ = HomologicalComplex.homologyMap
          ((tensorNormalizedChainIso.{a, w, p} A S).hom ≫
            normalizedChainComplexMap f R) 0 :=
        congrArg (fun q : tensorNormalizedChainComplex.{a, w, p} A S ⟶
          T.normalizedChainComplex R ↦ HomologicalComplex.homologyMap q 0) hchain
      _ = _ := HomologicalComplex.homologyMap_comp
        (tensorNormalizedChainIso.{a, w, p} A S).hom
        (normalizedChainComplexMap f R) 0
  calc
    _ = HomologicalComplex.homologyMap (tensorNormalizedChainIso.{a, w, p} A S).hom 0 ≫
        HomologicalComplex.homologyMap (normalizedChainComplexMap f R) 0 ≫
        ((T.homotopyEquivNormalizedChainComplex R).symm.toHomologyIso 0).hom ≫
        (T.homology₀Iso R).hom := by
      simpa only [tensorNormalizedHomologyZeroIsoComponents, Iso.trans_hom,
        HomologicalComplex.homologyMapIso_hom, Category.assoc] using
        congrArg
          (fun q ↦ q ≫
            ((T.homotopyEquivNormalizedChainComplex R).symm.toHomologyIso 0).hom ≫
            (T.homology₀Iso R).hom) h
    _ = HomologicalComplex.homologyMap (tensorNormalizedChainIso.{a, w, p} A S).hom 0 ≫
        ((S.homotopyEquivNormalizedChainComplex R).symm.toHomologyIso 0).hom ≫
        HomologicalComplex.homologyMap (chainComplexMap f R) 0 ≫
        (T.homology₀Iso R).hom := by
      rw [homotopyEquivNormalizedChainComplex_inv_homology_naturality_assoc]
    _ = _ := by
      change _ = (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom ≫
        CategoryTheory.Limits.Sigma.map'
          (f := fun _ : π₀ S ↦ R) (g := fun _ : π₀ T ↦ R)
          (mapπ₀ f) (fun _ : π₀ S ↦ 𝟙 R)
      rw [show HomologicalComplex.homologyMap (chainComplexMap f R) 0 =
          SSet.homologyMap f R 0 from rfl, homology₀Iso_hom_naturality]
      simp only [R, tensorNormalizedHomologyZeroIsoComponents, Iso.trans_hom,
        HomologicalComplex.homologyMapIso_hom, Category.assoc]

/-- On each component summand, the induced tensor homology map sends the
coefficient unchanged to the summand indexed by its image component. -/
@[reassoc]
theorem tensorNormalizedHomologyZeroIsoComponents_hom_naturality_ι
    (A : Type a) [AddCommGroup A] (f : S ⟶ T) (c : π₀ S) :
    Sigma.ι (fun _ : π₀ S ↦ ModuleCat.of ℤ (ULift.{max w p} A)) c ≫
        (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).inv ≫
        HomologicalComplex.homologyMap
          (tensorNormalizedChainComplexMap.{a, w, p} A f) 0 ≫
        (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A T).hom =
      Sigma.ι (fun _ : π₀ T ↦ ModuleCat.of ℤ (ULift.{max w p} A)) (mapπ₀ f c) := by
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Sigma.ι_comp_map',
    Category.id_comp] using
    congrArg
      (fun q ↦
        Sigma.ι (fun _ : π₀ S ↦ ModuleCat.of ℤ (ULift.{max w p} A)) c ≫
          (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).inv ≫ q)
      (tensorNormalizedHomologyZeroIsoComponents_hom_naturality.{a, w, p} A f)

/-- The inverse component isomorphisms satisfy the same simplicial naturality
square, without injectivity or nondegeneracy-preservation assumptions. -/
@[reassoc]
theorem tensorNormalizedHomologyZeroIsoComponents_inv_naturality
    (A : Type a) [AddCommGroup A] (f : S ⟶ T) :
    Sigma.map' (mapπ₀ f)
        (fun _ : π₀ S ↦ 𝟙 (ModuleCat.of ℤ (ULift.{max w p} A))) ≫
        (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A T).inv =
      (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).inv ≫
        HomologicalComplex.homologyMap
          (tensorNormalizedChainComplexMap.{a, w, p} A f) 0 := by
  apply (cancel_mono (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A T).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using
    (congrArg
      (fun q ↦ (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).inv ≫ q)
      (tensorNormalizedHomologyZeroIsoComponents_hom_naturality.{a, w, p} A f)).symm

end SSet
