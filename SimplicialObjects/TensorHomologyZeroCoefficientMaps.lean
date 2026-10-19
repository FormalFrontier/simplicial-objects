/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorHomologyZero
public import SimplicialObjects.TensorCoefficientMaps

/-!
# Change of coefficients in degree-zero normalized tensor homology

The component isomorphism is natural for arbitrary additive coefficient
homomorphisms. The coefficient universes, simplex universe and padding universe
are independent: source padding is `max b p`, target padding is `max a p`, and
all morphisms lie in `ModuleCat.{max a b w p} ℤ`. The normalized coefficient
objects are `ULift.{max w b p} A` and `ULift.{max w a p} B`, not the raw outer
lifts of the tensor groups.

Simultaneously changing the simplicial set and the coefficient group gives the
coproduct map with index function `SSet.mapπ₀` and the lifted coefficient map on
each summand. The mixed formula is proved on raw degree-zero tensor generators;
it does not require a separate simplicial-naturality theorem.

## References and attribution

Mathlib's degree-zero homology and simplicial component constructions, notably
by Joël Riou, supply the component isomorphism and coproduct API. The integral
tensor comparison and coefficient maps of `SimplicialObjects.TensorCoefficients`
and `SimplicialObjects.TensorCoefficientMaps` supply the tensor generator and
mixed chain-map formulas. The vertex class formula of
`SimplicialObjects.TensorHomologyZero` identifies their homology classes.
-/

@[expose] public section

universe a b w p

open CategoryTheory Limits Opposite
open scoped Simplicial TensorProduct

namespace SSet

variable {A : Type a} {B : Type b} [AddCommGroup A] [AddCommGroup B]

/-- Simultaneous simplicial and coefficient naturality of the component
isomorphism, with independent coefficient universes and balanced padding.
The target is the stock coproduct map with index function `mapπ₀ φ` and the
lift of the additive coefficient homomorphism on every summand. -/
theorem tensorNormalizedHomologyZeroIsoComponents_hom_mixed_naturality
    {S T : SSet.{w}} (φ : S ⟶ T) (f : A →+ B) :
    HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexMap.{a, w, max b p} A φ) 0 ≫
      HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} f T) 0 ≫
      (tensorNormalizedHomologyZeroIsoComponents.{b, w, max a p} B T).hom =
    (tensorNormalizedHomologyZeroIsoComponents.{a, w, max b p} A S).hom ≫
      CategoryTheory.Limits.Sigma.map'
        (f := fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w b p} A))
        (g := fun _ : π₀ T => ModuleCat.of ℤ (ULift.{max w a p} B))
        (mapπ₀ φ) (fun _ =>
          (ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
            f.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap) :
            ModuleCat.of ℤ (ULift.{max w b p} A) ⟶
              ModuleCat.of ℤ (ULift.{max w a p} B))) := by
  let KA := tensorNormalizedChainComplex.{a, w, max b p} A S
  let KB := tensorNormalizedChainComplex.{b, w, max a p} B T
  let eA := tensorNormalizedHomologyZeroIsoComponents.{a, w, max b p} A S
  let eB := tensorNormalizedHomologyZeroIsoComponents.{b, w, max a p} B T
  let u : ModuleCat.of ℤ (ULift.{max w b p} A) ⟶
      ModuleCat.of ℤ (ULift.{max w a p} B) :=
    ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
      f.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap)
  let k : KA ⟶ KB :=
    tensorNormalizedChainComplexMap.{a, w, max b p} A φ ≫
      tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} f T
  change HomologicalComplex.homologyMap
      (tensorNormalizedChainComplexMap.{a, w, max b p} A φ) 0 ≫
    HomologicalComplex.homologyMap
      (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} f T) 0 ≫ eB.hom =
    eA.hom ≫ CategoryTheory.Limits.Sigma.map'
        (f := fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w b p} A))
        (g := fun _ : π₀ T => ModuleCat.of ℤ (ULift.{max w a p} B))
        (mapπ₀ φ) (fun _ => u)
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp]
  change HomologicalComplex.homologyMap k 0 ≫ eB.hom =
    eA.hom ≫ CategoryTheory.Limits.Sigma.map'
        (f := fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w b p} A))
        (g := fun _ : π₀ T => ModuleCat.of ℤ (ULift.{max w a p} B))
        (mapπ₀ φ) (fun _ => u)
  apply (cancel_epi KA.homologyπ₀).1
  rw [← Category.assoc, ChainComplex.homologyπ₀_naturality]
  apply tensorNormalizedChainComplex_hom_ext.{a, w, max b p} A S 0
  intro s x
  let KT := tensorNormalizedChainComplex.{a, w, max b p} A T
  let zA : KA.X 0 := ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)
  let zT : KT.X 0 :=
    ULift.up (T.normalizedIntegralSimplex (φ.app (op ⦋0⦌) s.val) ⊗ₜ[ℤ] x)
  let zB : KB.X 0 :=
    ULift.up (T.normalizedIntegralSimplex (φ.app (op ⦋0⦌) s.val) ⊗ₜ[ℤ] f x)
  have hφ : (tensorNormalizedChainComplexMap.{a, w, max b p} A φ).f 0 zA = zT :=
    tensorNormalizedChainComplexMap_f_single.{a, w, max b p} A φ 0 s x
  have hf : (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} f T).f 0 zT = zB :=
    tensorNormalizedChainComplexCoefficientMap_f_simplex.{a, b, w, p}
      f T (φ.app (op ⦋0⦌) s.val) x
  have hk : k.f 0 zA = zB :=
    (ModuleCat.comp_apply
      ((tensorNormalizedChainComplexMap.{a, w, max b p} A φ).f 0)
      ((tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} f T).f 0) zA).trans
        ((congrArg (fun z : KT.X 0 =>
          (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} f T).f 0 z) hφ).trans hf)
  have hzA :
      (ULift.up (S.normalizedIntegralSimplex s.val ⊗ₜ[ℤ] x) : KA.X 0) = zA :=
    congrArg (fun z : S.nonDegenerate 0 →₀ ℤ =>
      (ULift.up (z ⊗ₜ[ℤ] x) : KA.X 0))
        (normalizedIntegralSimplex_of_mem_nonDegenerate S s.val s.property)
  have hA : eA.hom (KA.homologyπ₀ zA) =
      Sigma.ι (fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w b p} A))
        (π₀.mk s.val) (ULift.up x) :=
    (congrArg (fun z : KA.X 0 => eA.hom (KA.homologyπ₀ z)) hzA.symm).trans
      (tensorNormalizedHomologyZeroIsoComponents_hom_class.{a, w, max b p} A S s.val x)
  have hB : eB.hom (KB.homologyπ₀ zB) =
      Sigma.ι (fun _ : π₀ T => ModuleCat.of ℤ (ULift.{max w a p} B))
        (π₀.mk (φ.app (op ⦋0⦌) s.val)) (ULift.up (f x)) :=
    tensorNormalizedHomologyZeroIsoComponents_hom_class.{b, w, max a p}
      B T (φ.app (op ⦋0⦌) s.val) (f x)
  change eB.hom (KB.homologyπ₀ (k.f 0 zA)) =
    (CategoryTheory.Limits.Sigma.map'
        (f := fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w b p} A))
        (g := fun _ : π₀ T => ModuleCat.of ℤ (ULift.{max w a p} B))
        (mapπ₀ φ) (fun _ => u)) (eA.hom (KA.homologyπ₀ zA))
  rw [hk, hB, hA]
  change
    (Sigma.ι (fun _ : π₀ T => ModuleCat.of ℤ (ULift.{max w a p} B))
      (π₀.mk (φ.app (op ⦋0⦌) s.val))) (ULift.up (f x)) =
    (Sigma.ι (fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w b p} A)) (π₀.mk s.val) ≫
      CategoryTheory.Limits.Sigma.map'
        (f := fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w b p} A))
        (g := fun _ : π₀ T => ModuleCat.of ℤ (ULift.{max w a p} B))
        (mapπ₀ φ) (fun _ => u)) (ULift.up x)
  rw [Sigma.ι_comp_map', mapπ₀_mk]
  rfl

/-- The component isomorphism is natural in arbitrary additive coefficient
homomorphisms. The source and target use padding `max b p` and `max a p`,
respectively, so the coefficient universes need not agree. The map on components
is Mathlib's same-index coproduct map of the correctly lifted coefficient hom. -/
theorem tensorNormalizedHomologyZeroIsoComponents_hom_coefficient_naturality
    (f : A →+ B) (S : SSet.{w}) :
    HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} f S) 0 ≫
      (tensorNormalizedHomologyZeroIsoComponents.{b, w, max a p} B S).hom =
    (tensorNormalizedHomologyZeroIsoComponents.{a, w, max b p} A S).hom ≫
      CategoryTheory.Limits.Sigma.map
        (f := fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w b p} A))
        (g := fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w a p} B))
        (fun _ : π₀ S =>
          (ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
            f.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap) :
            ModuleCat.of ℤ (ULift.{max w b p} A) ⟶
              ModuleCat.of ℤ (ULift.{max w a p} B))) := by
  have hπ : mapπ₀ (𝟙 S) = id := funext (fun q => mapπ₀_id_apply q)
  simpa only [tensorNormalizedChainComplexMap_id, HomologicalComplex.homologyMap_id,
    Category.id_comp, hπ, Sigma.map'_id] using
    tensorNormalizedHomologyZeroIsoComponents_hom_mixed_naturality.{a, b, w, p} (𝟙 S) f

/-- The degree-zero homology maps for a simplicial map and an additive
coefficient map commute, without any restriction on the two coefficient
universes. This is the homology image of the existing mixed chain square. -/
theorem tensorNormalizedHomologyZeroCoefficientMap_naturality
    {S T : SSet.{w}} (φ : S ⟶ T) (f : A →+ B) :
    HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexMap.{a, w, max b p} A φ) 0 ≫
      HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} f T) 0 =
    HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} f S) 0 ≫
      HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexMap.{b, w, max a p} B φ) 0 := by
  have h := congrArg
    (fun k : tensorNormalizedChainComplex.{a, w, max b p} A S ⟶
        tensorNormalizedChainComplex.{b, w, max a p} B T =>
      HomologicalComplex.homologyMap k 0)
    (tensorNormalizedChainComplexCoefficientMap_naturality.{a, b, w, p} φ f)
  simpa only [HomologicalComplex.homologyMap_comp] using h

/-- Reindexing the coproduct along a simplicial map commutes with the lifted
coefficient homomorphism on every summand. These are stock coproduct maps in
the common integer-module category. -/
theorem tensorNormalizedHomologyZeroComponentCoefficientMap_naturality
    {S T : SSet.{w}} (φ : S ⟶ T) (f : A →+ B) :
    CategoryTheory.Limits.Sigma.map'
        (f := fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w b p} A))
        (g := fun _ : π₀ T => ModuleCat.of ℤ (ULift.{max w b p} A))
        (mapπ₀ φ) (fun _ => 𝟙 _) ≫
      CategoryTheory.Limits.Sigma.map
        (f := fun _ : π₀ T => ModuleCat.of ℤ (ULift.{max w b p} A))
        (g := fun _ : π₀ T => ModuleCat.of ℤ (ULift.{max w a p} B))
        (fun _ : π₀ T =>
          (ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
            f.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap) :
            ModuleCat.of ℤ (ULift.{max w b p} A) ⟶
              ModuleCat.of ℤ (ULift.{max w a p} B))) =
    CategoryTheory.Limits.Sigma.map
        (f := fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w b p} A))
        (g := fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w a p} B))
        (fun _ : π₀ S =>
          (ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
            f.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap) :
            ModuleCat.of ℤ (ULift.{max w b p} A) ⟶
              ModuleCat.of ℤ (ULift.{max w a p} B))) ≫
      CategoryTheory.Limits.Sigma.map'
        (f := fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w a p} B))
        (g := fun _ : π₀ T => ModuleCat.of ℤ (ULift.{max w a p} B))
        (mapπ₀ φ) (fun _ => 𝟙 _) := by
  simp only [Sigma.map'_comp_map, Sigma.map_comp_map', Category.id_comp, Category.comp_id]

end SSet
