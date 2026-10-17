/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorCoefficients

/-!
# Simplicial maps on integral tensor chains

A simplicial morphism sends an integral nondegenerate generator to the normalized
integral class of its image. That class can be zero: no preservation of
nondegenerate simplices is required. Tensoring this linear map with the identity
of an abelian coefficient group gives a map between the specified tensor degrees.

The whole chain map uses Mathlib's normalized-chain map and the chain comparisons
from `SimplicialObjects.TensorCoefficients`. Only morphisms are conjugated: the
integral generators, tensor carriers and independently defined alternating
boundary are unchanged. The component formula identifies this chain map with the
independently specified tensor-degree operation.

The coefficient, simplex and padding universes are independent. There are no
injectivity, finite-fiber, flatness or nonemptiness hypotheses. This construction
concerns normalized (degeneracy-quotient) chains, not unnormalized chains or a
comparison with singular chains of topological spaces.

## References

* May, *A Concise Course in Algebraic Topology*, revised edition, §16.1, motivates
  the integral tensor presentation of normalized chains.
* Mathlib supplies `SSet.normalizedChainComplexMap`, its all-simplex inclusion
  formula, `SSet.normalizedChainComplexFunctorObj`, `Finsupp.lift`,
  `LinearMap.rTensor` and `ULift.moduleEquiv`.
-/

@[expose] public section

universe a w p

open CategoryTheory Opposite
open scoped Simplicial TensorProduct

namespace SSet

variable {S T U : SSet.{w}}

/-- The integral degree map of a simplicial morphism, specified on nondegenerate
basis vectors by the normalized class of their images. -/
noncomputable def normalizedIntegralMap (f : S ⟶ T) (n : ℕ) :
    (S.nonDegenerate n →₀ ℤ) →ₗ[ℤ] (T.nonDegenerate n →₀ ℤ) :=
  Finsupp.lift _ ℤ _ fun s ↦ T.normalizedIntegralSimplex (f.app (op ⦋n⦌) s.val)

/-- An integral basis vector maps to the class of its image, possibly zero. -/
@[simp]
theorem normalizedIntegralMap_single (f : S ⟶ T) (n : ℕ)
    (s : S.nonDegenerate n) :
    normalizedIntegralMap f n (Finsupp.single s 1) =
      T.normalizedIntegralSimplex (f.app (op ⦋n⦌) s.val) := by
  classical
  simp [normalizedIntegralMap, Finsupp.lift_apply]

/-- The integral degree map takes the normalized class of every simplex to the
class of its image, including degenerate zero classes. -/
@[simp]
theorem normalizedIntegralMap_simplex (f : S ⟶ T) {n : ℕ} (s : S _⦋n⦌) :
    normalizedIntegralMap f n (S.normalizedIntegralSimplex s) =
      T.normalizedIntegralSimplex (f.app (op ⦋n⦌) s) := by
  classical
  by_cases hs : s ∈ S.nonDegenerate n
  · rw [S.normalizedIntegralSimplex_of_mem_nonDegenerate s hs]
    exact normalizedIntegralMap_single f n ⟨s, hs⟩
  · have hd := (S.mem_degenerate_iff_notMem_nonDegenerate s).mpr hs
    rw [S.normalizedIntegralSimplex_of_mem_degenerate s hd,
      T.normalizedIntegralSimplex_of_mem_degenerate _ (degenerate_app_apply hd f), map_zero]

/-- The image formula uniquely characterizes the integral degree map. -/
theorem normalizedIntegralMap_eq_iff (f : S ⟶ T) (n : ℕ)
    (g : (S.nonDegenerate n →₀ ℤ) →ₗ[ℤ] (T.nonDegenerate n →₀ ℤ)) :
    g = normalizedIntegralMap f n ↔ ∀ s : S.nonDegenerate n,
      g (Finsupp.single s 1) = T.normalizedIntegralSimplex (f.app (op ⦋n⦌) s.val) := by
  constructor
  · rintro rfl s
    exact normalizedIntegralMap_single f n s
  · intro h
    apply (Finsupp.lift (T.nonDegenerate n →₀ ℤ) ℤ (S.nonDegenerate n)).symm.injective
    funext s
    simpa only [Finsupp.lift_symm_apply, normalizedIntegralMap_single] using h s

/-- The degree map on integral tensor chains: tensor the integral map with the
coefficient identity, then lift to the common universe. -/
noncomputable def tensorNormalizedChainComplexXMap (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) (n : ℕ) :
    tensorNormalizedChainComplexX.{a, w, p} A S n ⟶
      tensorNormalizedChainComplexX.{a, w, p} A T n :=
  ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
    (normalizedIntegralMap f n).rTensor A ∘ₗ
      (ULift.moduleEquiv (R := ℤ)).toLinearMap)

/-- The tensor-degree map on a lifted pure tensor. -/
@[simp]
theorem tensorNormalizedChainComplexXMap_tmul (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) (n : ℕ) (z : S.nonDegenerate n →₀ ℤ) (x : A) :
    tensorNormalizedChainComplexXMap.{a, w, p} A f n (ULift.up (z ⊗ₜ[ℤ] x)) =
      ULift.up (normalizedIntegralMap f n z ⊗ₜ[ℤ] x) := rfl

/-- The tensor-degree map sends a basis tensor to the image simplex class tensored
with the same coefficient; a degenerate image contributes zero. -/
@[simp]
theorem tensorNormalizedChainComplexXMap_single (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) (n : ℕ) (s : S.nonDegenerate n) (x : A) :
    tensorNormalizedChainComplexXMap.{a, w, p} A f n
        (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
      ULift.up (T.normalizedIntegralSimplex (f.app (op ⦋n⦌) s.val) ⊗ₜ[ℤ] x) := by
  rw [tensorNormalizedChainComplexXMap_tmul, normalizedIntegralMap_single]

/-- The tensor-degree image formula holds for every simplex class. -/
@[simp]
theorem tensorNormalizedChainComplexXMap_simplex (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) {n : ℕ} (s : S _⦋n⦌) (x : A) :
    tensorNormalizedChainComplexXMap.{a, w, p} A f n
        (ULift.up (S.normalizedIntegralSimplex s ⊗ₜ[ℤ] x)) =
      ULift.up (T.normalizedIntegralSimplex (f.app (op ⦋n⦌) s) ⊗ₜ[ℤ] x) := by
  rw [tensorNormalizedChainComplexXMap_tmul, normalizedIntegralMap_simplex]

/-- The basis-tensor formula uniquely characterizes the tensor-degree map. -/
theorem tensorNormalizedChainComplexXMap_eq_iff (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) (n : ℕ)
    (g : tensorNormalizedChainComplexX.{a, w, p} A S n ⟶
      tensorNormalizedChainComplexX.{a, w, p} A T n) :
    g = tensorNormalizedChainComplexXMap.{a, w, p} A f n ↔
      ∀ (s : S.nonDegenerate n) (x : A),
        g (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
          ULift.up (T.normalizedIntegralSimplex (f.app (op ⦋n⦌) s.val) ⊗ₜ[ℤ] x) := by
  constructor
  · rintro rfl s x
    exact tensorNormalizedChainComplexXMap_single.{a, w, p} A f n s x
  · intro h
    apply tensorNormalizedChainComplexX_hom_ext.{a, w, p} A S n
    intro s x
    exact (h s x).trans (tensorNormalizedChainComplexXMap_single.{a, w, p} A f n s x).symm

/-- The whole tensor chain map induced by a simplicial morphism, using the
normalized-chain map between the existing chain comparisons. The tensor complex
and its boundary are not defined by this conjugation. -/
noncomputable def tensorNormalizedChainComplexMap (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) :
    tensorNormalizedChainComplex.{a, w, p} A S ⟶
      tensorNormalizedChainComplex.{a, w, p} A T :=
  (tensorNormalizedChainIso.{a, w, p} A S).hom ≫
    normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A)) ≫
      (tensorNormalizedChainIso.{a, w, p} A T).inv

/-- The whole map is characterized by its conjugation formula. -/
theorem tensorNormalizedChainComplexMap_eq (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) :
    tensorNormalizedChainComplexMap.{a, w, p} A f =
      (tensorNormalizedChainIso.{a, w, p} A S).hom ≫
        normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A)) ≫
          (tensorNormalizedChainIso.{a, w, p} A T).inv := rfl

/-- The whole tensor chain map preserves identities. -/
@[simp]
theorem tensorNormalizedChainComplexMap_id (A : Type a) [AddCommGroup A] (S : SSet.{w}) :
    tensorNormalizedChainComplexMap.{a, w, p} A (𝟙 S) =
      𝟙 (tensorNormalizedChainComplex.{a, w, p} A S) := by
  have h := (normalizedChainComplexFunctorObj (ModuleCat.of ℤ (ULift.{max w p} A))).map_id S
  change normalizedChainComplexMap (𝟙 S) (ModuleCat.of ℤ (ULift.{max w p} A)) = 𝟙 _ at h
  rw [tensorNormalizedChainComplexMap_eq, h, Category.id_comp, Iso.hom_inv_id]

/-- The whole tensor chain map preserves composition. -/
@[simp]
theorem tensorNormalizedChainComplexMap_comp (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) (g : T ⟶ U) :
    tensorNormalizedChainComplexMap.{a, w, p} A (f ≫ g) =
      tensorNormalizedChainComplexMap.{a, w, p} A f ≫
        tensorNormalizedChainComplexMap.{a, w, p} A g := by
  have h := (normalizedChainComplexFunctorObj (ModuleCat.of ℤ (ULift.{max w p} A))).map_comp f g
  change normalizedChainComplexMap (f ≫ g) (ModuleCat.of ℤ (ULift.{max w p} A)) =
    normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A)) ≫
      normalizedChainComplexMap g (ModuleCat.of ℤ (ULift.{max w p} A)) at h
  simp only [tensorNormalizedChainComplexMap_eq, h, Category.assoc, Iso.inv_hom_id_assoc]

/-- Integral tensor chains as a functor on simplicial sets with fixed abelian
coefficients, retaining the independently defined alternating boundary. -/
noncomputable def tensorNormalizedChainComplexFunctor (A : Type a) [AddCommGroup A] :
    SSet.{w} ⥤ ChainComplex (ModuleCat.{max a w p} ℤ) ℕ where
  obj S := tensorNormalizedChainComplex.{a, w, p} A S
  map f := tensorNormalizedChainComplexMap.{a, w, p} A f
  map_id S := tensorNormalizedChainComplexMap_id.{a, w, p} A S
  map_comp f g := tensorNormalizedChainComplexMap_comp.{a, w, p} A f g

/-- The tensor-chain functor has the specified tensor complex as its object. -/
@[simp]
theorem tensorNormalizedChainComplexFunctor_obj (A : Type a) [AddCommGroup A] (S : SSet.{w}) :
    (tensorNormalizedChainComplexFunctor.{a, w, p} A).obj S =
      tensorNormalizedChainComplex.{a, w, p} A S := rfl

/-- The tensor-chain functor acts by the constructed whole chain map. -/
@[simp]
theorem tensorNormalizedChainComplexFunctor_map (A : Type a) [AddCommGroup A] (f : S ⟶ T) :
    (tensorNormalizedChainComplexFunctor.{a, w, p} A).map f =
      tensorNormalizedChainComplexMap.{a, w, p} A f := rfl

/-- The degree comparison intertwines the independently specified tensor-degree
map with the normalized-chain map, including maps with degenerate images. -/
theorem tensorNormalizedChainComplexXIso_hom_naturality (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) (n : ℕ) :
    (tensorNormalizedChainComplexXIso.{a, w, p} A S n).hom ≫
        (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A))).f n =
      tensorNormalizedChainComplexXMap.{a, w, p} A f n ≫
        (tensorNormalizedChainComplexXIso.{a, w, p} A T n).hom := by
  apply tensorNormalizedChainComplexX_hom_ext.{a, w, p} A S n
  intro s x
  change
    ((normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A))).f n).hom
        ((tensorNormalizedChainComplexXIso.{a, w, p} A S n).hom.hom
          (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x))) =
      (tensorNormalizedChainComplexXIso.{a, w, p} A T n).hom.hom
        ((tensorNormalizedChainComplexXMap.{a, w, p} A f n).hom
          (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)))
  refine (congrArg
    (fun z : (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X n ↦
      ((normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A))).f n).hom z)
    (tensorNormalizedChainComplexXIso_hom_single.{a, w, p} A S n s x)).trans ?_
  refine (congrArg
    (fun g : ModuleCat.of ℤ (ULift.{max w p} A) ⟶
        (T.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X n ↦
      g.hom (ULift.up x))
    (ι_normalizedChainComplexMap_f f (ModuleCat.of ℤ (ULift.{max w p} A)) s.val)).trans ?_
  exact (tensorNormalizedChainComplexXIso_hom_simplex.{a, w, p} A T
    (f.app (op ⦋n⦌) s.val) x).symm.trans
      (congrArg
        (fun z : tensorNormalizedChainComplexX.{a, w, p} A T n ↦
          (tensorNormalizedChainComplexXIso.{a, w, p} A T n).hom.hom z)
        (tensorNormalizedChainComplexXMap_single.{a, w, p} A f n s x).symm)

/-- The raw tensor-degree maps commute with the independently specified tensor
differentials in every bidegree. -/
theorem tensorNormalizedChainComplexXMap_d (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) (i j : ℕ) :
    tensorNormalizedChainComplexXMap.{a, w, p} A f i ≫
        tensorNormalizedDifferential.{a, w, p} A T i j =
      tensorNormalizedDifferential.{a, w, p} A S i j ≫
        tensorNormalizedChainComplexXMap.{a, w, p} A f j := by
  apply (cancel_mono (tensorNormalizedChainComplexXIso.{a, w, p} A T j).hom).mp
  simp only [Category.assoc]
  rw [← tensorNormalizedChainComplexXIso_hom_d.{a, w, p} A T i j,
    ← Category.assoc,
    ← tensorNormalizedChainComplexXIso_hom_naturality.{a, w, p} A f i,
    Category.assoc,
    (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A))).comm i j,
    ← Category.assoc,
    tensorNormalizedChainComplexXIso_hom_d.{a, w, p} A S i j,
    Category.assoc,
    tensorNormalizedChainComplexXIso_hom_naturality.{a, w, p} A f j]

/-- Each component of the whole chain map is the independently specified raw
tensor-degree map, not merely a map on normalized coordinates. -/
theorem tensorNormalizedChainComplexMap_f (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) (n : ℕ) :
    (tensorNormalizedChainComplexMap.{a, w, p} A f).f n =
      tensorNormalizedChainComplexXMap.{a, w, p} A f n := by
  simp only [tensorNormalizedChainComplexMap_eq, HomologicalComplex.comp_f,
    tensorNormalizedChainIso_hom_f, tensorNormalizedChainIso_inv_f]
  change
    ((tensorNormalizedChainComplexXIso.{a, w, p} A S n).hom ≫
      (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A))).f n ≫
        (tensorNormalizedChainComplexXIso.{a, w, p} A T n).inv :
      tensorNormalizedChainComplexX.{a, w, p} A S n ⟶
        tensorNormalizedChainComplexX.{a, w, p} A T n) =
      tensorNormalizedChainComplexXMap.{a, w, p} A f n
  rw [← Category.assoc]
  exact ((tensorNormalizedChainComplexXIso.{a, w, p} A T n).comp_inv_eq).2
    (tensorNormalizedChainComplexXIso_hom_naturality.{a, w, p} A f n)

/-- The whole chain comparison is natural for arbitrary simplicial morphisms. -/
theorem tensorNormalizedChainIso_hom_naturality (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) :
    (tensorNormalizedChainIso.{a, w, p} A S).hom ≫
        normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A)) =
      (tensorNormalizedChainComplexFunctor.{a, w, p} A).map f ≫
        (tensorNormalizedChainIso.{a, w, p} A T).hom := by
  simp only [tensorNormalizedChainComplexFunctor_map]
  change
    ((tensorNormalizedChainIso.{a, w, p} A S).hom ≫
        normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A)) :
      tensorNormalizedChainComplex.{a, w, p} A S ⟶
        T.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))) =
      tensorNormalizedChainComplexMap.{a, w, p} A f ≫
        (tensorNormalizedChainIso.{a, w, p} A T).hom
  exact (Iso.comp_inv_eq (tensorNormalizedChainIso.{a, w, p} A T)).mp
    ((Category.assoc
      (tensorNormalizedChainIso.{a, w, p} A S).hom
      (normalizedChainComplexMap f (ModuleCat.of ℤ (ULift.{max w p} A)))
      (tensorNormalizedChainIso.{a, w, p} A T).inv).trans
        (tensorNormalizedChainComplexMap_eq.{a, w, p} A f).symm)

end SSet
