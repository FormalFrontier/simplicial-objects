/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorCoefficients
public import SimplicialObjects.TensorMaps
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Flat.Basic

/-!
# Change of coefficients in integral tensor chains

An additive homomorphism acts on each tensor degree by the identity on integral
simplex classes tensored with the coefficient homomorphism. The coefficient,
simplex and padding universes are independent. The source uses padding `max b p`
and the target uses padding `max a p`, so both raw lifts have level `max a b w p`.

The chain morphism is the existing normalized coefficient morphism conjugated by
`SSet.tensorNormalizedChainIso`. Neither the tensor carrier nor its independently
specified alternating boundary is changed. An exact pair of additive coefficient
homomorphisms induces an exact pair in every tensor degree, for every simplicial
set. Only the free integral first factor is required to be flat; the coefficient
groups are arbitrary.

## Implementation notes

The component formula identifies the chain morphism with the raw tensor operation.
The comparison is natural in coefficients, and the raw tensor operation commutes
with the independently specified alternating boundary. Composition uses extra
common padding for the third coefficient universe, including in every normalized
coefficient lift.

## References

* Mathlib supplies `AddMonoidHom.toIntLinearMap`, `LinearMap.lTensor`,
  `ULift.moduleEquiv`, and the normalized complexes.
  Its `LinearMap.lTensor_comp_rTensor` and `LinearMap.rTensor_comp_lTensor` identify
  both orders of the two tensor factors' operations with `TensorProduct.map`.
  Exactness uses `Module.Flat.finsupp` and `Module.Flat.lTensor_exact`, followed by
  `Function.Exact.of_ladder_linearEquiv_of_exact` for the outer lifts.
* `SimplicialObjects.Normalization` supplies the normalized morphism for arbitrary
  coefficient-valued simplicial maps and its coefficient action.
* May, *A Concise Course in Algebraic Topology*, revised edition, §16.1 motivates
  normalized chains as the quotient by degenerate simplices.
-/

@[expose] public section

universe a b c w p

open CategoryTheory Limits Opposite
open scoped Simplicial TensorProduct

namespace SSet

variable {A : Type a} {B : Type b} {C : Type c}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- The identity on integral simplex classes tensored with an additive coefficient
homomorphism, with balanced source and target padding. -/
noncomputable def tensorNormalizedCoefficientMap (g : A →+ B) (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedChainComplexX.{a, w, max b p} A S n ⟶
      tensorNormalizedChainComplexX.{b, w, max a p} B S n :=
  ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
    g.toIntLinearMap.lTensor (S.nonDegenerate n →₀ ℤ) ∘ₗ
      (ULift.moduleEquiv (R := ℤ)).toLinearMap)

/-- The coefficient operation on an arbitrary lifted pure tensor. -/
@[simp]
theorem tensorNormalizedCoefficientMap_tmul (g : A →+ B) (S : SSet.{w}) (n : ℕ)
    (z : S.nonDegenerate n →₀ ℤ) (x : A) :
    tensorNormalizedCoefficientMap.{a, b, w, p} g S n (ULift.up (z ⊗ₜ[ℤ] x)) =
      ULift.up (z ⊗ₜ[ℤ] g x) := rfl

/-- Integral generators keep their simplex and change only their coefficient. -/
@[simp]
theorem tensorNormalizedCoefficientMap_single (g : A →+ B) (S : SSet.{w}) (n : ℕ)
    (s : S.nonDegenerate n) (x : A) :
    tensorNormalizedCoefficientMap.{a, b, w, p} g S n
        (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
      ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] g x) :=
  tensorNormalizedCoefficientMap_tmul g S n _ x

/-- The same formula applies to every simplex, including degenerate zero classes. -/
@[simp]
theorem tensorNormalizedCoefficientMap_simplex (g : A →+ B) (S : SSet.{w})
    {n : ℕ} (s : S _⦋n⦌) (x : A) :
    tensorNormalizedCoefficientMap.{a, b, w, p} g S n
        (ULift.up (S.normalizedIntegralSimplex s ⊗ₜ[ℤ] x)) =
      ULift.up (S.normalizedIntegralSimplex s ⊗ₜ[ℤ] g x) :=
  tensorNormalizedCoefficientMap_tmul g S n _ x

/-- The generator formula uniquely characterizes the degree operation. -/
theorem tensorNormalizedCoefficientMap_eq_iff (g : A →+ B) (S : SSet.{w}) (n : ℕ)
    (f : tensorNormalizedChainComplexX.{a, w, max b p} A S n ⟶
      tensorNormalizedChainComplexX.{b, w, max a p} B S n) :
    f = tensorNormalizedCoefficientMap.{a, b, w, p} g S n ↔
      ∀ (s : S.nonDegenerate n) (x : A),
        f (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
          ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] g x) := by
  constructor
  · rintro rfl s x
    exact tensorNormalizedCoefficientMap_single g S n s x
  · intro h
    apply tensorNormalizedChainComplexX_hom_ext.{a, w, max b p} A S n
    intro s x
    exact (h s x).trans (tensorNormalizedCoefficientMap_single g S n s x).symm

/-- Identity coefficients give the identity on the balanced degree. -/
@[simp]
theorem tensorNormalizedCoefficientMap_id (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedCoefficientMap.{a, a, w, p} (AddMonoidHom.id A) S n = 𝟙 _ := by
  apply tensorNormalizedChainComplexX_hom_ext.{a, w, max a p} A S n
  intro s x
  rfl

/-- Coefficient operations compose with a common padding for all three universes. -/
theorem tensorNormalizedCoefficientMap_comp (g : A →+ B) (h : B →+ C)
    (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedCoefficientMap.{a, c, w, max b p} (h.comp g) S n =
      tensorNormalizedCoefficientMap.{a, b, w, max c p} g S n ≫
        tensorNormalizedCoefficientMap.{b, c, w, max a p} h S n := by
  apply tensorNormalizedChainComplexX_hom_ext.{a, w, max c (max b p)} A S n
  intro s x
  rfl

/-- The zero coefficient homomorphism gives the zero degree morphism. -/
@[simp]
theorem tensorNormalizedCoefficientMap_zero (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedCoefficientMap.{a, b, w, p} (0 : A →+ B) S n = 0 := by
  apply tensorNormalizedChainComplexX_hom_ext.{a, w, max b p} A S n
  intro s x
  simp only [tensorNormalizedCoefficientMap_single, AddMonoidHom.zero_apply,
    TensorProduct.tmul_zero]
  rfl

/-- The degree coefficient operation is additive in the coefficient homomorphism,
with independent coefficient, simplex and padding universes.

This is the balanced `ULift` form of `LinearMap.lTensor_add`, following Mathlib's
formalization of tensoring linear maps. -/
theorem tensorNormalizedCoefficientMap_add (g h : A →+ B) (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedCoefficientMap.{a, b, w, p} (g + h) S n =
      tensorNormalizedCoefficientMap.{a, b, w, p} g S n +
        tensorNormalizedCoefficientMap.{a, b, w, p} h S n := by
  have hadd : (g + h).toIntLinearMap = g.toIntLinearMap + h.toIntLinearMap := by
    ext x
    rfl
  simp only [tensorNormalizedCoefficientMap, hadd, LinearMap.lTensor_add]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

/-- Exact coefficient homomorphisms give an exact pair of normalized tensor degree maps.

The first tensor factor `S.nonDegenerate n →₀ ℤ` is free, so Mathlib's
`Module.Flat.lTensor_exact` supplies exactness before conjugation by the outer
`ULift.moduleEquiv` maps. May, *A Concise Course in Algebraic Topology*, §16.1
motivates this normalized integral presentation; the tensor exactness statement
uses Mathlib's flat-module theorem. -/
theorem tensorNormalizedCoefficientMap_exact (g : A →+ B) (h : B →+ C)
    (hExact : Function.Exact g h) (S : SSet.{w}) (n : ℕ) :
    Function.Exact
      (tensorNormalizedCoefficientMap.{a, b, w, max c p} g S n)
      (tensorNormalizedCoefficientMap.{b, c, w, max a p} h S n) := by
  have hLinear : Function.Exact g.toIntLinearMap h.toIntLinearMap := by
    simpa only [AddMonoidHom.coe_toIntLinearMap] using hExact
  have hTensor := Module.Flat.lTensor_exact (S.nonDegenerate n →₀ ℤ) hLinear
  -- The ladder uses only the existing outer lifts; coefficients inside the tensors
  -- retain their original canonical integer actions.
  exact Function.Exact.of_ladder_linearEquiv_of_exact
    (g₁₂ := (tensorNormalizedCoefficientMap.{a, b, w, max c p} g S n).hom)
    (g₂₃ := (tensorNormalizedCoefficientMap.{b, c, w, max a p} h S n).hom)
    (e₁ := (ULift.moduleEquiv (R := ℤ)).symm)
    (e₂ := (ULift.moduleEquiv (R := ℤ)).symm)
    (e₃ := (ULift.moduleEquiv (R := ℤ)).symm)
    (by apply LinearMap.ext; intro z; rfl)
    (by apply LinearMap.ext; intro z; rfl) hTensor

private noncomputable def liftedCoefficientMap (g : A →+ B) :
    ModuleCat.of ℤ (ULift.{max w b} A) ⟶
      ModuleCat.of ℤ (ULift.{max w a} B) :=
  ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
    g.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap)

/-- The normalized coefficient morphism, conjugated by the integral tensor
comparison. Only the morphism is conjugated; the tensor differential is unchanged. -/
@[no_expose]
noncomputable def tensorNormalizedChainComplexCoefficientMap (g : A →+ B) (S : SSet.{w}) :
    tensorNormalizedChainComplex.{a, w, max b p} A S ⟶
      tensorNormalizedChainComplex.{b, w, max a p} B S :=
  (tensorNormalizedChainIso.{a, w, max b p} A S).hom ≫
    (S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w b p} A)))).nondegComplexMap
      (S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w a p} B))))
      (Functor.whiskerLeft S (sigmaConst.map (liftedCoefficientMap.{a, b, max w p} g))) ≫
    (tensorNormalizedChainIso.{b, w, max a p} B S).inv

/-- On a nondegenerate tensor generator, the chain morphism changes only the coefficient. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientMap_f_single (g : A →+ B) (S : SSet.{w})
    (n : ℕ) (s : S.nonDegenerate n) (x : A) :
    (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S).f n
        (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
      ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] g x) := by
  have hk := S.ιNormalizedChainComplex_nondegComplexMap_coefficient
    (R := ModuleCat.of ℤ (ULift.{max w b p} A))
    (liftedCoefficientMap.{a, b, max w p} g) s.val
  have hv := congrArg
    (fun f : ModuleCat.of ℤ (ULift.{max w b p} A) ⟶
      (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w a p} B))).X n ↦
        f (ULift.up x)) hk
  change
    ((S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w b p} A)))).nondegComplexMap
      (S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w a p} B))))
      (Functor.whiskerLeft S (sigmaConst.map (liftedCoefficientMap.{a, b, max w p} g)))).f n
        (S.ιNormalizedChainComplex
          (R := ModuleCat.of ℤ (ULift.{max w b p} A)) s.val (ULift.up x)) =
      S.ιNormalizedChainComplex
        (R := ModuleCat.of ℤ (ULift.{max w a p} B)) s.val (ULift.up (g x)) at hv
  change (tensorNormalizedChainIso.{b, w, max a p} B S).inv.f n
    (((S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w b p} A)))).nondegComplexMap
      (S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w a p} B))))
      (Functor.whiskerLeft S (sigmaConst.map (liftedCoefficientMap.{a, b, max w p} g)))).f n
        ((tensorNormalizedChainIso.{a, w, max b p} A S).hom.f n
          (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)))) = _
  have hA : (tensorNormalizedChainIso.{a, w, max b p} A S).hom.f n
      (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
        S.ιNormalizedChainComplex
          (R := ModuleCat.of ℤ (ULift.{max w b p} A)) s.val (ULift.up x) :=
    tensorNormalizedChainComplexXIso_hom_single.{a, w, max b p} A S n s x
  rw [hA, hv]
  exact tensorNormalizedChainIso_inv_f_ι.{b, w, max a p} B S n s (g x)

/-- The generator formula uniquely characterizes the chain coefficient morphism. -/
theorem tensorNormalizedChainComplexCoefficientMap_eq_iff (g : A →+ B) (S : SSet.{w})
    (f : tensorNormalizedChainComplex.{a, w, max b p} A S ⟶
      tensorNormalizedChainComplex.{b, w, max a p} B S) :
    f = tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S ↔
      ∀ (n : ℕ) (s : S.nonDegenerate n) (x : A),
        f.f n (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
          ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] g x) := by
  constructor
  · rintro rfl n s x
    exact tensorNormalizedChainComplexCoefficientMap_f_single g S n s x
  · intro h
    ext n : 1
    apply tensorNormalizedChainComplex_hom_ext.{a, w, max b p} A S n
    intro s x
    exact (h n s x).trans
      (tensorNormalizedChainComplexCoefficientMap_f_single g S n s x).symm

/-- Identity coefficients give the identity chain morphism. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientMap_id (S : SSet.{w}) :
    tensorNormalizedChainComplexCoefficientMap.{a, a, w, p} (AddMonoidHom.id A) S = 𝟙 _ := by
  symm
  apply (tensorNormalizedChainComplexCoefficientMap_eq_iff.{a, a, w, p}
    (AddMonoidHom.id A) S (𝟙 _)).2
  intro n s x
  rfl

/-- Chain coefficient morphisms compose with balanced common padding. -/
theorem tensorNormalizedChainComplexCoefficientMap_comp (g : A →+ B) (h : B →+ C)
    (S : SSet.{w}) :
    tensorNormalizedChainComplexCoefficientMap.{a, c, w, max b p} (h.comp g) S =
      tensorNormalizedChainComplexCoefficientMap.{a, b, w, max c p} g S ≫
        tensorNormalizedChainComplexCoefficientMap.{b, c, w, max a p} h S := by
  symm
  apply (tensorNormalizedChainComplexCoefficientMap_eq_iff.{a, c, w, max b p}
    (h.comp g) S
    (tensorNormalizedChainComplexCoefficientMap.{a, b, w, max c p} g S ≫
      tensorNormalizedChainComplexCoefficientMap.{b, c, w, max a p} h S)).2
  intro n s x
  let u :
      ModuleCat.of ℤ (ULift.{max a b c w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] A)) ⟶
        ModuleCat.of ℤ (ULift.{max a b c w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] B)) :=
    (tensorNormalizedChainComplexCoefficientMap.{a, b, w, max c p} g S).f n
  let v :
      ModuleCat.of ℤ (ULift.{max a b c w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] B)) ⟶
        ModuleCat.of ℤ (ULift.{max a b c w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] C)) :=
    (tensorNormalizedChainComplexCoefficientMap.{b, c, w, max a p} h S).f n
  let z : ULift.{max a b c w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] A) :=
    ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)
  have hu : u z = ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] g x) :=
    tensorNormalizedChainComplexCoefficientMap_f_single.{a, b, w, max c p} g S n s x
  have hv : v (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] g x)) =
      ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] h (g x)) :=
    tensorNormalizedChainComplexCoefficientMap_f_single.{b, c, w, max a p} h S n s (g x)
  simp only [HomologicalComplex.comp_f]
  exact (ModuleCat.comp_apply u v z).trans
    ((congrArg
      (fun y : ULift.{max a b c w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] B) ↦ v y)
      hu).trans hv)

/-! ## Compatibility with the tensor comparison and boundary -/

/-- The conjugated chain morphism has the independently defined raw degree operation
as each component. -/
theorem tensorNormalizedChainComplexCoefficientMap_f (g : A →+ B) (S : SSet.{w}) (n : ℕ) :
    (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S).f n =
      tensorNormalizedCoefficientMap.{a, b, w, p} g S n := by
  apply tensorNormalizedChainComplexX_hom_ext.{a, w, max b p} A S n
  intro s x
  exact (tensorNormalizedChainComplexCoefficientMap_f_single.{a, b, w, p}
    g S n s x).trans
      (tensorNormalizedCoefficientMap_single.{a, b, w, p} g S n s x).symm

/-- Chain coefficient morphisms are additive in the coefficient homomorphism,
with independent coefficient, simplex and padding universes. -/
theorem tensorNormalizedChainComplexCoefficientMap_add (g h : A →+ B) (S : SSet.{w}) :
    tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} (g + h) S =
      tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S +
        tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} h S := by
  ext n : 1
  refine Eq.trans
    (tensorNormalizedChainComplexCoefficientMap_f.{a, b, w, p} (g + h) S n) ?_
  refine Eq.trans (tensorNormalizedCoefficientMap_add.{a, b, w, p} g h S n) ?_
  refine Eq.trans
    (congrArg₂ (· + ·)
      (tensorNormalizedChainComplexCoefficientMap_f.{a, b, w, p} g S n).symm
      (tensorNormalizedChainComplexCoefficientMap_f.{a, b, w, p} h S n).symm) ?_
  exact (HomologicalComplex.add_f_apply
    (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S)
    (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} h S) n).symm

/-- The whole integral tensor comparison is natural in coefficients, using the
corresponding padded coefficient lifts on normalized chains. -/
theorem tensorNormalizedChainComplexCoefficientMap_comparison (g : A →+ B) (S : SSet.{w}) :
    tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S ≫
        (tensorNormalizedChainIso.{b, w, max a p} B S).hom =
      (tensorNormalizedChainIso.{a, w, max b p} A S).hom ≫
        (S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w b p} A)))).nondegComplexMap
          (S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w a p} B))))
          (Functor.whiskerLeft S (sigmaConst.map
            (ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
              g.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap)))) := by
  let eA :
      tensorNormalizedChainComplex.{a, w, max b p} A S ≅
        S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w b p} A)) :=
    tensorNormalizedChainIso.{a, w, max b p} A S
  let eB :
      tensorNormalizedChainComplex.{b, w, max a p} B S ≅
        S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w a p} B)) :=
    tensorNormalizedChainIso.{b, w, max a p} B S
  let N :
      S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w b p} A)) ⟶
        S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w a p} B)) :=
    (S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w b p} A)))).nondegComplexMap
      (S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w a p} B))))
      (Functor.whiskerLeft S (sigmaConst.map (liftedCoefficientMap.{a, b, max w p} g)))
  change (eA.hom ≫ N ≫ eB.inv) ≫ eB.hom = eA.hom ≫ N
  exact eB.eq_comp_inv.mp (Category.assoc eA.hom N eB.inv).symm

/-- The degree comparison is natural in the coefficient homomorphism. -/
theorem tensorNormalizedCoefficientMap_comparison (g : A →+ B) (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedCoefficientMap.{a, b, w, p} g S n ≫
        (tensorNormalizedChainComplexXIso.{b, w, max a p} B S n).hom =
      (tensorNormalizedChainComplexXIso.{a, w, max b p} A S n).hom ≫
        ((S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w b p} A)))).nondegComplexMap
          (S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w a p} B))))
          (Functor.whiskerLeft S (sigmaConst.map
            (ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
              g.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap))))).f n := by
  let u :
      ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] A)) ⟶
        ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] B)) :=
    (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S).f n
  let v :
      ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] B)) ⟶
        (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w a p} B))).X n :=
    (tensorNormalizedChainIso.{b, w, max a p} B S).hom.f n
  let iA :
      ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] A)) ⟶
        (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w b p} A))).X n :=
    (tensorNormalizedChainIso.{a, w, max b p} A S).hom.f n
  let k :
      (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w b p} A))).X n ⟶
        (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w a p} B))).X n :=
    ((S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w b p} A)))).nondegComplexMap
      (S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w a p} B))))
      (Functor.whiskerLeft S (sigmaConst.map
        (ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
          g.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap))))).f n
  have h : u ≫ v = iA ≫ k := congrArg
    (fun f : tensorNormalizedChainComplex.{a, w, max b p} A S ⟶
      S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w a p} B)) ↦
        (f.f n :
          ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] A)) ⟶
            (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w a p} B))).X n))
    (tensorNormalizedChainComplexCoefficientMap_comparison.{a, b, w, p} g S)
  have hu : u = tensorNormalizedCoefficientMap.{a, b, w, p} g S n :=
    tensorNormalizedChainComplexCoefficientMap_f.{a, b, w, p} g S n
  have hv : v = (tensorNormalizedChainComplexXIso.{b, w, max a p} B S n).hom :=
    tensorNormalizedChainIso_hom_f.{b, w, max a p} B S n
  have hiA : iA = (tensorNormalizedChainComplexXIso.{a, w, max b p} A S n).hom :=
    tensorNormalizedChainIso_hom_f.{a, w, max b p} A S n
  rw [hu, hv, hiA] at h
  exact h

/-- The raw coefficient operation commutes with the independently specified
alternating tensor boundary. -/
theorem tensorNormalizedCoefficientMap_boundary (g : A →+ B) (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedBoundary.{a, w, max b p} A S n ≫
        tensorNormalizedCoefficientMap.{a, b, w, p} g S n =
      tensorNormalizedCoefficientMap.{a, b, w, p} g S (n + 1) ≫
        tensorNormalizedBoundary.{b, w, max a p} B S n := by
  let u :
      ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] A)) ⟶
        ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] B)) :=
    (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S).f n
  let v :
      ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate (n + 1) →₀ ℤ) ⊗[ℤ] A)) ⟶
        ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate (n + 1) →₀ ℤ) ⊗[ℤ] B)) :=
    (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S).f (n + 1)
  let dA :
      ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate (n + 1) →₀ ℤ) ⊗[ℤ] A)) ⟶
        ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] A)) :=
    (tensorNormalizedChainComplex.{a, w, max b p} A S).d (n + 1) n
  let dB :
      ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate (n + 1) →₀ ℤ) ⊗[ℤ] B)) ⟶
        ModuleCat.of ℤ (ULift.{max a b w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] B)) :=
    (tensorNormalizedChainComplex.{b, w, max a p} B S).d (n + 1) n
  have h : dA ≫ u = v ≫ dB :=
    ((tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S).comm (n + 1) n).symm
  have hu : u = tensorNormalizedCoefficientMap.{a, b, w, p} g S n :=
    tensorNormalizedChainComplexCoefficientMap_f.{a, b, w, p} g S n
  have hv : v = tensorNormalizedCoefficientMap.{a, b, w, p} g S (n + 1) :=
    tensorNormalizedChainComplexCoefficientMap_f.{a, b, w, p} g S (n + 1)
  have hdA : dA = tensorNormalizedBoundary.{a, w, max b p} A S n :=
    (tensorNormalizedChainComplex_d.{a, w, max b p} A S (n + 1) n).trans
      (tensorNormalizedDifferential_succ.{a, w, max b p} A S n)
  have hdB : dB = tensorNormalizedBoundary.{b, w, max a p} B S n :=
    (tensorNormalizedChainComplex_d.{b, w, max a p} B S (n + 1) n).trans
      (tensorNormalizedDifferential_succ.{b, w, max a p} B S n)
  rw [hu, hv, hdA, hdB] at h
  exact h

/-! ## Simultaneous simplicial and coefficient naturality -/

/-- Changing coefficients commutes with the raw tensor-degree map of any simplicial
morphism. The coefficient universes are independent, with balanced padding on both
sides; images of nondegenerate simplices may be degenerate. -/
theorem tensorNormalizedCoefficientMap_naturality {S T : SSet.{w}} (f : S ⟶ T)
    (g : A →+ B) (n : ℕ) :
    tensorNormalizedChainComplexXMap.{a, w, max b p} A f n ≫
        tensorNormalizedCoefficientMap.{a, b, w, p} g T n =
      tensorNormalizedCoefficientMap.{a, b, w, p} g S n ≫
        tensorNormalizedChainComplexXMap.{b, w, max a p} B f n := by
  apply tensorNormalizedChainComplexX_hom_ext.{a, w, max b p} A S n
  intro s x
  change
    (tensorNormalizedCoefficientMap.{a, b, w, p} g T n).hom
        ((tensorNormalizedChainComplexXMap.{a, w, max b p} A f n).hom
          (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x))) =
      (tensorNormalizedChainComplexXMap.{b, w, max a p} B f n).hom
        ((tensorNormalizedCoefficientMap.{a, b, w, p} g S n).hom
          (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)))
  have hleft :
      (tensorNormalizedCoefficientMap.{a, b, w, p} g T n).hom
          ((tensorNormalizedChainComplexXMap.{a, w, max b p} A f n).hom
            (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x))) =
        (ULift.up (normalizedIntegralMap f n (Finsupp.single s 1) ⊗ₜ[ℤ] g x) :
          ULift.{max a b w p} ((T.nonDegenerate n →₀ ℤ) ⊗[ℤ] B)) :=
    (congrArg
      (fun z : ULift.{max a b w p} ((T.nonDegenerate n →₀ ℤ) ⊗[ℤ] A) ↦
        (tensorNormalizedCoefficientMap.{a, b, w, p} g T n).hom z)
      (tensorNormalizedChainComplexXMap_tmul.{a, w, max b p}
        A f n (Finsupp.single s 1) x)).trans
      (tensorNormalizedCoefficientMap_tmul.{a, b, w, p}
        g T n (normalizedIntegralMap f n (Finsupp.single s 1)) x)
  have hright :
      (tensorNormalizedChainComplexXMap.{b, w, max a p} B f n).hom
          ((tensorNormalizedCoefficientMap.{a, b, w, p} g S n).hom
            (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x))) =
        (ULift.up (normalizedIntegralMap f n (Finsupp.single s 1) ⊗ₜ[ℤ] g x) :
          ULift.{max a b w p} ((T.nonDegenerate n →₀ ℤ) ⊗[ℤ] B)) :=
    (congrArg
      (fun z : ULift.{max a b w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] B) ↦
        (tensorNormalizedChainComplexXMap.{b, w, max a p} B f n).hom z)
      (tensorNormalizedCoefficientMap_tmul.{a, b, w, p}
        g S n (Finsupp.single s 1) x)).trans
      (tensorNormalizedChainComplexXMap_tmul.{b, w, max a p}
        B f n (Finsupp.single s 1) (g x))
  exact hleft.trans hright.symm

/-- Changing coefficients commutes with the whole tensor chain map of any simplicial
morphism, on the original tensor complexes with their alternating differentials.
The two coefficient universes, simplex universe and padding are independent. -/
theorem tensorNormalizedChainComplexCoefficientMap_naturality {S T : SSet.{w}}
    (f : S ⟶ T) (g : A →+ B) :
    tensorNormalizedChainComplexMap.{a, w, max b p} A f ≫
        tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g T =
      tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S ≫
        tensorNormalizedChainComplexMap.{b, w, max a p} B f := by
  ext n : 1
  change
    ((tensorNormalizedChainComplexMap.{a, w, max b p} A f ≫
      tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g T).f n :
      tensorNormalizedChainComplexX.{a, w, max b p} A S n ⟶
        tensorNormalizedChainComplexX.{b, w, max a p} B T n) =
      (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S ≫
        tensorNormalizedChainComplexMap.{b, w, max a p} B f).f n
  simp only [HomologicalComplex.comp_f, tensorNormalizedChainComplexMap_f,
    tensorNormalizedChainComplexCoefficientMap_f]
  exact tensorNormalizedCoefficientMap_naturality.{a, b, w, p} f g n

end SSet
