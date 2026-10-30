/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.ZMod
public import SimplicialObjects.TensorHomologyZeroProducts
public import SimplicialObjects.TensorHomologyZeroNaturality
public import SimplicialObjects.TensorHomologyZeroCoefficientMaps

/-!
# Naturality of degree-zero normalized homology of products

The product isomorphism commutes with simplicial maps in both factors and with
additive maps in both coefficient groups. The inverse squares use the same
isomorphisms. Coefficient, simplex and padding universes are independent.

The proofs use naturality of the degree-zero homology projection and the
chain-map vertex formulas, then pure-tensor extensionality and the characteristic
formula for the product comparison. The inverse squares follow by cancellation
of these isomorphisms.

## References and attribution

The component and product comparisons are those of
`SimplicialObjects.TensorHomologyZero`, `SimplicialObjects.ComponentProducts` and
`SimplicialObjects.TensorHomologyZeroProducts`. They use Mathlib's simplicial
homology formalization by Joël Riou and its tensor/direct-sum comparison by
Kenny Lau, Mario Carneiro and Eric Wieser.
-/

@[expose] public section

universe a a' b b' w v pK pL

open CategoryTheory Limits
open scoped Simplicial TensorProduct

namespace SSet

/-- The degree-zero product isomorphism commutes with simplicial maps in both
factors, using the product of their levelwise universe lifts. -/
theorem tensorNormalizedHomologyZeroProductIso_hom_naturality
    (A : Type a) (B : Type b) [AddCommGroup A] [AddCommGroup B]
    {K K' : SSet.{w}} {L L' : SSet.{v}} (f : K ⟶ K') (g : L ⟶ L') :
    let X := (tensorNormalizedChainComplex.{a, w, pK} A K).homology 0
    let Xf := (tensorNormalizedChainComplex.{a, w, pK} A K').homology 0
    let Y := (tensorNormalizedChainComplex.{b, v, pL} B L).homology 0
    let Yg := (tensorNormalizedChainComplex.{b, v, pL} B L').homology 0
    let Z := ModuleCat.of ℤ ((X : Type (max a w pK)) ⊗[ℤ] (Y : Type (max b v pL)))
    let Zf := ModuleCat.of ℤ ((Xf : Type (max a w pK)) ⊗[ℤ] (Yg : Type (max b v pL)))
    let tf : Z ⟶ Zf :=
      @ModuleCat.ofHom (R := ℤ) (X := (Z : Type (max a b w v pK pL)))
        (Y := (Zf : Type (max a b w v pK pL))) (inferInstance : Ring ℤ)
        Z.isAddCommGroup Z.isModule Zf.isAddCommGroup Zf.isModule
        (@AddMonoidHom.toZModLinearMap (n := 0)
          (M := (Z : Type (max a b w v pK pL)))
          (M₁ := (Zf : Type (max a b w v pK pL)))
          Z.isAddCommGroup Zf.isAddCommGroup Z.isModule Zf.isModule
          (TensorProduct.map
            (HomologicalComplex.homologyMap
              (tensorNormalizedChainComplexMap.{a, w, pK} A f) 0).hom
            (HomologicalComplex.homologyMap
              (tensorNormalizedChainComplexMap.{b, v, pL} B g) 0).hom).toAddMonoidHom)
    tf ≫ (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K' L').hom =
      (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K L).hom ≫
        HomologicalComplex.homologyMap
          (tensorNormalizedChainComplexMap.{max a b, max w v, max pK pL} (A ⊗[ℤ] B)
            (Limits.prod.map ((uliftFunctor.{v, w}).map f) ((uliftFunctor.{w, v}).map g))) 0 := by
  dsimp only
  apply ModuleCat.hom_ext
  apply tensorNormalizedHomologyZeroProduct_ext A B K L
  intro k l x y
  change (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL}
      A B K' L').hom
      (TensorProduct.map
        (HomologicalComplex.homologyMap
          (tensorNormalizedChainComplexMap.{a, w, pK} A f) 0).hom
        (HomologicalComplex.homologyMap
          (tensorNormalizedChainComplexMap.{b, v, pL} B g) 0).hom
        (_ ⊗ₜ[ℤ] _)) =
    HomologicalComplex.homologyMap
      (tensorNormalizedChainComplexMap.{max a b, max w v, max pK pL} (A ⊗[ℤ] B)
        (Limits.prod.map ((uliftFunctor.{v, w}).map f) ((uliftFunctor.{w, v}).map g))) 0
      ((tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K L).hom
        (_ ⊗ₜ[ℤ] _))
  rw [TensorProduct.map_tmul]
  have hf := tensorNormalizedHomologyZeroMap_class.{a, w, pK} A f k x
  have hg := tensorNormalizedHomologyZeroMap_class.{b, v, pL} B g l y
  have hs := tensorNormalizedHomologyZeroProductIso_hom_class.{a, b, w, v, pK, pL}
    A B K L k l x y
  have ht := tensorNormalizedHomologyZeroProductIso_hom_class.{a, b, w, v, pK, pL}
    A B K' L' (f.app (Opposite.op ⦋0⦌) k) (g.app (Opposite.op ⦋0⦌) l) x y
  let F := Limits.prod.map ((uliftFunctor.{v, w}).map f) ((uliftFunctor.{w, v}).map g)
  have hp := tensorNormalizedHomologyZeroMap_class.{max a b, max w v, max pK pL}
    (A ⊗[ℤ] B) F
    (prodVertex (X := (uliftFunctor.{v, w}).obj K)
      (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)) (x ⊗ₜ[ℤ] y)
  let P' := Limits.prod ((uliftFunctor.{v, w}).obj K') ((uliftFunctor.{w, v}).obj L')
  have hv := prodVertex_map ((uliftFunctor.{v, w}).map f) ((uliftFunctor.{w, v}).map g)
    (ULift.up k) (ULift.up l)
  -- Transport the vertex equality before composing the homology-class equalities.
  have hclass := congrArg
    (fun z : P' _⦋0⦌ =>
      (tensorNormalizedChainComplex.{max a b, max w v, max pK pL}
        (A ⊗[ℤ] B) P').homologyπ₀
        (ULift.up (P'.normalizedIntegralSimplex z ⊗ₜ[ℤ] (x ⊗ₜ[ℤ] y)))) hv
  exact ((congrArg
    (fun z => (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL}
      A B K' L').hom z)
    (congrArg₂ (fun s t => s ⊗ₜ[ℤ] t) hf hg)).trans ht).trans
    ((congrArg (fun z => HomologicalComplex.homologyMap
      (tensorNormalizedChainComplexMap.{max a b, max w v, max pK pL}
        (A ⊗[ℤ] B) F) 0 z) hs).trans (hp.trans hclass)).symm

/-- The degree-zero product isomorphism commutes with arbitrary additive maps
in both coefficient groups, with balanced independent coefficient paddings. -/
theorem tensorNormalizedHomologyZeroProductIso_hom_coefficient_naturality
    {A : Type a} {A' : Type a'} {B : Type b} {B' : Type b'}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    (m : A →+ A') (n : B →+ B') (K : SSet.{w}) (L : SSet.{v}) :
    let X := (tensorNormalizedChainComplex.{a, w, max a' pK} A K).homology 0
    let Xc := (tensorNormalizedChainComplex.{a', w, max a pK} A' K).homology 0
    let Y := (tensorNormalizedChainComplex.{b, v, max b' pL} B L).homology 0
    let Yc := (tensorNormalizedChainComplex.{b', v, max b pL} B' L).homology 0
    let Z := ModuleCat.of ℤ
      ((X : Type (max a a' w pK)) ⊗[ℤ] (Y : Type (max b b' v pL)))
    let Zc := ModuleCat.of ℤ
      ((Xc : Type (max a a' w pK)) ⊗[ℤ] (Yc : Type (max b b' v pL)))
    let tc : Z ⟶ Zc :=
      @ModuleCat.ofHom (R := ℤ) (X := (Z : Type (max a a' b b' w v pK pL)))
        (Y := (Zc : Type (max a a' b b' w v pK pL))) (inferInstance : Ring ℤ)
        Z.isAddCommGroup Z.isModule Zc.isAddCommGroup Zc.isModule
        (@AddMonoidHom.toZModLinearMap (n := 0)
          (M := (Z : Type (max a a' b b' w v pK pL)))
          (M₁ := (Zc : Type (max a a' b b' w v pK pL)))
          Z.isAddCommGroup Zc.isAddCommGroup Z.isModule Zc.isModule
          (TensorProduct.map
            (HomologicalComplex.homologyMap
              (tensorNormalizedChainComplexCoefficientMap.{a, a', w, pK} m K) 0).hom
            (HomologicalComplex.homologyMap
              (tensorNormalizedChainComplexCoefficientMap.{b, b', v, pL} n L) 0).hom
            ).toAddMonoidHom)
    tc ≫ (tensorNormalizedHomologyZeroProductIso.{a', b', w, v, max a pK, max b pL}
      A' B' K L).hom =
      (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, max a' pK, max b' pL}
        A B K L).hom ≫
        HomologicalComplex.homologyMap
          (tensorNormalizedChainComplexCoefficientMap.{max a b, max a' b',
            max w v, max pK pL}
            (TensorProduct.map m.toIntLinearMap n.toIntLinearMap).toAddMonoidHom
            (Limits.prod ((uliftFunctor.{v, w}).obj K) ((uliftFunctor.{w, v}).obj L))) 0 := by
  dsimp only
  apply ModuleCat.hom_ext
  apply tensorNormalizedHomologyZeroProduct_ext A B K L
  intro k l x y
  change (tensorNormalizedHomologyZeroProductIso.{a', b', w, v, max a pK, max b pL}
      A' B' K L).hom
      (TensorProduct.map
        (HomologicalComplex.homologyMap
          (tensorNormalizedChainComplexCoefficientMap.{a, a', w, pK} m K) 0).hom
        (HomologicalComplex.homologyMap
          (tensorNormalizedChainComplexCoefficientMap.{b, b', v, pL} n L) 0).hom
        (_ ⊗ₜ[ℤ] _)) =
    HomologicalComplex.homologyMap
      (tensorNormalizedChainComplexCoefficientMap.{max a b, max a' b',
        max w v, max pK pL}
        (TensorProduct.map m.toIntLinearMap n.toIntLinearMap).toAddMonoidHom
        (Limits.prod ((uliftFunctor.{v, w}).obj K) ((uliftFunctor.{w, v}).obj L))) 0
      ((tensorNormalizedHomologyZeroProductIso.{a, b, w, v, max a' pK, max b' pL}
        A B K L).hom (_ ⊗ₜ[ℤ] _))
  rw [TensorProduct.map_tmul]
  have hm := tensorNormalizedHomologyZeroCoefficientMap_class.{a, a', w, pK} m K k x
  have hn := tensorNormalizedHomologyZeroCoefficientMap_class.{b, b', v, pL} n L l y
  have hs := tensorNormalizedHomologyZeroProductIso_hom_class.{a, b, w, v,
    max a' pK, max b' pL} A B K L k l x y
  have ht := tensorNormalizedHomologyZeroProductIso_hom_class.{a', b', w, v,
    max a pK, max b pL} A' B' K L k l (m x) (n y)
  let P := Limits.prod ((uliftFunctor.{v, w}).obj K) ((uliftFunctor.{w, v}).obj L)
  let c := (TensorProduct.map m.toIntLinearMap n.toIntLinearMap).toAddMonoidHom
  have hp := tensorNormalizedHomologyZeroCoefficientMap_class.{max a b, max a' b',
    max w v, max pK pL} c P
    (prodVertex (X := (uliftFunctor.{v, w}).obj K)
      (Y := (uliftFunctor.{w, v}).obj L) (ULift.up k) (ULift.up l)) (x ⊗ₜ[ℤ] y)
  simp only [c, LinearMap.toAddMonoidHom_coe, TensorProduct.map_tmul,
    AddMonoidHom.coe_toIntLinearMap] at hp
  exact ((congrArg
    (fun z => (tensorNormalizedHomologyZeroProductIso.{a', b', w, v,
      max a pK, max b pL} A' B' K L).hom z)
    (congrArg₂ (fun s t => s ⊗ₜ[ℤ] t) hm hn)).trans ht).trans
    ((congrArg (fun z => HomologicalComplex.homologyMap
      (tensorNormalizedChainComplexCoefficientMap.{max a b, max a' b',
        max w v, max pK pL} c P) 0 z) hs).trans hp).symm

/-- The inverse degree-zero product comparison commutes with simplicial maps
in both factors. -/
theorem tensorNormalizedHomologyZeroProductIso_inv_naturality
    (A : Type a) (B : Type b) [AddCommGroup A] [AddCommGroup B]
    {K K' : SSet.{w}} {L L' : SSet.{v}} (f : K ⟶ K') (g : L ⟶ L') :
    let X := (tensorNormalizedChainComplex.{a, w, pK} A K).homology 0
    let Xf := (tensorNormalizedChainComplex.{a, w, pK} A K').homology 0
    let Y := (tensorNormalizedChainComplex.{b, v, pL} B L).homology 0
    let Yg := (tensorNormalizedChainComplex.{b, v, pL} B L').homology 0
    let Z := ModuleCat.of ℤ ((X : Type (max a w pK)) ⊗[ℤ] (Y : Type (max b v pL)))
    let Zf := ModuleCat.of ℤ ((Xf : Type (max a w pK)) ⊗[ℤ] (Yg : Type (max b v pL)))
    let tf : Z ⟶ Zf :=
      @ModuleCat.ofHom (R := ℤ) (X := (Z : Type (max a b w v pK pL)))
        (Y := (Zf : Type (max a b w v pK pL))) (inferInstance : Ring ℤ)
        Z.isAddCommGroup Z.isModule Zf.isAddCommGroup Zf.isModule
        (@AddMonoidHom.toZModLinearMap (n := 0)
          (M := (Z : Type (max a b w v pK pL)))
          (M₁ := (Zf : Type (max a b w v pK pL)))
          Z.isAddCommGroup Zf.isAddCommGroup Z.isModule Zf.isModule
          (TensorProduct.map
            (HomologicalComplex.homologyMap
              (tensorNormalizedChainComplexMap.{a, w, pK} A f) 0).hom
            (HomologicalComplex.homologyMap
              (tensorNormalizedChainComplexMap.{b, v, pL} B g) 0).hom).toAddMonoidHom)
    (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K L).inv ≫ tf =
      HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexMap.{max a b, max w v, max pK pL} (A ⊗[ℤ] B)
          (Limits.prod.map ((uliftFunctor.{v, w}).map f) ((uliftFunctor.{w, v}).map g))) 0 ≫
        (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K' L').inv := by
  dsimp only
  apply (cancel_mono
    (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K' L').hom).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg
      (fun q ↦
        (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, pK, pL} A B K L).inv ≫ q)
      (tensorNormalizedHomologyZeroProductIso_hom_naturality.{a, b, w, v, pK, pL} A B f g)

/-- The inverse degree-zero product comparison commutes with arbitrary additive
maps in both coefficient groups. -/
theorem tensorNormalizedHomologyZeroProductIso_inv_coefficient_naturality
    {A : Type a} {A' : Type a'} {B : Type b} {B' : Type b'}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    (m : A →+ A') (n : B →+ B') (K : SSet.{w}) (L : SSet.{v}) :
    let X := (tensorNormalizedChainComplex.{a, w, max a' pK} A K).homology 0
    let Xc := (tensorNormalizedChainComplex.{a', w, max a pK} A' K).homology 0
    let Y := (tensorNormalizedChainComplex.{b, v, max b' pL} B L).homology 0
    let Yc := (tensorNormalizedChainComplex.{b', v, max b pL} B' L).homology 0
    let Z := ModuleCat.of ℤ
      ((X : Type (max a a' w pK)) ⊗[ℤ] (Y : Type (max b b' v pL)))
    let Zc := ModuleCat.of ℤ
      ((Xc : Type (max a a' w pK)) ⊗[ℤ] (Yc : Type (max b b' v pL)))
    let tc : Z ⟶ Zc :=
      @ModuleCat.ofHom (R := ℤ) (X := (Z : Type (max a a' b b' w v pK pL)))
        (Y := (Zc : Type (max a a' b b' w v pK pL))) (inferInstance : Ring ℤ)
        Z.isAddCommGroup Z.isModule Zc.isAddCommGroup Zc.isModule
        (@AddMonoidHom.toZModLinearMap (n := 0)
          (M := (Z : Type (max a a' b b' w v pK pL)))
          (M₁ := (Zc : Type (max a a' b b' w v pK pL)))
          Z.isAddCommGroup Zc.isAddCommGroup Z.isModule Zc.isModule
          (TensorProduct.map
            (HomologicalComplex.homologyMap
              (tensorNormalizedChainComplexCoefficientMap.{a, a', w, pK} m K) 0).hom
            (HomologicalComplex.homologyMap
              (tensorNormalizedChainComplexCoefficientMap.{b, b', v, pL} n L) 0).hom
            ).toAddMonoidHom)
    (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, max a' pK, max b' pL}
      A B K L).inv ≫ tc =
      HomologicalComplex.homologyMap
        (tensorNormalizedChainComplexCoefficientMap.{max a b, max a' b',
            max w v, max pK pL}
          (TensorProduct.map m.toIntLinearMap n.toIntLinearMap).toAddMonoidHom
          (Limits.prod ((uliftFunctor.{v, w}).obj K) ((uliftFunctor.{w, v}).obj L))) 0 ≫
        (tensorNormalizedHomologyZeroProductIso.{a', b', w, v, max a pK, max b pL}
          A' B' K L).inv := by
  dsimp only
  apply (cancel_mono
    (tensorNormalizedHomologyZeroProductIso.{a', b', w, v, max a pK, max b pL}
      A' B' K L).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg
      (fun q ↦ (tensorNormalizedHomologyZeroProductIso.{a, b, w, v, max a' pK, max b' pL}
        A B K L).inv ≫ q)
      (tensorNormalizedHomologyZeroProductIso_hom_coefficient_naturality.{a, a', b, b',
        w, v, pK, pL} m n K L)

end SSet
