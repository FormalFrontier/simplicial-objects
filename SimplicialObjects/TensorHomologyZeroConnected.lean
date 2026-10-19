/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorHomologyZero

/-!
# The component fold and connected degree-zero tensor homology

The fold used here is Mathlib's `Sigma.desc (fun _ ↦ 𝟙 R)`. It exists for every
simplicial set, including the empty simplicial set. Composing the component
isomorphism with this fold is the homology map of collapse to the standard
point followed by the coefficient isomorphism of terminal tensor chains.
Only the assertion that this fold is invertible requires simplicial
connectedness.

The terminal comparison is checked on the original vertex tensors, using the
coefficient evaluation and insertion formulas, rather than defining a new
comparison by conjugation. Its normalization formula uses the map from
normalized chains to all-simplex chains.

## References and attribution

Mathlib's simplicial component quotient, unique-index coproduct isomorphism,
and normalization are due in particular to Joël Riou. The integral tensor
comparison and the terminal coefficient evaluation/insertion API are supplied
by `SimplicialObjects.TensorCoefficients` and `SimplicialObjects.PointHomology`.
-/

@[expose] public section

universe a w p v u

open CategoryTheory Limits Opposite
open scoped Simplicial TensorProduct

namespace SSet

/-- A terminal simplicial set is simplicially connected. -/
theorem isConnected_of_isTerminal (S : SSet.{w}) (hS : IsTerminal S) :
    S.IsConnected := by
  let h₀ : IsTerminal (S.obj (op ⦋0⦌)) :=
    IsTerminal.isTerminalObj
      ((evaluation SimplexCategoryᵒᵖ (Type w)).obj (op ⦋0⦌)) S hS
  let : Unique (S.obj (op ⦋0⦌)) := Types.isTerminalEquivUnique _ h₀
  refine (S.isConnected_iff).2 ⟨?_, inferInstance⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨x, rfl⟩ := π₀.mk_surjective x
  obtain ⟨y, rfl⟩ := π₀.mk_surjective y
  exact congrArg π₀.mk (Subsingleton.elim x y)

section Coproduct

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]

/-- The coproduct over the simplicial components of a connected simplicial set
is the coefficient object. This is the unique-index coproduct isomorphism. -/
noncomputable def componentsCoproductIso (S : SSet.{w}) [hS : S.IsConnected]
    (R : C) : (∐ fun _ : π₀ S => R) ≅ R := by
  classical
  letI : Unique (π₀ S) := Classical.choice ((S.isConnected_iff_nonempty_unique).1 hS)
  exact coproductUniqueIso (fun _ : π₀ S => R)

omit [HasCoproducts.{w} C] in
/-- The canonical connected coproduct isomorphism is the fold by identities.
The expression on the right is also defined without connectedness. -/
@[simp]
theorem componentsCoproductIso_hom (S : SSet.{w}) [S.IsConnected] (R : C) :
    (componentsCoproductIso S R).hom = Sigma.desc (fun _ : π₀ S => 𝟙 R) := by
  classical
  dsimp only [componentsCoproductIso]
  apply Sigma.hom_ext
  intro c
  simp

end Coproduct

/-- Terminal coefficient evaluation on the original tensor of any vertex. -/
theorem tensorNormalizedHomologyZeroIsoCoefficient_hom_class
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T)
    (v : T _⦋0⦌) (x : A) :
    (tensorNormalizedHomologyZeroIsoCoefficient.{a, w, p} A T hT).hom
        ((tensorNormalizedChainComplex.{a, w, p} A T).homologyπ₀
          (ULift.up (T.normalizedIntegralSimplex v ⊗ₜ[ℤ] x))) =
      (ULift.up x : ULift.{max w p} A) := by
  rw [tensorNormalizedHomologyZeroIsoCoefficient_hom]
  change tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A T hT
      ((tensorNormalizedChainComplex.{a, w, p} A T).homologyπ 0
        ((ChainComplex.cycles₀Iso (tensorNormalizedChainComplex.{a, w, p} A T)).inv
          (ULift.up (T.normalizedIntegralSimplex v ⊗ₜ[ℤ] x)))) = _
  have hv : v ∈ T.nonDegenerate 0 := by simp
  rw [T.normalizedIntegralSimplex_of_mem_nonDegenerate v hv]
  exact tensorNormalizedHomologyZeroToCoefficient_class.{a, w, p} A T hT ⟨v, hv⟩ x

/-- Terminal coefficient insertion is the original raw vertex class. This
formula can be used before applying any simplicial homology map. -/
theorem tensorNormalizedHomologyZeroIsoCoefficient_inv_up
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T)
    (v : T _⦋0⦌) (x : A) :
    (tensorNormalizedHomologyZeroIsoCoefficient.{a, w, p} A T hT).inv
        (ULift.up x : ULift.{max w p} A) =
      (tensorNormalizedChainComplex.{a, w, p} A T).homologyπ₀
        (ULift.up (T.normalizedIntegralSimplex v ⊗ₜ[ℤ] x)) := by
  rw [tensorNormalizedHomologyZeroIsoCoefficient_inv]
  change tensorNormalizedCoefficientToHomologyZero.{a, w, p} A T hT
      (ULift.up x : ULift.{max w p} A) =
    (tensorNormalizedChainComplex.{a, w, p} A T).homologyπ 0
      ((ChainComplex.cycles₀Iso (tensorNormalizedChainComplex.{a, w, p} A T)).inv
        (ULift.up (T.normalizedIntegralSimplex v ⊗ₜ[ℤ] x)))
  have hv : v ∈ T.nonDegenerate 0 := by simp
  rw [T.normalizedIntegralSimplex_of_mem_nonDegenerate v hv]
  exact tensorNormalizedCoefficientToHomologyZero_up.{a, w, p} A T hT ⟨v, hv⟩ x

/-- For any map to a terminal simplicial set, folding the component comparison
is the induced homology map followed by terminal coefficient evaluation.
There is no connectedness or nonemptiness hypothesis on the source. -/
theorem tensorNormalizedHomologyZeroIsoComponents_hom_fold_to_terminal
    (A : Type a) [AddCommGroup A] (S T : SSet.{w}) (hT : IsTerminal T)
    (f : S ⟶ T) :
    (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom ≫
        Sigma.desc (fun _ : π₀ S => 𝟙 (ModuleCat.of ℤ (ULift.{max w p} A))) =
      HomologicalComplex.homologyMap (tensorNormalizedChainComplexMap.{a, w, p} A f) 0 ≫
        (tensorNormalizedHomologyZeroIsoCoefficient.{a, w, p} A T hT).hom := by
  let K := tensorNormalizedChainComplex.{a, w, p} A S
  let L := tensorNormalizedChainComplex.{a, w, p} A T
  let F : K ⟶ L := tensorNormalizedChainComplexMap.{a, w, p} A f
  change (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom ≫ _ =
    HomologicalComplex.homologyMap F 0 ≫ _
  apply (cancel_epi K.homologyπ₀).mp
  rw [← Category.assoc K.homologyπ₀ (HomologicalComplex.homologyMap F 0),
    ChainComplex.homologyπ₀_naturality]
  simp only [Category.assoc]
  apply tensorNormalizedChainComplex_hom_ext.{a, w, p} A S 0
  intro v x
  let vT : T.nonDegenerate 0 := ⟨f.app (op ⦋0⦌) v.val, by simp⟩
  have hf :
      F.f 0 (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x)) =
        ULift.up (Finsupp.single vT 1 ⊗ₜ[ℤ] x) := by
    dsimp only [F]
    rw [tensorNormalizedChainComplexMap_f]
    change tensorNormalizedChainComplexXMap.{a, w, p} A f 0
        (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x)) =
      (ULift.up (Finsupp.single vT 1 ⊗ₜ[ℤ] x) :
        ULift.{max a w p} ((T.nonDegenerate 0 →₀ ℤ) ⊗[ℤ] A))
    rw [tensorNormalizedChainComplexXMap_single,
      T.normalizedIntegralSimplex_of_mem_nonDegenerate
        (f.app (op ⦋0⦌) v.val) vT.property]
  have he := tensorNormalizedHomologyZeroIsoComponents_hom_class.{a, w, p} A S v.val x
  rw [S.normalizedIntegralSimplex_of_mem_nonDegenerate v.val v.property] at he
  change (Sigma.desc (fun _ : π₀ S => 𝟙 (ModuleCat.of ℤ (ULift.{max w p} A))))
      ((tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom
        (K.homologyπ₀ (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x)))) =
    tensorNormalizedHomologyZeroToCoefficient.{a, w, p} A T hT
      (L.homologyπ 0 ((ChainComplex.cycles₀Iso L).inv
        (F.f 0 (ULift.up (Finsupp.single v 1 ⊗ₜ[ℤ] x)))))
  rw [hf, he, tensorNormalizedHomologyZeroToCoefficient_class.{a, w, p} A T hT vT x]
  exact ConcreteCategory.congr_hom
    (Sigma.ι_desc (fun _ : π₀ S => 𝟙 (ModuleCat.of ℤ (ULift.{max w p} A)))
      (π₀.mk v.val)) (ULift.up x)

/-- The all-source fold is collapse to the standard point, followed by the
original terminal coefficient isomorphism. In particular it is defined on the
empty simplicial set. -/
theorem tensorNormalizedHomologyZeroIsoComponents_hom_fold
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) :
    (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom ≫
        Sigma.desc (fun _ : π₀ S => 𝟙 (ModuleCat.of ℤ (ULift.{max w p} A))) =
      HomologicalComplex.homologyMap
          (tensorNormalizedChainComplexMap.{a, w, p} A
            (stdSimplex.isTerminalObj₀.from S)) 0 ≫
        (tensorNormalizedHomologyZeroIsoCoefficient.{a, w, p}
          A (Δ[0] : SSet.{w}) stdSimplex.isTerminalObj₀).hom :=
  tensorNormalizedHomologyZeroIsoComponents_hom_fold_to_terminal
    A S Δ[0] stdSimplex.isTerminalObj₀ (stdSimplex.isTerminalObj₀.from S)

/-- On a terminal simplicial set the component fold is the coefficient
evaluation map itself. -/
theorem tensorNormalizedHomologyZeroIsoComponents_hom_fold_of_isTerminal
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A T).hom ≫
        Sigma.desc (fun _ : π₀ T => 𝟙 (ModuleCat.of ℤ (ULift.{max w p} A))) =
      (tensorNormalizedHomologyZeroIsoCoefficient.{a, w, p} A T hT).hom := by
  simpa only [tensorNormalizedChainComplexMap_id, HomologicalComplex.homologyMap_id,
    Category.id_comp] using
    tensorNormalizedHomologyZeroIsoComponents_hom_fold_to_terminal.{a, w, p}
      A T T hT (𝟙 T)

/-- The all-source component fold is the usual homology augmentation after the
integral tensor comparison and the normalized-chain inclusion. -/
theorem tensorNormalizedHomologyZeroIsoComponents_hom_fold_normalization
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) :
    (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom ≫
        Sigma.desc (fun _ : π₀ S => 𝟙 (ModuleCat.of ℤ (ULift.{max w p} A))) =
      HomologicalComplex.homologyMap (tensorNormalizedChainIso.{a, w, p} A S).hom 0 ≫
        HomologicalComplex.homologyMap
          (S.fromNormalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))) 0 ≫
        S.homology₀ε (ModuleCat.of ℤ (ULift.{max w p} A)) := by
  change (HomologicalComplex.homologyMap (tensorNormalizedChainIso.{a, w, p} A S).hom 0 ≫
      HomologicalComplex.homologyMap
        (S.fromNormalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))) 0 ≫
      (S.homology₀Iso (ModuleCat.of ℤ (ULift.{max w p} A))).hom) ≫ _ = _
  simp only [homology₀ε, Category.assoc]

/-- Normalization compatibility of terminal coefficient evaluation.
The second homology map is induced by the normalized-chain inclusion. -/
theorem tensorNormalizedHomologyZeroIsoCoefficient_hom_normalization
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    (tensorNormalizedHomologyZeroIsoCoefficient.{a, w, p} A T hT).hom =
      HomologicalComplex.homologyMap (tensorNormalizedChainIso.{a, w, p} A T).hom 0 ≫
        HomologicalComplex.homologyMap
          (T.fromNormalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))) 0 ≫
        T.homology₀ε (ModuleCat.of ℤ (ULift.{max w p} A)) := by
  exact (tensorNormalizedHomologyZeroIsoComponents_hom_fold_of_isTerminal.{a, w, p}
    A T hT).symm.trans
      (tensorNormalizedHomologyZeroIsoComponents_hom_fold_normalization.{a, w, p} A T)

/-- Degree-zero tensor homology of a simplicially connected simplicial set.
The hom is the component comparison followed by the canonical fold. -/
noncomputable def tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) [hS : S.IsConnected] :
    (tensorNormalizedChainComplex.{a, w, p} A S).homology 0 ≅
      ModuleCat.of ℤ (ULift.{max w p} A) :=
  tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S ≪≫
    componentsCoproductIso S (ModuleCat.of ℤ (ULift.{max w p} A))

/-- The connected coefficient isomorphism uses the canonical component fold. -/
@[simp]
theorem tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected_hom
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) [S.IsConnected] :
    (tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected.{a, w, p} A S).hom =
      (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom ≫
        Sigma.desc (fun _ : π₀ S => 𝟙 (ModuleCat.of ℤ (ULift.{max w p} A))) := by
  simp only [tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected, Iso.trans_hom,
    componentsCoproductIso_hom]

/-- The connected coefficient comparison sends each original vertex tensor to
its coefficient. -/
theorem tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected_hom_class
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) [S.IsConnected]
    (v : S _⦋0⦌) (x : A) :
    (tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected.{a, w, p} A S).hom
        ((tensorNormalizedChainComplex.{a, w, p} A S).homologyπ₀
          (ULift.up (S.normalizedIntegralSimplex v ⊗ₜ[ℤ] x))) =
      (ULift.up x : ULift.{max w p} A) := by
  rw [tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected_hom]
  change (Sigma.desc (fun _ : π₀ S => 𝟙 (ModuleCat.of ℤ (ULift.{max w p} A))))
      ((tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom _) = _
  rw [tensorNormalizedHomologyZeroIsoComponents_hom_class]
  exact ConcreteCategory.congr_hom
    (Sigma.ι_desc (fun _ : π₀ S => 𝟙 (ModuleCat.of ℤ (ULift.{max w p} A)))
      (π₀.mk v)) (ULift.up x)

/-- The inverse of the connected comparison inserts the class of any vertex. -/
theorem tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected_inv_up
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) [S.IsConnected]
    (v : S _⦋0⦌) (x : A) :
    (tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected.{a, w, p} A S).inv
        (ULift.up x : ULift.{max w p} A) =
      (tensorNormalizedChainComplex.{a, w, p} A S).homologyπ₀
        (ULift.up (S.normalizedIntegralSimplex v ⊗ₜ[ℤ] x)) := by
  rw [← tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected_hom_class.{a, w, p}
    A S v x]
  exact ModuleCat.inv_hom_apply _ _

/-- On a terminal simplicial set the connected coefficient isomorphism agrees
with coefficient evaluation and vertex insertion. -/
theorem tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected_eq
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected.{a, w, p}
        A T (hS := isConnected_of_isTerminal T hT) =
      tensorNormalizedHomologyZeroIsoCoefficient.{a, w, p} A T hT := by
  apply Iso.ext
  rw [tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected_hom]
  exact tensorNormalizedHomologyZeroIsoComponents_hom_fold_of_isTerminal A T hT

end SSet
