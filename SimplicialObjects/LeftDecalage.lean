/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal

/-!
# Augmented left décalage of a simplicial object

Prepending a vertex to the augmented simplex category gives an augmented simplicial object
whose degree `n` is the original degree `n + 1`. The original zeroth degeneracies supply
mathlib's `SimplicialObject.Augmented.ExtraDegeneracy` in any category.
-/

@[expose] public section

open CategoryTheory Category Opposite
open scoped Simplicial

namespace SimplicialObjects.LeftDecalage

/-- Adjoin a new initial vertex to a simplex morphism. -/
def prependMap {source target : SimplexCategory} (morphism : source ⟶ target) :
    ⦋source.len + 1⦌ ⟶ ⦋target.len + 1⦌ :=
  SimplexCategory.mkHom {
    toFun := Fin.cases 0 (fun vertex => (morphism.toOrderHom vertex).succ)
    monotone' := by
      intro first second comparison
      cases first using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ first =>
        cases second using Fin.cases with
        | zero => exact False.elim (by have := Fin.le_def.mp comparison; simp at this)
        | succ second =>
          simp only [Fin.cases_succ, Fin.succ_le_succ_iff]
          exact morphism.toOrderHom.monotone
            (by simpa only [Fin.succ_le_succ_iff] using comparison) }

theorem prependMap_id (simplex : SimplexCategory) :
    prependMap (𝟙 simplex) = 𝟙 _ := by
  ext vertex
  cases vertex using Fin.cases <;> rfl

theorem prependMap_comp {source middle target : SimplexCategory}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    prependMap (first ≫ second) = prependMap first ≫ prependMap second := by
  ext vertex
  cases vertex using Fin.cases <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Prepending the initial vertex sends the empty augmented simplex to `[0]`.
For nonempty simplices, this is the left ordinal sum `[0] ⊗ [-]` with canonical degree objects. -/
def index : AugmentedSimplexCategory ⥤ SimplexCategory where
  obj
    | .star => ⦋0⦌
    | .of simplex => ⦋simplex.len + 1⦌
  map {source target} morphism :=
    match source, target, morphism with
    | .star, .star, _ => 𝟙 _
    | .star, .of simplex, _ => SimplexCategory.const ⦋0⦌ ⦋simplex.len + 1⦌ 0
    | .of _, .of _, morphism => prependMap morphism
  map_id simplex := by
    cases simplex with
    | star => rfl
    | of simplex => exact prependMap_id simplex
  map_comp := fun {source middle target} first second =>
    match source, middle, target, first, second with
    | .of _, .of _, .of _, first, second => prependMap_comp first second
    | .star, .of middle, .of target, _, second => by
      change SimplexCategory.const ⦋0⦌ ⦋target.len + 1⦌ 0 =
        SimplexCategory.const ⦋0⦌ ⦋middle.len + 1⦌ 0 ≫ prependMap second
      ext vertex
      simp [prependMap]
    | .star, .star, .of _, _, _ => by simp
    | .star, .star, .star, _, _ => by simp
    | .of _, .of _, .star, _, second => (second : PEmpty).elim
    | .of _, .star, _, first, _ => (first : PEmpty).elim
    | .star, .of _, .star, _, second => (second : PEmpty).elim

theorem prependMap_δ (degree : ℕ) (faceIndex : Fin (degree + 2)) :
    prependMap (SimplexCategory.δ faceIndex) = SimplexCategory.δ faceIndex.succ := by
  ext vertex
  cases vertex using Fin.cases with
  | zero => simp [prependMap, SimplexCategory.δ, Fin.succAbove]
  | succ vertex => simp [prependMap, SimplexCategory.δ]

theorem prependMap_σ (degree : ℕ) (degeneracyIndex : Fin (degree + 1)) :
    prependMap (SimplexCategory.σ degeneracyIndex) =
      SimplexCategory.σ degeneracyIndex.succ := by
  ext vertex
  cases vertex using Fin.cases with
  | zero => simp [prependMap, SimplexCategory.σ, Fin.predAbove]
  | succ vertex => simp [prependMap, SimplexCategory.σ]

theorem prependMap_comp_δ_zero {source target : SimplexCategory}
    (morphism : source ⟶ target) :
    SimplexCategory.δ 0 ≫ prependMap morphism =
      morphism ≫ SimplexCategory.δ 0 := by
  ext vertex
  simp [prependMap, SimplexCategory.δ, Fin.succAbove]

/-- The augmented left décalage, with target the original degree-zero object. -/
def augmented {C : Type*} [Category* C] (X : SimplicialObject C) :
    SimplicialObject.Augmented C :=
  AugmentedSimplexCategory.equivAugmentedSimplicialObject.functor.obj (index.op ⋙ X)

@[simp] theorem augmentation_point {C : Type*} [Category* C] (X : SimplicialObject C) :
    (augmented X).right = X _⦋0⦌ := by rfl

@[simp] theorem path_obj {C : Type*} [Category* C] (X : SimplicialObject C) (degree : ℕ) :
    (augmented X).left _⦋degree⦌ = X _⦋degree + 1⦌ := by rfl

@[simp] theorem path_face {C : Type*} [Category* C] (X : SimplicialObject C)
    (degree : ℕ) (faceIndex : Fin (degree + 2)) :
    (augmented X).left.δ faceIndex = X.δ faceIndex.succ := by
  change X.map (prependMap (SimplexCategory.δ faceIndex)).op =
    X.map (SimplexCategory.δ faceIndex.succ).op
  rw [prependMap_δ]

@[simp] theorem path_degeneracy {C : Type*} [Category* C] (X : SimplicialObject C)
    (degree : ℕ) (degeneracyIndex : Fin (degree + 1)) :
    (augmented X).left.σ degeneracyIndex = X.σ degeneracyIndex.succ := by
  change X.map (prependMap (SimplexCategory.σ degeneracyIndex)).op =
    X.map (SimplexCategory.σ degeneracyIndex.succ).op
  rw [prependMap_σ]

/-- The augmentation selects the newly prepended vertex, vertex zero. -/
theorem augmentation_app {C : Type*} [Category* C] (X : SimplicialObject C)
    (degree : ℕ) :
    (augmented X).hom.app (op ⦋degree⦌) =
      X.map (SimplexCategory.const ⦋0⦌ ⦋degree + 1⦌ 0).op := by rfl

@[simp] theorem augmentation_zero {C : Type*} [Category* C] (X : SimplicialObject C) :
    (augmented X).hom.app (op ⦋0⦌) = X.δ (1 : Fin 2) := by
  change X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op = X.map (SimplexCategory.δ 1).op
  have identity : SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 = SimplexCategory.δ 1 := by
    ext vertex
    fin_cases vertex
    decide
  rw [identity]

/-- Original `σ 0` satisfies all five native extra-degeneracy equations,
including the augmentation section and the exceptional degree-zero face. -/
def extraDegeneracy {C : Type*} [Category* C] (X : SimplicialObject C) :
    SimplicialObject.Augmented.ExtraDegeneracy (augmented X) where
  s' := X.σ 0
  s _ := X.σ 0
  s'_comp_ε := by
    change X.σ (0 : Fin 1) ≫ (augmented X).hom.app (op ⦋0⦌) = 𝟙 _
    rw [augmentation_zero]
    exact X.δ_comp_σ_succ (i := 0)
  s₀_comp_δ₁ := by
    change X.σ (0 : Fin 2) ≫ (augmented X).left.δ (1 : Fin 2) =
      (augmented X).hom.app (op ⦋0⦌) ≫ X.σ (0 : Fin 1)
    rw [path_face, augmentation_zero]
    exact X.δ_comp_σ_of_gt (by decide : (0 : Fin 1).castSucc < (1 : Fin 2))
  s_comp_δ₀ degree := by
    change X.σ (0 : Fin (degree + 2)) ≫ (augmented X).left.δ 0 = 𝟙 _
    rw [path_face]
    exact X.δ_comp_σ_succ (i := 0)
  s_comp_δ degree faceIndex := by
    change X.σ (0 : Fin (degree + 3)) ≫ (augmented X).left.δ faceIndex.succ =
      (augmented X).left.δ faceIndex ≫ X.σ (0 : Fin (degree + 2))
    rw [path_face, path_face]
    exact X.δ_comp_σ_of_gt (by simp : (0 : Fin (degree + 2)).castSucc < faceIndex.succ)
  s_comp_σ degree degeneracyIndex := by
    change X.σ (0 : Fin (degree + 2)) ≫ (augmented X).left.σ degeneracyIndex.succ =
      (augmented X).left.σ degeneracyIndex ≫ X.σ (0 : Fin (degree + 3))
    rw [path_degeneracy, path_degeneracy]
    exact (X.σ_comp_σ (Fin.zero_le degeneracyIndex.succ)).symm

/-- The natural simplicial projection is the *other* first face, `δ 0`.
At degree zero it differs from the augmentation's `δ 1` in general. -/
def projection {C : Type*} [Category* C] (X : SimplicialObject C) :
    (augmented X).left ⟶ X where
  app | op simplex => X.map (SimplexCategory.δ (0 : Fin (simplex.len + 2))).op
  naturality source target morphism := by
    change X.map (prependMap morphism.unop).op ≫ X.map (SimplexCategory.δ 0).op =
      X.map (SimplexCategory.δ 0).op ≫ X.map morphism
    rw [← X.map_comp, ← X.map_comp]
    exact congrArg X.map (congrArg Opposite.op (prependMap_comp_δ_zero morphism.unop))

@[simp] theorem projection_zero {C : Type*} [Category* C] (X : SimplicialObject C) :
    (projection X).app (op ⦋0⦌) = X.δ (0 : Fin 2) := rfl

/-- Left décalage is functorial in its simplicial object, including the augmentation target. -/
def functor (C : Type*) [Category* C] :
    SimplicialObject C ⥤ SimplicialObject.Augmented C :=
  ((Functor.whiskeringLeft _ _ C).obj index.op) ⋙
    AugmentedSimplexCategory.equivAugmentedSimplicialObject.functor

@[simp] theorem functor_obj {C : Type*} [Category* C] (X : SimplicialObject C) :
    (functor C).obj X = augmented X := rfl

@[simp] theorem functor_map_left_app {C : Type*} [Category* C]
    {X Y : SimplicialObject C} (morphism : X ⟶ Y) (degree : ℕ) :
    ((functor C).map morphism).left.app (op ⦋degree⦌) =
      morphism.app (op ⦋degree + 1⦌) := by rfl

@[simp] theorem functor_map_right {C : Type*} [Category* C]
    {X Y : SimplicialObject C} (morphism : X ⟶ Y) :
    ((functor C).map morphism).right = morphism.app (op ⦋0⦌) := by rfl

/-- The augmentation section supplied by `σ 0` is natural in the simplicial object. -/
theorem extraDegeneracy_s'_naturality {C : Type*} [Category* C]
    {X Y : SimplicialObject C} (morphism : X ⟶ Y) :
    (extraDegeneracy X).s' ≫ ((functor C).map morphism).left.app (op ⦋0⦌) =
      ((functor C).map morphism).right ≫ (extraDegeneracy Y).s' := by
  change X.σ (0 : Fin 1) ≫ morphism.app (op ⦋1⦌) =
    morphism.app (op ⦋0⦌) ≫ Y.σ 0
  exact SimplicialObject.σ_naturality morphism (0 : Fin 1)

/-- Every higher extra-degeneracy component is natural in the simplicial object. -/
theorem extraDegeneracy_s_naturality {C : Type*} [Category* C]
    {X Y : SimplicialObject C} (morphism : X ⟶ Y) (degree : ℕ) :
    (extraDegeneracy X).s degree ≫
        ((functor C).map morphism).left.app (op ⦋degree + 1⦌) =
      ((functor C).map morphism).left.app (op ⦋degree⦌) ≫
        (extraDegeneracy Y).s degree := by
  change X.σ (0 : Fin (degree + 2)) ≫ morphism.app (op ⦋degree + 2⦌) =
    morphism.app (op ⦋degree + 1⦌) ≫ Y.σ 0
  exact SimplicialObject.σ_naturality morphism (0 : Fin (degree + 2))

/-- The zeroth-face projection varies naturally with the simplicial object. -/
def naturalProjection (C : Type*) [Category* C] :
    functor C ⋙ SimplicialObject.Augmented.drop ⟶ 𝟭 (SimplicialObject C) where
  app X := projection X
  naturality X Y morphism := by
    ext ⟨simplex⟩
    dsimp [SimplicialObject.Augmented.drop, Comma.fst, functor]
    change morphism.app (op ⦋simplex.len + 1⦌) ≫ Y.δ 0 =
      X.δ (0 : Fin (simplex.len + 2)) ≫ morphism.app (op simplex)
    exact (SimplicialObject.δ_naturality morphism (0 : Fin (simplex.len + 2))).symm

end SimplicialObjects.LeftDecalage
