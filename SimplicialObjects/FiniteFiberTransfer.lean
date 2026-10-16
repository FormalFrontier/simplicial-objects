/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Basic.Finite.Sigma

/-!
# Finite-fiber transfers

Finite fibers define a contravariant map on coproducts of a coefficient object in a
preadditive category. Cartesian naturality assembles these maps on diagrams, and the
alternating face map functor gives a map on simplicial chains. Vertex fibers suffice
for an equifibered map of simplicial sets.

The complexes here include all simplices. No comparison with normalized, topological,
or twisted-coefficient chains is asserted.

## References

May, *A Concise Course in Algebraic Topology*, revised edition, §16, Problem 3,
motivates the covering transfer and its sheet identity. The categorical construction
here does not identify a topological covering with an equifibered simplicial map.
-/

@[expose] public section

open CategoryTheory Limits Opposite Functor
open scoped Simplicial

universe w v u vD uD

namespace CategoryTheory.Limits.Types

/-- Restriction of the upper map of a pullback square to a fiber of its left map. -/
def pullbackFiberMap {A B U V : Type w} {t : A ⟶ B} {l : A ⟶ U}
    {r : B ⟶ V} {b : U ⟶ V} (h : IsPullback t l r b) (x : U) :
    {a : A // l a = x} → {y : B // r y = b x} :=
  fun a ↦ ⟨t a, (congrArg (fun k : A ⟶ V ↦ k a) h.w).trans (congrArg b a.property)⟩

/-- Pullback restriction is bijective, without finiteness assumptions. -/
theorem pullbackFiberMap_bijective {A B U V : Type w} {t : A ⟶ B} {l : A ⟶ U}
    {r : B ⟶ V} {b : U ⟶ V} (h : IsPullback t l r b) (x : U) :
    Function.Bijective (pullbackFiberMap h x) := by
  constructor
  · intro a a' e
    apply Subtype.ext
    exact ext_of_isPullback h (congrArg Subtype.val e)
      (a.property.trans a'.property.symm)
  · intro y
    obtain ⟨a, ht, hl⟩ := exists_of_isPullback h y.val x y.property
    exact ⟨⟨a, hl⟩, Subtype.ext ht⟩

/-- The equivalence between fibers supplied by a pullback square. -/
noncomputable def pullbackFiberEquiv {A B U V : Type w} {t : A ⟶ B} {l : A ⟶ U}
    {r : B ⟶ V} {b : U ⟶ V} (h : IsPullback t l r b) (x : U) :
    {a : A // l a = x} ≃ {y : B // r y = b x} :=
  Equiv.ofBijective _ (pullbackFiberMap_bijective h x)

@[simp]
theorem pullbackFiberEquiv_apply {A B U V : Type w} {t : A ⟶ B} {l : A ⟶ U}
    {r : B ⟶ V} {b : U ⟶ V} (h : IsPullback t l r b) (x : U)
    (a : {a : A // l a = x}) :
    (pullbackFiberEquiv h x a).val = t a := rfl

/-- A composite of two maps with finite fibers has finite fibers. -/
theorem finite_fiber_comp {A B D : Type*} (f : A → B) (g : B → D)
    (hf : ∀ b : B, Finite {a : A // f a = b})
    (hg : ∀ d : D, Finite {b : B // g b = d}) (d : D) :
    Finite {a : A // (g ∘ f) a = d} := by
  let := hg d
  let := fun b : {b : B // g b = d} ↦ hf b.val
  exact Finite.of_equiv (Σ b : {b : B // g b = d}, {a : A // f a = b.val})
    (Equiv.sigmaSubtypeFiberEquivSubtype f (p := fun a ↦ (g ∘ f) a = d)
      (q := fun b ↦ g b = d) (fun _ ↦ Iff.rfl))

end CategoryTheory.Limits.Types

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Send a coproduct generator to the sum of the generators over its finite fiber.
The coefficient is an object, not a scalar ring. -/
noncomputable def sigmaConstTransfer {A B : Type w} (f : A ⟶ B)
    (hf : ∀ b : B, Finite {a : A // f a = b}) (R : C) :
    (sigmaConst.obj R).obj B ⟶ (sigmaConst.obj R).obj A := by
  classical
  exact Sigma.desc fun b ↦ by
    letI := hf b
    letI := Fintype.ofFinite {a : A // f a = b}
    exact ∑ a : {a : A // f a = b}, Sigma.ι (fun _ : A ↦ R) a.val

/-- The characteristic generator equation, independent of finite enumerations. -/
@[reassoc]
theorem ι_sigmaConstTransfer {A B : Type w} (f : A ⟶ B)
    (hf : ∀ b : B, Finite {a : A // f a = b}) (R : C) (b : B) :
    Sigma.ι (fun _ : B ↦ R) b ≫ sigmaConstTransfer f hf R =
      ∑ᶠ a : {a : A // f a = b}, Sigma.ι (fun _ : A ↦ R) a.val := by
  classical
  let := hf b
  let := Fintype.ofFinite {a : A // f a = b}
  simp [sigmaConstTransfer, finsum_eq_sum_of_fintype]

/-- The transfer of the identity is the identity on the coproduct. -/
@[simp]
theorem sigmaConstTransfer_id (A : Type w) (R : C) :
    sigmaConstTransfer (𝟙 A) (fun a ↦ by
      change Finite {a' : A // a' = a}
      infer_instance) R = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro a
  calc
    _ = ∑ᶠ a' : {a' : A // a' = a}, Sigma.ι (fun _ : A ↦ R) a'.val :=
      ι_sigmaConstTransfer _ _ _ _
    _ = Sigma.ι (fun _ : A ↦ R) a :=
      finsum_eq_single (fun a' : {a' : A // a' = a} ↦ Sigma.ι (fun _ : A ↦ R) a'.val)
        ⟨a, rfl⟩ (fun a' h ↦ (h (Subtype.ext a'.property)).elim)
    _ = _ := (Category.comp_id _).symm

/-- The transfer of a composite is the reverse-order composite of transfers.
Finiteness of composite fibers follows from the constituent fibers. -/
theorem sigmaConstTransfer_comp {A B D : Type w} (f : A ⟶ B) (g : B ⟶ D)
    (hf : ∀ b : B, Finite {a : A // f a = b})
    (hg : ∀ d : D, Finite {b : B // g b = d}) (R : C) :
    sigmaConstTransfer (f ≫ g) (Types.finite_fiber_comp f g hf hg) R =
      sigmaConstTransfer g hg R ≫ sigmaConstTransfer f hf R := by
  classical
  apply Sigma.hom_ext
  intro d
  let := hg d
  let := hf
  let : Finite {a : A // (f ≫ g) a = d} := Types.finite_fiber_comp f g hf hg d
  let := Fintype.ofFinite {b : B // g b = d}
  let := fun b : B ↦ Fintype.ofFinite {a : A // f a = b}
  let := Fintype.ofFinite {a : A // (f ≫ g) a = d}
  rw [ι_sigmaConstTransfer, ι_sigmaConstTransfer_assoc]
  simp only [finsum_eq_sum_of_fintype, Preadditive.sum_comp]
  simp_rw [ι_sigmaConstTransfer, finsum_eq_sum_of_fintype]
  rw [← Fintype.sum_sigma']
  exact ((Equiv.sigmaSubtypeFiberEquivSubtype f (p := fun a ↦ (f ≫ g) a = d)
    (q := fun b ↦ g b = d) (fun _ ↦ Iff.rfl)).sum_comp
      (fun a ↦ Sigma.ι (fun _ : A ↦ R) a.val)).symm

/-- Postcomposition of a transfer with the coproduct eliminator sums the chosen maps
along fibers. Uniqueness is the coproduct universal property `Sigma.hom_ext`. -/
theorem sigmaConstTransfer_desc {A B : Type w} (f : A ⟶ B)
    (hf : ∀ b : B, Finite {a : A // f a = b}) (R : C) {Z : C} (h : A → (R ⟶ Z)) :
    sigmaConstTransfer f hf R ≫ Sigma.desc h =
      Sigma.desc (fun b ↦ ∑ᶠ a : {a : A // f a = b}, h a.val) := by
  classical
  apply Sigma.hom_ext
  intro b
  let := hf b
  let := Fintype.ofFinite {a : A // f a = b}
  simp only [ι_sigmaConstTransfer_assoc, finsum_eq_sum_of_fintype,
    Preadditive.sum_comp, Sigma.ι_desc]

/-- Transfer commutes with changing the coefficient object. -/
theorem sigmaConstTransfer_coefficient {A B : Type w} (f : A ⟶ B)
    (hf : ∀ b : B, Finite {a : A // f a = b}) {R R' : C} (a : R ⟶ R') :
    (sigmaConst.map a).app B ≫ sigmaConstTransfer f hf R' =
      sigmaConstTransfer f hf R ≫ (sigmaConst.map a).app A := by
  classical
  apply Sigma.hom_ext
  intro b
  let := hf b
  let := Fintype.ofFinite {a : A // f a = b}
  rw [← Category.assoc, sigmaConst_map_app, Sigma.ι_map, Category.assoc,
    ι_sigmaConstTransfer, ι_sigmaConstTransfer_assoc]
  simp only [finsum_eq_sum_of_fintype, Preadditive.comp_sum, Preadditive.sum_comp,
    sigmaConst_map_app, Sigma.ι_map]

/-- Base change for a pullback square with finite vertical fibers. No preservation
of pullbacks by `sigmaConst.obj R` is assumed. -/
theorem sigmaConstTransfer_baseChange {A B U V : Type w} {t : A ⟶ B} {l : A ⟶ U}
    {r : B ⟶ V} {b : U ⟶ V} (h : IsPullback t l r b)
    (hl : ∀ x : U, Finite {a : A // l a = x})
    (hr : ∀ y : V, Finite {a : B // r a = y}) (R : C) :
    (sigmaConst.obj R).map b ≫ sigmaConstTransfer r hr R =
      sigmaConstTransfer l hl R ≫ (sigmaConst.obj R).map t := by
  classical
  apply Sigma.hom_ext
  intro x
  let := hl x
  let := hr (b x)
  let := Fintype.ofFinite {a : A // l a = x}
  let := Fintype.ofFinite {y : B // r y = b x}
  rw [← Category.assoc, sigmaConst_obj_map, Sigma.ι_comp_map', Category.id_comp,
    ι_sigmaConstTransfer, ι_sigmaConstTransfer_assoc]
  simp only [finsum_eq_sum_of_fintype, Preadditive.sum_comp, sigmaConst_obj_map,
    Sigma.ι_comp_map', Category.id_comp]
  exact ((Types.pullbackFiberEquiv h x).sum_comp
    (fun y : {y : B // r y = b x} ↦ Sigma.ι (fun _ : B ↦ R) y.val)).symm

/-- Transfer on coproduct-valued diagrams for an equifibered natural transformation. -/
noncomputable def equifiberedSigmaTransfer
    {D : Type uD} [Category.{vD} D] {F G : D ⥤ Type w} (p : F ⟶ G)
    (hp : NatTrans.Equifibered p)
    (hf : ∀ j (g : G.obj j), Finite {f : F.obj j // p.app j f = g}) (R : C) :
    G ⋙ sigmaConst.obj R ⟶ F ⋙ sigmaConst.obj R where
  app j := sigmaConstTransfer (p.app j) (hf j) R
  naturality i j α := sigmaConstTransfer_baseChange (hp α) (hf i) (hf j) R

@[simp]
theorem equifiberedSigmaTransfer_app
    {D : Type uD} [Category.{vD} D] {F G : D ⥤ Type w} (p : F ⟶ G)
    (hp : NatTrans.Equifibered p)
    (hf : ∀ j (g : G.obj j), Finite {f : F.obj j // p.app j f = g}) (R : C) (j : D) :
    (equifiberedSigmaTransfer p hp hf R).app j =
      sigmaConstTransfer (p.app j) (hf j) R := rfl

/-- Diagram transfers compose in reverse order for equifibered maps. -/
theorem equifiberedSigmaTransfer_comp
    {D : Type uD} [Category.{vD} D] {F G H : D ⥤ Type w} (p : F ⟶ G) (q : G ⟶ H)
    (hp : NatTrans.Equifibered p) (hq : NatTrans.Equifibered q)
    (hf : ∀ j (g : G.obj j), Finite {f : F.obj j // p.app j f = g})
    (hg : ∀ j (h : H.obj j), Finite {g : G.obj j // q.app j g = h}) (R : C) :
    equifiberedSigmaTransfer (p ≫ q) (hp.comp hq)
        (fun j ↦ Types.finite_fiber_comp (p.app j) (q.app j) (hf j) (hg j)) R =
      equifiberedSigmaTransfer q hq hg R ≫ equifiberedSigmaTransfer p hp hf R := by
  ext j
  exact sigmaConstTransfer_comp (p.app j) (q.app j) (hf j) (hg j) R

/-- Coefficient naturality for the diagram transfer. -/
theorem equifiberedSigmaTransfer_coefficient
    {D : Type uD} [Category.{vD} D] {F G : D ⥤ Type w} (p : F ⟶ G)
    (hp : NatTrans.Equifibered p)
    (hf : ∀ j (g : G.obj j), Finite {f : F.obj j // p.app j f = g})
    {R R' : C} (a : R ⟶ R') :
    whiskerLeft G (sigmaConst.map a) ≫ equifiberedSigmaTransfer p hp hf R' =
      equifiberedSigmaTransfer p hp hf R ≫ whiskerLeft F (sigmaConst.map a) := by
  ext j
  exact sigmaConstTransfer_coefficient (p.app j) (hf j) a

/-- Transfer followed by pushforward counts the fiber on each generator. -/
@[reassoc]
theorem ι_sigmaConstTransfer_push {A B : Type w} (f : A ⟶ B)
    (hf : ∀ b : B, Finite {a : A // f a = b}) (R : C) (b : B) :
    Sigma.ι (fun _ : B ↦ R) b ≫ sigmaConstTransfer f hf R ≫ (sigmaConst.obj R).map f =
      Nat.card {a : A // f a = b} • Sigma.ι (fun _ : B ↦ R) b := by
  classical
  let := hf b
  let := Fintype.ofFinite {a : A // f a = b}
  rw [ι_sigmaConstTransfer_assoc, finsum_eq_sum_of_fintype, Preadditive.sum_comp]
  simp only [sigmaConst_obj_map, Sigma.ι_comp_map', Category.id_comp]
  calc
    _ = ∑ _ : {a : A // f a = b}, Sigma.ι (fun _ : B ↦ R) b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [a.property]
    _ = _ := by simp [Nat.card_eq_fintype_card]

end CategoryTheory

namespace SSet

variable {F G : SSet.{w}} (p : F ⟶ G) (hp : NatTrans.Equifibered p)

/-- Restriction along any simplicial operator identifies its source and target fibers. -/
noncomputable def equifiberedFiberEquiv {i j : SimplexCategoryᵒᵖ} (α : i ⟶ j) (g : G.obj i) :
    {f : F.obj i // p.app i f = g} ≃
      {f : F.obj j // p.app j f = G.map α g} :=
  Types.pullbackFiberEquiv (hp α) g

@[simp]
theorem equifiberedFiberEquiv_apply {i j : SimplexCategoryᵒᵖ} (α : i ⟶ j) (g : G.obj i)
    (f : {f : F.obj i // p.app i f = g}) :
    (equifiberedFiberEquiv p hp α g f).val = F.map α f := rfl

include hp in
/-- Finite vertex fibers imply finite fibers in every simplicial degree. -/
theorem finite_fiber_of_finite_vertices
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g})
    (j : SimplexCategoryᵒᵖ) (g : G.obj j) : Finite {f : F.obj j // p.app j f = g} := by
  let α : j ⟶ op ⦋0⦌ := (SimplexCategory.const ⦋0⦌ j.unop 0).op
  let := hf (G.map α g)
  exact Finite.of_equiv _ (equifiberedFiberEquiv p hp α g).symm

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- Transfer on the all-simplex chain complexes of an equifibered map, requiring
only finite vertex fibers and no constant degree. -/
noncomputable def chainComplexTransfer
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g}) (R : C) :
    G.chainComplex R ⟶ F.chainComplex R :=
  (AlgebraicTopology.alternatingFaceMapComplex C).map
    (equifiberedSigmaTransfer p hp (finite_fiber_of_finite_vertices p hp hf) R)

/-- The component of the chain transfer is the coproduct transfer. -/
@[simp]
theorem chainComplexTransfer_f
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g}) (R : C) (n : ℕ) :
    (chainComplexTransfer p hp hf R).f n =
      sigmaConstTransfer (p.app (op ⦋n⦌))
        (finite_fiber_of_finite_vertices p hp hf (op ⦋n⦌)) R := rfl

/-- Chain transfers compose in reverse order, with only finite vertex fibers. -/
theorem chainComplexTransfer_comp {H : SSet.{w}} (q : G ⟶ H)
    (hq : NatTrans.Equifibered q)
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g})
    (hg : ∀ h : H _⦋0⦌, Finite {g : G _⦋0⦌ // q.app _ g = h}) (R : C) :
    chainComplexTransfer (p ≫ q) (hp.comp hq)
        (Types.finite_fiber_comp (p.app _) (q.app _) hf hg) R =
      chainComplexTransfer q hq hg R ≫ chainComplexTransfer p hp hf R := by
  simpa only [chainComplexTransfer, Functor.map_comp] using
    congrArg (AlgebraicTopology.alternatingFaceMapComplex C).map
      (equifiberedSigmaTransfer_comp p q hp hq
        (finite_fiber_of_finite_vertices p hp hf)
        (finite_fiber_of_finite_vertices q hq hg) R)

/-- The generator formula in every chain degree. -/
@[reassoc]
theorem ι_chainComplexTransfer_f
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g}) (R : C)
    {n : ℕ} (g : G _⦋n⦌) :
    G.ιChainComplex g ≫ (chainComplexTransfer p hp hf R).f n =
      ∑ᶠ f : {f : F _⦋n⦌ // p.app _ f = g}, F.ιChainComplex f.val :=
  ι_sigmaConstTransfer _ _ _ _

/-- Transfer followed by pushforward counts the fiber of a simplex, without a
constant-sheet assumption. -/
@[reassoc]
theorem ι_chainComplexTransfer_push
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g}) (R : C)
    {n : ℕ} (g : G _⦋n⦌) :
    G.ιChainComplex g ≫ (chainComplexTransfer p hp hf R).f n ≫
        (chainComplexMap p R).f n =
      Nat.card {f : F _⦋n⦌ // p.app _ f = g} • G.ιChainComplex g :=
  ι_sigmaConstTransfer_push _ _ _ _

/-- Chain transfer is natural in the coefficient object. -/
theorem chainComplexTransfer_coefficient
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g})
    {R R' : C} (a : R ⟶ R') :
    ((chainComplexFunctor C).map a).app G ≫ chainComplexTransfer p hp hf R' =
      chainComplexTransfer p hp hf R ≫ ((chainComplexFunctor C).map a).app F := by
  ext n : 1
  change (sigmaConst.map a).app (G.obj (op ⦋n⦌)) ≫
      sigmaConstTransfer (p.app (op ⦋n⦌))
        (finite_fiber_of_finite_vertices p hp hf (op ⦋n⦌)) R' =
    sigmaConstTransfer (p.app (op ⦋n⦌))
        (finite_fiber_of_finite_vertices p hp hf (op ⦋n⦌)) R ≫
      (sigmaConst.map a).app (F.obj (op ⦋n⦌))
  exact sigmaConstTransfer_coefficient (p.app (op ⦋n⦌))
    (finite_fiber_of_finite_vertices p hp hf (op ⦋n⦌)) a

/-- A fixed vertex-fiber cardinal gives the same sheet number in all chain degrees.
The constructor itself has no fixed-sheet hypothesis. -/
theorem chainComplexTransfer_comp_map
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g})
    (R : C) (d : ℕ)
    (hd : ∀ g : G _⦋0⦌, Nat.card {f : F _⦋0⦌ // p.app _ f = g} = d) :
    chainComplexTransfer p hp hf R ≫ chainComplexMap p R = d • 𝟙 (G.chainComplex R) := by
  ext n : 1
  apply SSet.chainComplex_hom_ext
  intro g
  let α : op ⦋n⦌ ⟶ op ⦋0⦌ := (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op
  have hcard : Nat.card {f : F _⦋n⦌ // p.app _ f = g} = d :=
    (Nat.card_congr (equifiberedFiberEquiv p hp α g)).trans (hd (G.map α g))
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.nsmul_f_apply,
    HomologicalComplex.id_f, Preadditive.comp_nsmul, Category.comp_id, hcard] using
    ι_chainComplexTransfer_push p hp hf R g

variable [CategoryWithHomology C]

/-- The induced transfer on simplicial homology, with no new homology model. -/
noncomputable def homologyTransfer
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g}) (R : C) (q : ℕ) :
    G.homology R q ⟶ F.homology R q :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) q).map
    (chainComplexTransfer p hp hf R)

/-- The homology functor carries reverse-order chain-transfer composition to homology. -/
theorem homologyTransfer_comp {H : SSet.{w}} (q : G ⟶ H)
    (hq : NatTrans.Equifibered q)
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g})
    (hg : ∀ h : H _⦋0⦌, Finite {g : G _⦋0⦌ // q.app _ g = h}) (R : C) (n : ℕ) :
    homologyTransfer (p ≫ q) (hp.comp hq)
        (Types.finite_fiber_comp (p.app _) (q.app _) hf hg) R n =
      homologyTransfer q hq hg R n ≫ homologyTransfer p hp hf R n := by
  let T := HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n
  change T.map (chainComplexTransfer (p ≫ q) (hp.comp hq)
      (Types.finite_fiber_comp (p.app _) (q.app _) hf hg) R) =
    T.map (chainComplexTransfer q hq hg R) ≫ T.map (chainComplexTransfer p hp hf R)
  exact (congrArg T.map (chainComplexTransfer_comp p hp q hq hf hg R)).trans
    (T.map_comp _ _)

/-- The fixed-sheet identity descends to homology. -/
theorem homologyTransfer_comp_map
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g})
    (R : C) (d q : ℕ)
    (hd : ∀ g : G _⦋0⦌, Nat.card {f : F _⦋0⦌ // p.app _ f = g} = d) :
    homologyTransfer p hp hf R q ≫ SSet.homologyMap p R q =
      d • 𝟙 (G.homology R q) := by
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) q
  change H.map (chainComplexTransfer p hp hf R) ≫ H.map (chainComplexMap p R) =
    d • 𝟙 (H.obj (G.chainComplex R))
  rw [← H.map_comp, chainComplexTransfer_comp_map p hp hf R d hd,
    H.map_nsmul, H.map_id]

end SSet
