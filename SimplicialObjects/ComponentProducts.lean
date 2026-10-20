/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Connected components of binary simplicial products

The connected components of a binary product of simplicial sets are the product
of their connected components. The forward map is induced by the two projections.
The inverse pairs vertices using the Cartesian monoidal comparison, then descends
in each variable through Mathlib's `SSet.π₀.lift`.

The vertex constructor `SSet.prodVertex` and its projection, reconstruction and
naturality lemmas give an interface to vertices of the categorical product.

## Implementation notes

The descent uses constant edges in the other variable. This argument concerns
binary simplicial products, not arbitrary semisimplicial or infinite products.
The construction reuses Mathlib's connected components and Cartesian monoidal
structure; it introduces no additional component relation.
-/

@[expose] public section

universe w

open CategoryTheory Limits MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

variable {X Y X' Y' : SSet.{w}}

/-- Pair vertices using the comparison from the Cartesian tensor to the
categorical binary product. -/
noncomputable def prodVertex (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (Limits.prod X Y) _⦋0⦌ :=
  let β : X ⊗ Y ≅ Limits.prod X Y :=
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
      (limit.isLimit (pair X Y))
  β.hom.app (op ⦋0⦌) (x, y)

/-- The first projection of a paired vertex. -/
@[simp]
lemma prodVertex_fst (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (Limits.prod.fst : Limits.prod X Y ⟶ X).app (op ⦋0⦌) (prodVertex x y) = x := by
  let β : X ⊗ Y ≅ Limits.prod X Y :=
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
      (limit.isLimit (pair X Y))
  have h : β.hom ≫ (Limits.prod.fst : Limits.prod X Y ⟶ X) =
      CartesianMonoidalCategory.fst X Y :=
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso_hom_comp
      (limit.isLimit (pair X Y)) (Discrete.mk WalkingPair.left)
  change (β.hom ≫ (Limits.prod.fst : Limits.prod X Y ⟶ X)).app (op ⦋0⦌) (x, y) = x
  rw [h]
  rfl

/-- The second projection of a paired vertex. -/
@[simp]
lemma prodVertex_snd (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (Limits.prod.snd : Limits.prod X Y ⟶ Y).app (op ⦋0⦌) (prodVertex x y) = y := by
  let β : X ⊗ Y ≅ Limits.prod X Y :=
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
      (limit.isLimit (pair X Y))
  have h : β.hom ≫ (Limits.prod.snd : Limits.prod X Y ⟶ Y) =
      CartesianMonoidalCategory.snd X Y :=
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso_hom_comp
      (limit.isLimit (pair X Y)) (Discrete.mk WalkingPair.right)
  change (β.hom ≫ (Limits.prod.snd : Limits.prod X Y ⟶ Y)).app (op ⦋0⦌) (x, y) = y
  rw [h]
  rfl

/-- A product vertex is reconstructed from its two projections. -/
@[simp]
lemma prodVertex_eta (z : (Limits.prod X Y) _⦋0⦌) :
    prodVertex ((Limits.prod.fst : Limits.prod X Y ⟶ X).app (op ⦋0⦌) z)
      ((Limits.prod.snd : Limits.prod X Y ⟶ Y).app (op ⦋0⦌) z) = z := by
  let β : X ⊗ Y ≅ Limits.prod X Y :=
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
      (limit.isLimit (pair X Y))
  have h : prodVertex (β.inv.app (op ⦋0⦌) z).1 (β.inv.app (op ⦋0⦌) z).2 = z := by
    change (β.inv ≫ β.hom).app (op ⦋0⦌) z = z
    rw [β.inv_hom_id]
    rfl
  rw [← h, prodVertex_fst, prodVertex_snd]

/-- Pairing vertices commutes with maps in both factors. -/
@[simp]
lemma prodVertex_map (f : X ⟶ X') (g : Y ⟶ Y')
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (Limits.prod.map f g).app (op ⦋0⦌) (prodVertex x y) =
      prodVertex (f.app (op ⦋0⦌) x) (g.app (op ⦋0⦌) y) := by
  calc
    (Limits.prod.map f g).app (op ⦋0⦌) (prodVertex x y) =
        prodVertex
          ((Limits.prod.fst : Limits.prod X' Y' ⟶ X').app (op ⦋0⦌)
            ((Limits.prod.map f g).app (op ⦋0⦌) (prodVertex x y)))
          ((Limits.prod.snd : Limits.prod X' Y' ⟶ Y').app (op ⦋0⦌)
            ((Limits.prod.map f g).app (op ⦋0⦌) (prodVertex x y))) :=
      (prodVertex_eta _).symm
    _ = _ := by
      congr 1
      · change (Limits.prod.map f g ≫ Limits.prod.fst).app (op ⦋0⦌)
          (prodVertex x y) = _
        rw [Limits.prod.map_fst]
        change f.app (op ⦋0⦌)
          ((Limits.prod.fst : Limits.prod X Y ⟶ X).app (op ⦋0⦌) (prodVertex x y)) = _
        rw [prodVertex_fst]
      · change (Limits.prod.map f g ≫ Limits.prod.snd).app (op ⦋0⦌)
          (prodVertex x y) = _
        rw [Limits.prod.map_snd]
        change g.app (op ⦋0⦌)
          ((Limits.prod.snd : Limits.prod X Y ⟶ Y).app (op ⦋0⦌) (prodVertex x y)) = _
        rw [prodVertex_snd]

private def tensorEdge {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (e : X.Edge x₀ x₁) (d : Y.Edge y₀ y₁) :
    (X ⊗ Y).Edge (x₀, y₀) (x₁, y₁) :=
  Edge.mk (e.edge, d.edge)
    (by
      change (X.δ 1 e.edge, Y.δ 1 d.edge) = (x₀, y₀)
      rw [e.src_eq, d.src_eq])
    (by
      change (X.δ 0 e.edge, Y.δ 0 d.edge) = (x₁, y₁)
      rw [e.tgt_eq, d.tgt_eq])

private lemma prodVertex_sound
    {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (e : X.Edge x₀ x₁) (d : Y.Edge y₀ y₁) :
    π₀.mk (prodVertex x₀ y₀) = π₀.mk (prodVertex x₁ y₁) := by
  let β : X ⊗ Y ≅ Limits.prod X Y :=
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
      (limit.isLimit (pair X Y))
  exact π₀.sound ((tensorEdge e d).map β.hom)

/-- Connected components of a binary simplicial product are pairs of connected
components. The forward map is induced directly by the product projections. -/
noncomputable def piZeroProdEquiv (X Y : SSet.{w}) :
    π₀ (Limits.prod X Y) ≃ (π₀ X × π₀ Y) where
  toFun z := (mapπ₀ Limits.prod.fst z, mapπ₀ Limits.prod.snd z)
  invFun p :=
    π₀.lift
      (fun x : X _⦋0⦌ ↦
        π₀.lift (fun y : Y _⦋0⦌ ↦ π₀.mk (prodVertex x y))
          (fun _ _ e ↦ by exact prodVertex_sound (Edge.id x) e))
      (fun _ _ e ↦ by
        funext b
        obtain ⟨y, rfl⟩ := π₀.mk_surjective b
        simp only [π₀.lift_mk]
        exact prodVertex_sound e (Edge.id y)) p.1 p.2
  left_inv z := by
    obtain ⟨z, rfl⟩ := π₀.mk_surjective z
    change π₀.mk (prodVertex
      ((Limits.prod.fst : Limits.prod X Y ⟶ X).app (op ⦋0⦌) z)
      ((Limits.prod.snd : Limits.prod X Y ⟶ Y).app (op ⦋0⦌) z)) = π₀.mk z
    rw [prodVertex_eta]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    obtain ⟨x, rfl⟩ := π₀.mk_surjective a
    obtain ⟨y, rfl⟩ := π₀.mk_surjective b
    change
      (mapπ₀ Limits.prod.fst (π₀.mk (prodVertex x y)),
        mapπ₀ Limits.prod.snd (π₀.mk (prodVertex x y))) = _
    simp only [mapπ₀_mk, prodVertex_fst, prodVertex_snd]

/-- The component equivalence acts by the two projection maps. -/
lemma piZeroProdEquiv_apply (z : π₀ (Limits.prod X Y)) :
    piZeroProdEquiv X Y z = (mapπ₀ Limits.prod.fst z, mapπ₀ Limits.prod.snd z) :=
  rfl

/-- The forward representative rule uses the projections of a product vertex. -/
@[simp]
lemma piZeroProdEquiv_mk (z : (Limits.prod X Y) _⦋0⦌) :
    piZeroProdEquiv X Y (π₀.mk z) =
      (π₀.mk ((Limits.prod.fst : Limits.prod X Y ⟶ X).app (op ⦋0⦌) z),
        π₀.mk ((Limits.prod.snd : Limits.prod X Y ⟶ Y).app (op ⦋0⦌) z)) :=
  rfl

/-- The inverse sends a pair of vertex components to the component of their
paired vertex under the Cartesian monoidal comparison. -/
@[simp]
lemma piZeroProdEquiv_symm_mk (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (piZeroProdEquiv X Y).symm (π₀.mk x, π₀.mk y) = π₀.mk (prodVertex x y) :=
  rfl

/-- Naturality of the component equivalence in both simplicial factors. -/
lemma piZeroProdEquiv_naturality (f : X ⟶ X') (g : Y ⟶ Y')
    (z : π₀ (Limits.prod X Y)) :
    piZeroProdEquiv X' Y' (mapπ₀ (Limits.prod.map f g) z) =
      (mapπ₀ f (piZeroProdEquiv X Y z).1, mapπ₀ g (piZeroProdEquiv X Y z).2) := by
  apply Prod.ext
  · change mapπ₀ Limits.prod.fst (mapπ₀ (Limits.prod.map f g) z) =
      mapπ₀ f (mapπ₀ Limits.prod.fst z)
    rw [← mapπ₀_comp_apply, Limits.prod.map_fst, mapπ₀_comp_apply]
  · change mapπ₀ Limits.prod.snd (mapπ₀ (Limits.prod.map f g) z) =
      mapπ₀ g (mapπ₀ Limits.prod.snd z)
    rw [← mapπ₀_comp_apply, Limits.prod.map_snd, mapπ₀_comp_apply]

/-- Inverse naturality, with a pair of components as the input. -/
lemma piZeroProdEquiv_symm_naturality (f : X ⟶ X') (g : Y ⟶ Y')
    (p : π₀ X × π₀ Y) :
    mapπ₀ (Limits.prod.map f g) ((piZeroProdEquiv X Y).symm p) =
      (piZeroProdEquiv X' Y').symm (mapπ₀ f p.1, mapπ₀ g p.2) := by
  apply (piZeroProdEquiv X' Y').injective
  simp only [piZeroProdEquiv_naturality, Equiv.apply_symm_apply]

/-- The forward representative rule uniquely determines the component map. -/
lemma piZeroProdEquiv_unique
    (f : π₀ (Limits.prod X Y) → (π₀ X × π₀ Y))
    (h : ∀ z : (Limits.prod X Y) _⦋0⦌,
      f (π₀.mk z) =
        (π₀.mk ((Limits.prod.fst : Limits.prod X Y ⟶ X).app (op ⦋0⦌) z),
          π₀.mk ((Limits.prod.snd : Limits.prod X Y ⟶ Y).app (op ⦋0⦌) z))) :
    f = piZeroProdEquiv X Y := by
  funext z
  obtain ⟨z, rfl⟩ := π₀.mk_surjective z
  exact h z

/-- The inverse representative rule uniquely determines the inverse component map. -/
lemma piZeroProdEquiv_symm_unique
    (f : (π₀ X × π₀ Y) → π₀ (Limits.prod X Y))
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌),
      f (π₀.mk x, π₀.mk y) = π₀.mk (prodVertex x y)) :
    f = (piZeroProdEquiv X Y).symm := by
  apply funext
  rintro ⟨a, b⟩
  obtain ⟨x, rfl⟩ := π₀.mk_surjective a
  obtain ⟨y, rfl⟩ := π₀.mk_surjective b
  exact h x y

end SSet
