/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.Normalization
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# An integral tensor presentation of normalized chains

A simplex has an integral class in the free abelian group on nondegenerate
simplices, with degenerate simplices sent to zero. The boundary is specified by
alternating faces, starting with a positive zeroth face. Tensoring this boundary
with an abelian group gives the differential of `SSet.tensorNormalizedChainComplex`.
Its comparison with normalized coefficient chains is assembled from degreewise
isomorphisms, not used to define the boundary.

The coefficient group, simplicial set and padding have independent universes.
Only the canonical integer-module structures are used. This construction concerns
arbitrary simplicial sets; it does not identify a simplicial set with the singular
simplices of a topological space.

## Implementation notes

The normalized-degree coordinates use Mathlib's normalized cofan universal
property, coproduct/direct-sum isomorphism and inverse Finsupp/direct-sum
isomorphism. The tensor coordinates use `TensorProduct.finsuppScalarLeft`.
No choice of a normalization or comparison is an argument to these constructions.

## References

* May, *A Concise Course in Algebraic Topology*, revised edition, §16.1, motivates
  the integral tensor presentation.
* Mathlib supplies the normalized cofan, direct-sum and tensor constructions.
* `SimplicialObjects.Normalization` supplies normalization for coefficient-valued
  simplicial morphisms and the additive coefficient-comparison coherence laws.
-/

@[expose] public section

universe a w p r v

open CategoryTheory Limits Opposite
open scoped Simplicial TensorProduct

namespace SSet

/-- The normalized integral class of a simplex: its nondegenerate generator,
or zero if the simplex is degenerate. -/
noncomputable def normalizedIntegralSimplex (S : SSet.{w}) {n : ℕ} (s : S _⦋n⦌) :
    S.nonDegenerate n →₀ ℤ := by
  classical
  exact if h : s ∈ S.nonDegenerate n then Finsupp.single ⟨s, h⟩ 1 else 0

/-- A nondegenerate simplex represents its integral basis vector. -/
@[simp]
theorem normalizedIntegralSimplex_of_mem_nonDegenerate (S : SSet.{w}) {n : ℕ}
    (s : S _⦋n⦌) (hs : s ∈ S.nonDegenerate n) :
    S.normalizedIntegralSimplex s = Finsupp.single ⟨s, hs⟩ 1 := by
  classical
  simp [normalizedIntegralSimplex, hs]

/-- A degenerate simplex has zero integral class. -/
@[simp]
theorem normalizedIntegralSimplex_of_mem_degenerate (S : SSet.{w}) {n : ℕ}
    (s : S _⦋n⦌) (hs : s ∈ S.degenerate n) :
    S.normalizedIntegralSimplex s = 0 := by
  classical
  simp [normalizedIntegralSimplex, (S.mem_degenerate_iff_notMem_nonDegenerate s).mp hs]

/-- The alternating boundary on nondegenerate integral generators.
The zeroth face has positive sign; degenerate faces contribute zero. -/
noncomputable def normalizedIntegralBoundary (S : SSet.{w}) (n : ℕ) :
    (S.nonDegenerate (n + 1) →₀ ℤ) →ₗ[ℤ] (S.nonDegenerate n →₀ ℤ) :=
  Finsupp.lift _ ℤ _ fun s ↦
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • S.normalizedIntegralSimplex (S.δ i s.val)

/-- The boundary of a nondegenerate generator is its alternating sum of face classes. -/
@[simp]
theorem normalizedIntegralBoundary_single (S : SSet.{w}) (n : ℕ)
    (s : S.nonDegenerate (n + 1)) :
    S.normalizedIntegralBoundary n (Finsupp.single s 1) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • S.normalizedIntegralSimplex (S.δ i s.val) := by
  classical
  simp [normalizedIntegralBoundary, Finsupp.lift_apply]

/-- The alternating generator formula characterizes the integral boundary among linear maps. -/
theorem normalizedIntegralBoundary_eq_iff (S : SSet.{w}) (n : ℕ)
    (f : (S.nonDegenerate (n + 1) →₀ ℤ) →ₗ[ℤ] (S.nonDegenerate n →₀ ℤ)) :
    f = S.normalizedIntegralBoundary n ↔ ∀ s : S.nonDegenerate (n + 1),
      f (Finsupp.single s 1) =
        ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • S.normalizedIntegralSimplex (S.δ i s.val) := by
  constructor
  · rintro rfl s
    exact S.normalizedIntegralBoundary_single n s
  · intro h
    apply (Finsupp.lift (S.nonDegenerate n →₀ ℤ) ℤ (S.nonDegenerate (n + 1))).symm.injective
    funext s
    simpa only [Finsupp.lift_symm_apply, normalizedIntegralBoundary_single] using h s

/-- Normalized chains in one degree as finitely supported coefficient families.
The ring universe is independent of the simplex and module universes. -/
noncomputable def normalizedChainComplexXIsoFinsupp {R : Type r} [Ring R]
    (S : SSet.{w}) (M : ModuleCat.{max w v} R) (n : ℕ) :
    (S.normalizedChainComplex M).X n ≅ ModuleCat.of R (S.nonDegenerate n →₀ M) := by
  classical
  exact
    (S.isColimitCofanNormalizedChainComplex M n).coconePointUniqueUpToIso
        (colimit.isColimit (Discrete.functor (fun _ : S.nonDegenerate n ↦ M))) ≪≫
      ModuleCat.coprodIsoDirectSum (fun _ : S.nonDegenerate n ↦ M) ≪≫
      (finsuppLEquivDirectSum R M (S.nonDegenerate n)).symm.toModuleIso

/-- The normalized-degree coordinates take each cofan inclusion to a single coefficient. -/
@[reassoc]
theorem ιNormalizedChainComplex_normalizedChainComplexXIsoFinsupp_hom
    {R : Type r} [Ring R] (S : SSet.{w}) (M : ModuleCat.{max w v} R)
    (n : ℕ) (s : S.nonDegenerate n) :
    S.ιNormalizedChainComplex (R := M) s.val ≫ (S.normalizedChainComplexXIsoFinsupp M n).hom =
      ModuleCat.ofHom (Finsupp.lsingle s) := by
  classical
  let e := (S.isColimitCofanNormalizedChainComplex M n).coconePointUniqueUpToIso
    (colimit.isColimit (Discrete.functor (fun _ : S.nonDegenerate n ↦ M)))
  have he : S.ιNormalizedChainComplex (R := M) s.val ≫ e.hom =
      Sigma.ι (fun _ : S.nonDegenerate n ↦ M) s :=
    (S.isColimitCofanNormalizedChainComplex M n).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit _) (Discrete.mk s)
  calc
    _ = Sigma.ι (fun _ : S.nonDegenerate n ↦ M) s ≫
        (ModuleCat.coprodIsoDirectSum (fun _ : S.nonDegenerate n ↦ M)).hom ≫
          (finsuppLEquivDirectSum R M (S.nonDegenerate n)).symm.toModuleIso.hom := by
      dsimp only [normalizedChainComplexXIsoFinsupp, Iso.trans_hom]
      exact (Category.assoc (S.ιNormalizedChainComplex (R := M) s.val) e.hom
        ((ModuleCat.coprodIsoDirectSum (fun _ : S.nonDegenerate n ↦ M)).hom ≫
          (finsuppLEquivDirectSum R M (S.nonDegenerate n)).symm.toModuleIso.hom)).symm.trans
        (congrArg (fun f : M ⟶ ∐ (fun _ : S.nonDegenerate n ↦ M) ↦ f ≫
          (ModuleCat.coprodIsoDirectSum (fun _ : S.nonDegenerate n ↦ M)).hom ≫
            (finsuppLEquivDirectSum R M (S.nonDegenerate n)).symm.toModuleIso.hom) he)
    _ = _ := by
      rw [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      exact finsuppLEquivDirectSum_symm_lof R M (S.nonDegenerate n) s m

/-- The coordinates of a normalized nondegenerate simplex with coefficient `m`. -/
@[simp]
theorem normalizedChainComplexXIsoFinsupp_hom_ι {R : Type r} [Ring R]
    (S : SSet.{w}) (M : ModuleCat.{max w v} R) (n : ℕ)
    (s : S.nonDegenerate n) (m : M) :
    (S.normalizedChainComplexXIsoFinsupp M n).hom (S.ιNormalizedChainComplex (R := M) s.val m) =
      Finsupp.single s m := by
  have h := congrArg
    (fun f : M ⟶ ModuleCat.of R (S.nonDegenerate n →₀ M) ↦ f.hom)
    (S.ιNormalizedChainComplex_normalizedChainComplexXIsoFinsupp_hom M n s)
  rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  exact (congrArg (fun f : M →ₗ[R] (S.nonDegenerate n →₀ M) ↦ f m) h).trans
    (Finsupp.lsingle_apply s m)

/-- The inverse coordinates insert a single nondegenerate simplex. -/
@[simp]
theorem normalizedChainComplexXIsoFinsupp_inv_single {R : Type r} [Ring R]
    (S : SSet.{w}) (M : ModuleCat.{max w v} R) (n : ℕ)
    (s : S.nonDegenerate n) (m : M) :
    (S.normalizedChainComplexXIsoFinsupp M n).inv (Finsupp.single s m) =
      S.ιNormalizedChainComplex (R := M) s.val m := by
  rw [← S.normalizedChainComplexXIsoFinsupp_hom_ι M n s m]
  exact ModuleCat.inv_hom_apply _ _

/-- The degree-`n` integral tensor group, lifted to the common coefficient universe. -/
noncomputable def tensorNormalizedChainComplexX (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) : ModuleCat.{max a w p} ℤ :=
  ModuleCat.of ℤ (ULift.{max a w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] A))

/-- The integral alternating boundary tensored with the coefficient identity, then lifted. -/
noncomputable def tensorNormalizedBoundary (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedChainComplexX.{a, w, p} A S (n + 1) ⟶
      tensorNormalizedChainComplexX.{a, w, p} A S n :=
  ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
    (S.normalizedIntegralBoundary n).rTensor A ∘ₗ
      (ULift.moduleEquiv (R := ℤ)).toLinearMap)

/-- The tensor boundary on a lifted pure tensor. -/
@[simp]
theorem tensorNormalizedBoundary_tmul (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) (z : S.nonDegenerate (n + 1) →₀ ℤ) (x : A) :
    tensorNormalizedBoundary.{a, w, p} A S n (ULift.up (z ⊗ₜ[ℤ] x)) =
      ULift.up (S.normalizedIntegralBoundary n z ⊗ₜ[ℤ] x) := rfl

/-- The boundary of a tensor generator is the alternating sum of its face classes. -/
@[simp]
theorem tensorNormalizedBoundary_single (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) (s : S.nonDegenerate (n + 1)) (x : A) :
    tensorNormalizedBoundary.{a, w, p} A S n
        (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (ULift.up (S.normalizedIntegralSimplex (S.δ i s.val) ⊗ₜ[ℤ] x) :
          tensorNormalizedChainComplexX.{a, w, p} A S n) := by
  classical
  rw [tensorNormalizedBoundary_tmul, S.normalizedIntegralBoundary_single]
  apply (ULift.moduleEquiv (R := ℤ)).injective
  rw [map_sum]
  simp_rw [map_smul]
  simp only [ULift.moduleEquiv_apply, TensorProduct.sum_tmul,
    ← TensorProduct.smul_tmul']

/-- The tensor differential: successor boundary, and zero in every other bidegree. -/
noncomputable def tensorNormalizedDifferential (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (i j : ℕ) :
    tensorNormalizedChainComplexX.{a, w, p} A S i ⟶
      tensorNormalizedChainComplexX.{a, w, p} A S j :=
  if h : i = j + 1 then by subst i; exact tensorNormalizedBoundary.{a, w, p} A S j else 0

/-- The successor component is the independently specified tensor boundary. -/
@[simp]
theorem tensorNormalizedDifferential_succ (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedDifferential.{a, w, p} A S (n + 1) n =
      tensorNormalizedBoundary.{a, w, p} A S n := by
  simp [tensorNormalizedDifferential]

/-- Non-successor components of the tensor differential vanish. -/
theorem tensorNormalizedDifferential_eq_zero (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (i j : ℕ) (h : i ≠ j + 1) :
    tensorNormalizedDifferential.{a, w, p} A S i j = 0 := by
  simp [tensorNormalizedDifferential, h]

/-- In particular there is no outgoing degree-zero tensor boundary. -/
@[simp]
theorem tensorNormalizedDifferential_zero (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (j : ℕ) :
    tensorNormalizedDifferential.{a, w, p} A S 0 j = 0 :=
  tensorNormalizedDifferential_eq_zero.{a, w, p} A S 0 j (by simp)

/-- Tensor chains in one degree as finitely supported lifted coefficients. -/
noncomputable def tensorNormalizedChainComplexXIsoFinsupp (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedChainComplexX.{a, w, p} A S n ≅
      ModuleCat.of ℤ (S.nonDegenerate n →₀ ULift.{max w p} A) := by
  classical
  exact ((ULift.moduleEquiv (R := ℤ)).trans
    ((TensorProduct.finsuppScalarLeft ℤ A (S.nonDegenerate n)).trans
      (Finsupp.mapRange.linearEquiv (ULift.moduleEquiv (R := ℤ) (M := A)).symm))).toModuleIso

/-- Pure tensors have coefficient `z s • x` in coordinate `s`. -/
@[simp]
theorem tensorNormalizedChainComplexXIsoFinsupp_hom_tmul_apply
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) (n : ℕ)
    (z : S.nonDegenerate n →₀ ℤ) (x : A) (s : S.nonDegenerate n) :
    (tensorNormalizedChainComplexXIsoFinsupp.{a, w, p} A S n).hom
        (ULift.up (z ⊗ₜ[ℤ] x)) s = ULift.up (z s • x) := by
  classical
  dsimp only [tensorNormalizedChainComplexXIsoFinsupp, LinearEquiv.toModuleIso]
  refine (congrArg
    (fun f : ULift.{max a w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] A) →ₗ[ℤ]
        (S.nonDegenerate n →₀ ULift.{max w p} A) ↦
      f (ULift.up (z ⊗ₜ[ℤ] x)) s)
    (ModuleCat.hom_ofHom _)).trans ?_
  apply ULift.ext
  simp

/-- A tensor basis vector has just one nonzero lifted coefficient. -/
@[simp]
theorem tensorNormalizedChainComplexXIsoFinsupp_hom_single
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) (n : ℕ)
    (s : S.nonDegenerate n) (x : A) :
    (tensorNormalizedChainComplexXIsoFinsupp.{a, w, p} A S n).hom
        (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) = Finsupp.single s (ULift.up x) := by
  classical
  apply Finsupp.ext
  intro t
  rw [tensorNormalizedChainComplexXIsoFinsupp_hom_tmul_apply]
  apply ULift.ext
  by_cases h : s = t <;> simp [h]

/-- Inverse tensor coordinates send a single coefficient to the corresponding pure tensor. -/
@[simp]
theorem tensorNormalizedChainComplexXIsoFinsupp_inv_single
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) (n : ℕ)
    (s : S.nonDegenerate n) (x : A) :
    (tensorNormalizedChainComplexXIsoFinsupp.{a, w, p} A S n).inv
        (Finsupp.single s (ULift.up x)) = ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x) := by
  rw [← tensorNormalizedChainComplexXIsoFinsupp_hom_single.{a, w, p} A S n s x]
  exact ModuleCat.inv_hom_apply _ _

/-- Linear maps out of tensor chains are determined by integral generators with coefficients. -/
theorem tensorNormalizedChainComplexX_hom_ext (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) {M : ModuleCat.{max a w p} ℤ}
    {f g : tensorNormalizedChainComplexX.{a, w, p} A S n ⟶ M}
    (h : ∀ (s : S.nonDegenerate n) (x : A),
      f (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
        g (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x))) : f = g := by
  apply (cancel_epi (tensorNormalizedChainComplexXIsoFinsupp.{a, w, p} A S n).inv).mp
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s x
  obtain ⟨x⟩ := x
  change f ((tensorNormalizedChainComplexXIsoFinsupp.{a, w, p} A S n).inv
      (Finsupp.single s (ULift.up x))) =
    g ((tensorNormalizedChainComplexXIsoFinsupp.{a, w, p} A S n).inv
      (Finsupp.single s (ULift.up x)))
  rw [tensorNormalizedChainComplexXIsoFinsupp_inv_single]
  exact h s x

/-- The degreewise comparison to normalized chains, obtained by applying inverse
normalized coordinates after the tensor coordinates. Its target is the whole
normalized degree, not the coefficient Finsupp object. -/
noncomputable def tensorNormalizedChainComplexXIso (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedChainComplexX.{a, w, p} A S n ≅
      (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X n :=
  tensorNormalizedChainComplexXIsoFinsupp.{a, w, p} A S n ≪≫
    (S.normalizedChainComplexXIsoFinsupp (ModuleCat.of ℤ (ULift.{max w p} A)) n).symm

/-- Composing the comparison with normalized coordinates recovers tensor coordinates. -/
@[reassoc (attr := simp)]
theorem tensorNormalizedChainComplexXIso_hom_coordinates (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) :
    (tensorNormalizedChainComplexXIso.{a, w, p} A S n).hom ≫
        (S.normalizedChainComplexXIsoFinsupp (ModuleCat.of ℤ (ULift.{max w p} A)) n).hom =
      (tensorNormalizedChainComplexXIsoFinsupp.{a, w, p} A S n).hom := by
  simp [tensorNormalizedChainComplexXIso]

/-- The degreewise comparison sends a tensor generator to the normalized simplex. -/
@[simp]
theorem tensorNormalizedChainComplexXIso_hom_single (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) (s : S.nonDegenerate n) (x : A) :
    (tensorNormalizedChainComplexXIso.{a, w, p} A S n).hom
        (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
      S.ιNormalizedChainComplex (R := ModuleCat.of ℤ (ULift.{max w p} A)) s.val (ULift.up x) := by
  dsimp only [tensorNormalizedChainComplexXIso, Iso.trans_hom, Iso.symm_hom]
  exact (congrArg
    (fun f : tensorNormalizedChainComplexX.{a, w, p} A S n →ₗ[ℤ]
        (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X n ↦
      f (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)))
    (ModuleCat.hom_comp _ _)).trans
      ((congrArg
        (fun z : S.nonDegenerate n →₀ ULift.{max w p} A ↦
          (S.normalizedChainComplexXIsoFinsupp
            (ModuleCat.of ℤ (ULift.{max w p} A)) n).inv z)
        (tensorNormalizedChainComplexXIsoFinsupp_hom_single.{a, w, p} A S n s x)).trans
        (S.normalizedChainComplexXIsoFinsupp_inv_single
          (ModuleCat.of ℤ (ULift.{max w p} A)) n s (ULift.up x)))

/-- The degreewise comparison formula holds for every simplex, including degenerate ones. -/
@[simp]
theorem tensorNormalizedChainComplexXIso_hom_simplex (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) {n : ℕ} (s : S _⦋n⦌) (x : A) :
    (tensorNormalizedChainComplexXIso.{a, w, p} A S n).hom
        (ULift.up (S.normalizedIntegralSimplex s ⊗ₜ[ℤ] x)) =
      S.ιNormalizedChainComplex (R := ModuleCat.of ℤ (ULift.{max w p} A)) s (ULift.up x) := by
  classical
  by_cases hs : s ∈ S.nonDegenerate n
  · rw [S.normalizedIntegralSimplex_of_mem_nonDegenerate s hs]
    exact tensorNormalizedChainComplexXIso_hom_single.{a, w, p} A S n ⟨s, hs⟩ x
  · have hd := (S.mem_degenerate_iff_notMem_nonDegenerate s).mpr hs
    rw [S.normalizedIntegralSimplex_of_mem_degenerate s hd, TensorProduct.zero_tmul]
    have hz := S.ιNormalizedChainComplex_eq_zero
      (R := ModuleCat.of ℤ (ULift.{max w p} A)) s hd
    rw [hz]
    exact map_zero _

/-- The inverse comparison recovers a tensor generator from a normalized inclusion. -/
@[simp]
theorem tensorNormalizedChainComplexXIso_inv_ι (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) (s : S.nonDegenerate n) (x : A) :
    (tensorNormalizedChainComplexXIso.{a, w, p} A S n).inv
        (S.ιNormalizedChainComplex (R := ModuleCat.of ℤ (ULift.{max w p} A)) s.val (ULift.up x)) =
      ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x) := by
  rw [← tensorNormalizedChainComplexXIso_hom_single.{a, w, p} A S n s x]
  exact ModuleCat.inv_hom_apply _ _

/-- The degree comparisons intertwine the independent tensor boundary with the
normalized coefficient differential. -/
theorem tensorNormalizedChainComplexXIso_hom_d (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (i j : ℕ) :
    (tensorNormalizedChainComplexXIso.{a, w, p} A S i).hom ≫
        (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).d i j =
      tensorNormalizedDifferential.{a, w, p} A S i j ≫
        (tensorNormalizedChainComplexXIso.{a, w, p} A S j).hom := by
  classical
  by_cases hij : i = j + 1
  · subst i
    rw [tensorNormalizedDifferential_succ]
    apply tensorNormalizedChainComplexX_hom_ext.{a, w, p} A S (j + 1)
    intro s x
    change
      ((S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).d (j + 1) j).hom
          ((tensorNormalizedChainComplexXIso.{a, w, p} A S (j + 1)).hom.hom
            (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x))) =
        (tensorNormalizedChainComplexXIso.{a, w, p} A S j).hom.hom
          ((tensorNormalizedBoundary.{a, w, p} A S j).hom
            (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)))
    have hd :
        ((S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).d (j + 1) j).hom
            ((S.ιNormalizedChainComplex
              (R := ModuleCat.of ℤ (ULift.{max w p} A)) s.val).hom (ULift.up x)) =
          ∑ k : Fin (j + 2), ((-1 : ℤ) ^ k.val) •
            (S.ιNormalizedChainComplex
              (R := ModuleCat.of ℤ (ULift.{max w p} A)) (S.δ k s.val)).hom (ULift.up x) := by
      -- Evaluation is additive, so it preserves the alternating sum.
      let ev :
          (ModuleCat.of ℤ (ULift.{max w p} A) ⟶
            (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X j) →+
              (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X j :=
        (LinearMap.evalAddMonoidHom
          (ULift.up x : ModuleCat.of ℤ (ULift.{max w p} A))).comp
            ModuleCat.homAddEquiv.toAddMonoidHom
      exact (congrArg ev
        (S.ιNormalizedChainComplex_d
          (R := ModuleCat.of ℤ (ULift.{max w p} A)) s.val)).trans
        ((map_sum ev _ Finset.univ).trans
          (Finset.sum_congr rfl (fun k _ ↦ map_zsmul ev ((-1 : ℤ) ^ k.val) _)))
    refine (congrArg
      (fun z : (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X (j + 1) ↦
        ((S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).d (j + 1) j).hom z)
      (tensorNormalizedChainComplexXIso_hom_single.{a, w, p} A S (j + 1) s x)).trans
        (hd.trans ?_)
    symm
    refine (congrArg
      (fun z : tensorNormalizedChainComplexX.{a, w, p} A S j ↦
        (tensorNormalizedChainComplexXIso.{a, w, p} A S j).hom.hom z)
      (tensorNormalizedBoundary_single.{a, w, p} A S j s x)).trans
        ((map_sum (tensorNormalizedChainComplexXIso.{a, w, p} A S j).hom.hom
          _ Finset.univ).trans ?_)
    apply Finset.sum_congr rfl
    intro k _
    exact (map_zsmul (tensorNormalizedChainComplexXIso.{a, w, p} A S j).hom.hom
      ((-1 : ℤ) ^ k.val) _).trans
      (congrArg
        (fun z : (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X j ↦
          ((-1 : ℤ) ^ k.val) • z)
        (tensorNormalizedChainComplexXIso_hom_simplex.{a, w, p} A S (S.δ k s.val) x))
  · rw [tensorNormalizedDifferential_eq_zero.{a, w, p} A S i j hij,
      (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).shape i j
        (fun h ↦ hij h.symm), comp_zero, zero_comp]

/-- Two successive independently specified tensor differentials have zero composite. -/
theorem tensorNormalizedDifferential_comp (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (i j k : ℕ) :
    tensorNormalizedDifferential.{a, w, p} A S i j ≫
      tensorNormalizedDifferential.{a, w, p} A S j k = 0 := by
  apply (cancel_mono (tensorNormalizedChainComplexXIso.{a, w, p} A S k).hom).mp
  rw [zero_comp, Category.assoc,
    ← tensorNormalizedChainComplexXIso_hom_d.{a, w, p} A S j k,
    ← Category.assoc, ← tensorNormalizedChainComplexXIso_hom_d.{a, w, p} A S i j,
    Category.assoc, HomologicalComplex.d_comp_d, comp_zero]

/-- Normalized integral generators tensored with an abelian group, with the
independently specified alternating boundary. -/
noncomputable def tensorNormalizedChainComplex (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) : ChainComplex (ModuleCat.{max a w p} ℤ) ℕ where
  X := tensorNormalizedChainComplexX.{a, w, p} A S
  d := tensorNormalizedDifferential.{a, w, p} A S
  shape i j hij := tensorNormalizedDifferential_eq_zero.{a, w, p} A S i j (fun h ↦ hij h.symm)
  d_comp_d' i j k _ _ := tensorNormalizedDifferential_comp.{a, w, p} A S i j k

/-- The degree objects are the specified lifted integral tensor groups. -/
theorem tensorNormalizedChainComplex_X (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) :
    (tensorNormalizedChainComplex.{a, w, p} A S).X n =
      ModuleCat.of ℤ (ULift.{max a w p} ((S.nonDegenerate n →₀ ℤ) ⊗[ℤ] A)) := rfl

/-- The successor boundary on lifted pure tensors. -/
@[simp]
theorem tensorNormalizedChainComplex_d_tmul (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) (z : S.nonDegenerate (n + 1) →₀ ℤ) (x : A) :
    (tensorNormalizedChainComplex.{a, w, p} A S).d (n + 1) n (ULift.up (z ⊗ₜ[ℤ] x)) =
      ULift.up (S.normalizedIntegralBoundary n z ⊗ₜ[ℤ] x) := by
  exact (congrArg (fun f ↦ f (ULift.up (z ⊗ₜ[ℤ] x)))
    (tensorNormalizedDifferential_succ.{a, w, p} A S n)).trans
      (tensorNormalizedBoundary_tmul.{a, w, p} A S n z x)

/-- All off-shape components of the tensor chain complex vanish. -/
theorem tensorNormalizedChainComplex_d_eq_zero (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (i j : ℕ) (h : i ≠ j + 1) :
    (tensorNormalizedChainComplex.{a, w, p} A S).d i j = 0 :=
  tensorNormalizedDifferential_eq_zero.{a, w, p} A S i j h

/-- Maps from a degree of the tensor chain complex are determined on its generators. -/
theorem tensorNormalizedChainComplex_hom_ext (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) {M : ModuleCat.{max a w p} ℤ}
    {f g : (tensorNormalizedChainComplex.{a, w, p} A S).X n ⟶ M}
    (h : ∀ (s : S.nonDegenerate n) (x : A),
      f (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
        g (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x))) : f = g :=
  tensorNormalizedChainComplexX_hom_ext.{a, w, p} A S n h

/-- The comparison from integral tensor chains to normalized chains with lifted
coefficients, assembled from the constructed degreewise comparisons. -/
noncomputable def tensorNormalizedChainIso (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) :
    tensorNormalizedChainComplex.{a, w, p} A S ≅
      S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A)) :=
  HomologicalComplex.Hom.isoOfComponents (tensorNormalizedChainComplexXIso.{a, w, p} A S)
    (fun i j _ ↦ tensorNormalizedChainComplexXIso_hom_d.{a, w, p} A S i j)

/-- The chain comparison agrees with the degree comparison on every simplex class. -/
@[simp]
theorem tensorNormalizedChainIso_hom_f_apply (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) {n : ℕ} (s : S _⦋n⦌) (x : A) :
    (tensorNormalizedChainIso.{a, w, p} A S).hom.f n
        (ULift.up (S.normalizedIntegralSimplex s ⊗ₜ[ℤ] x)) =
      S.ιNormalizedChainComplex (R := ModuleCat.of ℤ (ULift.{max w p} A)) s (ULift.up x) :=
  tensorNormalizedChainComplexXIso_hom_simplex.{a, w, p} A S s x

/-- The inverse chain comparison recovers the tensor of a nondegenerate generator. -/
@[simp]
theorem tensorNormalizedChainIso_inv_f_ι (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) (s : S.nonDegenerate n) (x : A) :
    (tensorNormalizedChainIso.{a, w, p} A S).inv.f n
        (S.ιNormalizedChainComplex (R := ModuleCat.of ℤ (ULift.{max w p} A)) s.val (ULift.up x)) =
      ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x) :=
  tensorNormalizedChainComplexXIso_inv_ι.{a, w, p} A S n s x

/-- The coefficient of an arbitrary pure tensor under the chain comparison. -/
theorem tensorNormalizedChainIso_hom_f_tmul_coordinate (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) (z : S.nonDegenerate n →₀ ℤ) (x : A)
    (s : S.nonDegenerate n) :
    (S.normalizedChainComplexXIsoFinsupp (ModuleCat.of ℤ (ULift.{max w p} A)) n).hom
        ((tensorNormalizedChainIso.{a, w, p} A S).hom.f n (ULift.up (z ⊗ₜ[ℤ] x))) s =
      ULift.up (z s • x) := by
  have h := congrArg (fun f ↦ f (ULift.up (z ⊗ₜ[ℤ] x)) s)
    (tensorNormalizedChainComplexXIso_hom_coordinates.{a, w, p} A S n)
  exact h.trans (tensorNormalizedChainComplexXIsoFinsupp_hom_tmul_apply.{a, w, p} A S n z x s)

/-- The simplex formula uniquely characterizes the chain isomorphism. -/
theorem tensorNormalizedChainIso_eq_iff (A : Type a) [AddCommGroup A]
    (S : SSet.{w})
    (e : tensorNormalizedChainComplex.{a, w, p} A S ≅
      S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))) :
    e = tensorNormalizedChainIso.{a, w, p} A S ↔ ∀ (n : ℕ) (s : S.nonDegenerate n) (x : A),
      e.hom.f n (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
        S.ιNormalizedChainComplex (R := ModuleCat.of ℤ (ULift.{max w p} A)) s.val (ULift.up x) := by
  constructor
  · rintro rfl n s x
    exact tensorNormalizedChainComplexXIso_hom_single.{a, w, p} A S n s x
  · intro h
    apply Iso.ext
    ext n : 1
    apply tensorNormalizedChainComplex_hom_ext.{a, w, p} A S n
    intro s x
    exact (h n s x).trans (tensorNormalizedChainComplexXIso_hom_single.{a, w, p} A S n s x).symm

end SSet
