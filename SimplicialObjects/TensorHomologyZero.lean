/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.PointHomology
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
public import SimplicialObjects.HomologyZero

/-!
# Components and degree-zero normalized tensor homology

For an abelian group `A` and a simplicial set `S`,
`SSet.tensorNormalizedHomologyZeroIsoComponents` identifies degree-zero homology
of the integral normalized tensor complex with the coproduct of lifted copies
of `A` indexed by `SSet.π₀ S`. These are simplicial components, defined by
edge zigzags.

The construction composes the integral tensor comparison with the homology
isomorphism of the normalization homotopy equivalence, in the direction from
normalized chains to all-simplex chains, and Mathlib's component isomorphism.
The tensor complex keeps its independently defined alternating differential,
with positive zeroth face and zero degenerate classes. The coefficient lift
`ULift.{max w p} A` is distinct from the outer lift on the tensor groups.

`ChainComplex.homologyπ₀`, from `SimplicialObjects.HomologyZero`, exposes the
standard projection from degree-zero chains to homology. The characteristic
formulas below compute the component isomorphism and its inverse on original
vertex tensors. The degree-one formula
is face zero minus face one; its image in homology proves endpoint equality.

## References and attribution

* Mathlib's Dold–Kan normalization and simplicial degree-zero homology work,
  notably by Joël Riou, supply the normalization homotopy equivalence and the
  component isomorphism.
* The integral normalized tensor formalization in
  `SimplicialObjects.TensorCoefficients` supplies the tensor comparison.
* J. Peter May, *A Concise Course in Algebraic Topology*, revised edition,
  §16.1, motivates the integral tensor presentation. No topological or
  singular-homology comparison is asserted here.
-/

@[expose] public section

universe a w p

open CategoryTheory Limits
open scoped Simplicial TensorProduct

namespace SSet

/-- Degree-zero homology of the integral normalized tensor complex as the
coproduct of the coefficient object over the simplicial components.

The coefficient, simplex and padding universes are independent, and the
integer-module structures are the canonical ones from `AddCommGroup A`.
The hom, inverse and both inverse identities are those of the composite of
the existing tensor comparison, Mathlib's normalization homotopy equivalence
and its component isomorphism. This uses Mathlib's Dold–Kan and degree-zero
homology constructions, notably the work of Joël Riou, together with the
integral normalized tensor formalization. -/
noncomputable def tensorNormalizedHomologyZeroIsoComponents
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) :
    (SSet.tensorNormalizedChainComplex.{a, w, p} A S).homology 0 ≅
      ∐ (fun _ : SSet.π₀ S => ModuleCat.of ℤ (ULift.{max w p} A)) :=
  HomologicalComplex.homologyMapIso (SSet.tensorNormalizedChainIso.{a, w, p} A S) 0 ≪≫
    (S.homotopyEquivNormalizedChainComplex
      (ModuleCat.of ℤ (ULift.{max w p} A))).symm.toHomologyIso 0 ≪≫
    S.homology₀Iso (ModuleCat.of ℤ (ULift.{max w p} A))

/-- In degree one the independently defined tensor differential has positive
zeroth face and negative first face on a nondegenerate generator. -/
theorem tensorNormalizedChainComplex_d_one_single
    (A : Type a) [AddCommGroup A] (S : SSet.{w})
    (s : S.nonDegenerate 1) (x : A) :
    (tensorNormalizedChainComplex.{a, w, p} A S).d 1 0
        (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)) =
      (ULift.up (S.normalizedIntegralSimplex (S.δ 0 s.val) ⊗ₜ[ℤ] x) :
        (tensorNormalizedChainComplex.{a, w, p} A S).X 0) -
      ULift.up (S.normalizedIntegralSimplex (S.δ 1 s.val) ⊗ₜ[ℤ] x) := by
  change tensorNormalizedDifferential.{a, w, p} A S 1 0 _ = _
  rw [tensorNormalizedDifferential_succ]
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using
    (tensorNormalizedBoundary_single.{a, w, p} A S 0 s x)

/-- The signed degree-one boundary formula also holds on the normalized class
of an arbitrary edge. A degenerate edge has zero class and equal faces. -/
theorem tensorNormalizedChainComplex_d_one_simplex
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) (s : S _⦋1⦌) (x : A) :
    (tensorNormalizedChainComplex.{a, w, p} A S).d 1 0
        (ULift.up (S.normalizedIntegralSimplex s ⊗ₜ[ℤ] x)) =
      (ULift.up (S.normalizedIntegralSimplex (S.δ 0 s) ⊗ₜ[ℤ] x) :
        (tensorNormalizedChainComplex.{a, w, p} A S).X 0) -
      ULift.up (S.normalizedIntegralSimplex (S.δ 1 s) ⊗ₜ[ℤ] x) := by
  classical
  by_cases hs : s ∈ S.nonDegenerate 1
  · rw [S.normalizedIntegralSimplex_of_mem_nonDegenerate s hs]
    exact tensorNormalizedChainComplex_d_one_single.{a, w, p} A S ⟨s, hs⟩ x
  · have hd := (S.mem_degenerate_iff_notMem_nonDegenerate s).mpr hs
    have hz := S.normalizedIntegralSimplex_of_mem_degenerate s hd
    rw [S.degenerate_eq_iUnion_range_σ, Set.mem_iUnion] at hd
    obtain ⟨i, hσ⟩ := hd
    obtain ⟨t, rfl⟩ := hσ
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    have h₀ : S.δ (0 : Fin 2) (S.σ (0 : Fin 1) t) = t :=
      S.δ_comp_σ_self_apply 0 t
    have h₁ : S.δ (1 : Fin 2) (S.σ (0 : Fin 1) t) = t :=
      S.δ_comp_σ_succ_apply 0 t
    have hz' :
        (ULift.up
          (S.normalizedIntegralSimplex (S.σ (0 : Fin 1) t) ⊗ₜ[ℤ] x) :
          (tensorNormalizedChainComplex.{a, w, p} A S).X 1) = 0 := by
      rw [hz, TensorProduct.zero_tmul]
      rfl
    rw [hz', h₀, h₁, sub_self]
    exact ((tensorNormalizedChainComplex.{a, w, p} A S).d 1 0).hom.map_zero

/-- The two endpoints of every edge give the same degree-zero class, because
their difference is the signed boundary of the original edge tensor. -/
theorem tensorNormalizedHomologyZeroClass_endpoints
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) (s : S _⦋1⦌) (x : A) :
    (tensorNormalizedChainComplex.{a, w, p} A S).homologyπ₀
        (ULift.up (S.normalizedIntegralSimplex (S.δ 0 s) ⊗ₜ[ℤ] x)) =
      (tensorNormalizedChainComplex.{a, w, p} A S).homologyπ₀
        (ULift.up (S.normalizedIntegralSimplex (S.δ 1 s) ⊗ₜ[ℤ] x)) := by
  let K := tensorNormalizedChainComplex.{a, w, p} A S
  let z : K.X 1 := ULift.up (S.normalizedIntegralSimplex s ⊗ₜ[ℤ] x)
  let v₀ : K.X 0 := ULift.up (S.normalizedIntegralSimplex (S.δ 0 s) ⊗ₜ[ℤ] x)
  let v₁ : K.X 0 := ULift.up (S.normalizedIntegralSimplex (S.δ 1 s) ⊗ₜ[ℤ] x)
  let π : K.X 0 →ₗ[ℤ] K.homology 0 := K.homologyπ₀.hom
  have hd : K.d 1 0 z = v₀ - v₁ :=
    tensorNormalizedChainComplex_d_one_simplex.{a, w, p} A S s x
  have hπ : π (K.d 1 0 z) = 0 := by
    have h := congrArg (fun f : K.X 1 ⟶ K.homology 0 => f z)
      (ChainComplex.d_homologyπ₀ K 1)
    change π (K.d 1 0 z) = 0 at h
    exact h
  change π v₀ = π v₁
  apply sub_eq_zero.mp
  calc
    π v₀ - π v₁ = π (v₀ - v₁) := (map_sub π v₀ v₁).symm
    _ = π (K.d 1 0 z) := congrArg π hd.symm
    _ = 0 := hπ

/-- The component isomorphism sends the class of every original vertex tensor
to the injection indexed by its simplicial component.

The calculation uses the tensor comparison on a generator, the normalization
inclusion in degree zero, and Mathlib's vertex formula for `homology₀Iso`. -/
theorem tensorNormalizedHomologyZeroIsoComponents_hom_class
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) (v : S _⦋0⦌) (x : A) :
    (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom
        ((tensorNormalizedChainComplex.{a, w, p} A S).homologyπ₀
          (ULift.up (S.normalizedIntegralSimplex v ⊗ₜ[ℤ] x))) =
      Sigma.ι (fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w p} A))
        (π₀.mk v) (ULift.up x) := by
  let R := ModuleCat.of ℤ (ULift.{max w p} A)
  let K := tensorNormalizedChainComplex.{a, w, p} A S
  let U := S.chainComplex R
  have hmap : K.homologyπ₀ ≫
      (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).hom =
      (tensorNormalizedChainIso.{a, w, p} A S).hom.f 0 ≫
        (S.fromNormalizedChainComplex R).f 0 ≫ U.homologyπ₀ ≫
          (S.homology₀Iso R).hom := by
    dsimp only [K, U, R]
    simp only [tensorNormalizedHomologyZeroIsoComponents, Iso.trans_hom,
      HomologicalComplex.homologyMapIso_hom, HomotopyEquiv.toHomologyIso,
      HomotopyEquiv.symm_hom, homotopyEquivNormalizedChainComplex_inv,
      ChainComplex.homologyπ₀_naturality_assoc]
  have hinc : S.ιNormalizedChainComplex (R := R) v ≫
      (S.fromNormalizedChainComplex R).f 0 = S.ιChainComplex v := by
    calc
      _ = S.ιChainComplex (R := R) v ≫ 𝟙 (U.X 0) :=
        S.ιNormalizedChainComplex_fromNormalizedChainComplex_f (R := R) v
      _ = _ := Category.comp_id _
  have hstock : S.ιChainComplex (R := R) v ≫ U.homologyπ₀ ≫
      (S.homology₀Iso R).hom = Sigma.ι (fun _ : π₀ S => R) (π₀.mk v) := by
    rw [ChainComplex.comp_homologyπ₀_assoc]
    exact S.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom R v
  have hvertex : S.ιNormalizedChainComplex (R := R) v ≫
      (S.fromNormalizedChainComplex R).f 0 ≫ U.homologyπ₀ ≫
        (S.homology₀Iso R).hom = Sigma.ι (fun _ : π₀ S => R) (π₀.mk v) := by
    calc
      _ = (S.ιNormalizedChainComplex (R := R) v ≫
          (S.fromNormalizedChainComplex R).f 0) ≫ U.homologyπ₀ ≫
            (S.homology₀Iso R).hom := (Category.assoc _ _ _).symm
      _ = S.ιChainComplex (R := R) v ≫ U.homologyπ₀ ≫
          (S.homology₀Iso R).hom :=
        congrArg (fun f : R ⟶ U.X 0 => f ≫ U.homologyπ₀ ≫ (S.homology₀Iso R).hom) hinc
      _ = _ := hstock
  let z : K.X 0 := ULift.up (S.normalizedIntegralSimplex v ⊗ₜ[ℤ] x)
  have hz : (tensorNormalizedChainIso.{a, w, p} A S).hom.f 0 z =
      S.ιNormalizedChainComplex (R := R) v (ULift.up x) :=
    tensorNormalizedChainIso_hom_f_apply.{a, w, p} A S v x
  calc
    _ = (S.homology₀Iso R).hom
        (U.homologyπ₀ ((S.fromNormalizedChainComplex R).f 0
          ((tensorNormalizedChainIso.{a, w, p} A S).hom.f 0 z))) :=
      ConcreteCategory.congr_hom hmap z
    _ = (S.homology₀Iso R).hom
        (U.homologyπ₀ ((S.fromNormalizedChainComplex R).f 0
          (S.ιNormalizedChainComplex (R := R) v (ULift.up x)))) :=
      congrArg (fun y : (S.normalizedChainComplex R).X 0 =>
        (S.homology₀Iso R).hom (U.homologyπ₀ ((S.fromNormalizedChainComplex R).f 0 y))) hz
    _ = _ := ConcreteCategory.congr_hom hvertex (ULift.up x)

/-- The inverse component isomorphism recovers the original vertex class on
each lifted coefficient in its component summand. -/
theorem tensorNormalizedHomologyZeroIsoComponents_inv_ι
    (A : Type a) [AddCommGroup A] (S : SSet.{w}) (v : S _⦋0⦌) (x : A) :
    (tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S).inv
        (Sigma.ι (fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w p} A))
          (π₀.mk v) (ULift.up x)) =
      (tensorNormalizedChainComplex.{a, w, p} A S).homologyπ₀
        (ULift.up (S.normalizedIntegralSimplex v ⊗ₜ[ℤ] x)) := by
  let E := tensorNormalizedHomologyZeroIsoComponents.{a, w, p} A S
  let K := tensorNormalizedChainComplex.{a, w, p} A S
  let z : K.homology 0 := K.homologyπ₀
    (ULift.up (S.normalizedIntegralSimplex v ⊗ₜ[ℤ] x) : K.X 0)
  have hz : E.hom z =
      Sigma.ι (fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w p} A))
        (π₀.mk v) (ULift.up x) :=
    tensorNormalizedHomologyZeroIsoComponents_hom_class.{a, w, p} A S v x
  calc
    E.inv (Sigma.ι (fun _ : π₀ S => ModuleCat.of ℤ (ULift.{max w p} A))
        (π₀.mk v) (ULift.up x)) = E.inv (E.hom z) :=
      congrArg (fun y => E.inv y) hz.symm
    _ = z := ConcreteCategory.congr_hom E.hom_inv_id z

end SSet
