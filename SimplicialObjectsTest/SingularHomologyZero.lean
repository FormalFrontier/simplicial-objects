/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects.SingularHomologyZero
import SimplicialObjects.SingularHomologyZeroNaturality
import SimplicialObjects.SingularHomologyZeroCoefficientMaps
import Mathlib.Logic.Equiv.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order

/-!
# Integral vertex classes of the discrete two-point space

The two vertices of the singular simplicial set of discrete `Fin 2` give nonzero,
distinct classes in the original normalized integral tensor complex, with arbitrary
padding universe. The path-component isomorphism computes these classes, and local
coproduct retractions detect the lifted coefficient `1`. On this same space,
transposition and integer doubling give the space, coefficient, and mixed images
of these vertex classes.

The separation argument uses Mathlib's `PreconnectedSpace.constant`, and the
coefficient detectors use its categorical coproduct universal property. The
comparison reuses Mathlib's normalization and degree-zero homology constructions,
notably by Joël Riou, through the integral normalized tensor approach. No choice
of basis or presentation of the coproduct carrier is needed.
-/

universe p

open CategoryTheory Limits
open scoped Simplicial TensorProduct

namespace TopCat

private def transposition : C(Fin 2, Fin 2) where
  toFun := Equiv.swap (0 : Fin 2) 1
  continuous_toFun := continuous_of_discreteTopology

private def double : ℤ →+ ℤ := AddMonoidHom.id ℤ + AddMonoidHom.id ℤ

private theorem twoPointHomologyClasses :
    let X : TopCat.{0} := TopCat.of (Fin 2)
    let S := TopCat.toSSet.obj X
    let v0 : S _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm (0 : Fin 2)
    let v1 : S _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm (1 : Fin 2)
    let K := SSet.tensorNormalizedChainComplex.{0, 0, p} ℤ S
    let h0 := K.homologyπ₀
      (ULift.up (S.normalizedIntegralSimplex v0 ⊗ₜ[ℤ] (1 : ℤ)))
    let h1 := K.homologyπ₀
      (ULift.up (S.normalizedIntegralSimplex v1 ⊗ₜ[ℤ] (1 : ℤ)))
    ZerothHomotopy.mk (0 : Fin 2) ≠ ZerothHomotopy.mk (1 : Fin 2) ∧
      h0 ≠ 0 ∧ h1 ≠ 0 ∧ h0 ≠ h1 := by
  classical
  let X : TopCat.{0} := TopCat.of (Fin 2)
  let S := TopCat.toSSet.obj X
  let K := SSet.tensorNormalizedChainComplex.{0, 0, p} ℤ S
  let h (i : Fin 2) := K.homologyπ₀
    (ULift.up (S.normalizedIntegralSimplex
      (TopCat.toSSetObj₀Equiv.symm i) ⊗ₜ[ℤ] (1 : ℤ)))
  let R := ModuleCat.of ℤ (ULift.{p} ℤ)
  let e := tensorNormalizedHomologyZeroIsoPathComponents.{0, 0, p} ℤ X
  let c (i : Fin 2) := ZerothHomotopy.mk i
  let u : R := ULift.up (1 : ℤ)
  change c 0 ≠ c 1 ∧ h 0 ≠ 0 ∧ h 1 ≠ 0 ∧ h 0 ≠ h 1
  have hc : c 0 ≠ c 1 := by
    intro heq
    obtain ⟨γ⟩ := (Quotient.exact heq : Joined (0 : Fin 2) (1 : Fin 2))
    have endpoints : γ (0 : unitInterval) = γ 1 :=
      PreconnectedSpace.constant
        (inferInstance : PreconnectedSpace unitInterval) γ.continuous
    exact (by decide : (0 : Fin 2) ≠ 1)
      (γ.source.symm.trans (endpoints.trans γ.target))
  have hu : u ≠ 0 := by
    intro heq
    exact (by decide : (1 : ℤ) ≠ 0) (congrArg ULift.down heq)
  have image (i : Fin 2) :
      e.hom (h i) = Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R) (c i) u := by
    simpa only [Equiv.apply_symm_apply] using
      (tensorNormalizedHomologyZeroIsoPathComponents_hom_class.{0, 0, p}
        ℤ X (TopCat.toSSetObj₀Equiv.symm i) (1 : ℤ))
  let r (d : ZerothHomotopy (Fin 2)) :
      (∐ (fun _ : ZerothHomotopy (Fin 2) => R)) ⟶ R :=
    Sigma.desc (fun j => if j = d then 𝟙 R else 0)
  have detect (d j : ZerothHomotopy (Fin 2)) (x : R) :
      r d (Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R) j x) =
        (if j = d then 𝟙 R else 0) x :=
    ConcreteCategory.congr_hom
      (Sigma.ι_desc (fun j => if j = d then 𝟙 R else 0) j) x
  have detect_self (i : Fin 2) : r (c i) (e.hom (h i)) = u := by
    rw [image]
    simpa only [ite_eq_left rfl, ite_true, ModuleCat.id_apply] using detect (c i) (c i) u
  have hn (i : Fin 2) : h i ≠ 0 := by
    intro heq
    apply hu
    calc
      u = r (c i) (e.hom (h i)) := (detect_self i).symm
      _ = r (c i) (e.hom 0) := congrArg (fun z => r (c i) (e.hom z)) heq
      _ = 0 := by rw [e.hom.hom.map_zero, (r (c i)).hom.map_zero]
  refine ⟨hc, hn 0, hn 1, ?_⟩
  intro heq
  apply hu
  calc
    u = r (c 0) (e.hom (h 0)) := (detect_self 0).symm
    _ = r (c 0) (e.hom (h 1)) := congrArg (fun z => r (c 0) (e.hom z)) heq
    _ = 0 := by
      rw [image]
      calc
        r (c 0) (Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R) (c 1) u) =
            (0 : R ⟶ R) u := by
          simpa only [ite_eq_right (Ne.symm hc)] using detect (c 0) (c 1) u
        _ = 0 := rfl

private theorem vertexClassMapImages (i : Fin 2) :
    let X : TopCat.{0} := TopCat.of (Fin 2)
    let S := TopCat.toSSet.obj X
    let K := SSet.tensorNormalizedChainComplex.{0, 0, p} ℤ S
    let v : S _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm i
    let z := K.homologyπ₀
      (ULift.up (S.normalizedIntegralSimplex v ⊗ₜ[ℤ] (1 : ℤ)))
    let R := ModuleCat.of ℤ (ULift.{p} ℤ)
    let e := tensorNormalizedHomologyZeroIsoPathComponents.{0, 0, p} ℤ X
    let hs := HomologicalComplex.homologyMap
      (SSet.tensorNormalizedChainComplexMap.{0, 0, p} ℤ
        (TopCat.toSSet.map (TopCat.ofHom transposition))) 0
    let hc := HomologicalComplex.homologyMap
      (SSet.tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, p} double S) 0
    e.hom (hs z) = Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R)
        (ZerothHomotopy.mk (transposition i)) (ULift.up (1 : ℤ)) ∧
      e.hom (hc z) = Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R)
        (ZerothHomotopy.mk i) (ULift.up (2 : ℤ)) ∧
      e.hom (hc (hs z)) = Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R)
        (ZerothHomotopy.mk (transposition i)) (ULift.up (2 : ℤ)) := by
  let X : TopCat.{0} := TopCat.of (Fin 2)
  let S := TopCat.toSSet.obj X
  let K := SSet.tensorNormalizedChainComplex.{0, 0, p} ℤ S
  let z := K.homologyπ₀
    (ULift.up (S.normalizedIntegralSimplex
      (TopCat.toSSetObj₀Equiv.symm i) ⊗ₜ[ℤ] (1 : ℤ)))
  let R := ModuleCat.of ℤ (ULift.{p} ℤ)
  let e := tensorNormalizedHomologyZeroIsoPathComponents.{0, 0, p} ℤ X
  let hs := HomologicalComplex.homologyMap
    (SSet.tensorNormalizedChainComplexMap.{0, 0, p} ℤ
      (TopCat.toSSet.map (TopCat.ofHom transposition))) 0
  let hc := HomologicalComplex.homologyMap
    (SSet.tensorNormalizedChainComplexCoefficientMap.{0, 0, 0, p} double S) 0
  let k : R ⟶ R := ModuleCat.ofHom
    ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
      double.toIntLinearMap ∘ₗ (ULift.moduleEquiv (R := ℤ)).toLinearMap)
  let qc := Sigma.map' (f := fun _ : ZerothHomotopy (Fin 2) => R)
    (g := fun _ : ZerothHomotopy (Fin 2) => R) id (fun _ => k)
  let qm := Sigma.map' (f := fun _ : ZerothHomotopy (Fin 2) => R)
    (g := fun _ : ZerothHomotopy (Fin 2) => R)
    (ZerothHomotopy.map transposition) (fun _ => k)
  let qs := Sigma.map' (f := fun _ : ZerothHomotopy (Fin 2) => R)
    (g := fun _ : ZerothHomotopy (Fin 2) => R)
    (ZerothHomotopy.map transposition) (fun _ => 𝟙 R)
  have vertex : e.hom z =
      Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R)
        (ZerothHomotopy.mk i) (ULift.up (1 : ℤ)) := by
    simpa only [Equiv.apply_symm_apply] using
      (tensorNormalizedHomologyZeroIsoPathComponents_hom_class.{0, 0, p}
        ℤ X (TopCat.toSSetObj₀Equiv.symm i) (1 : ℤ))
  have space_square : hs ≫ e.hom = e.hom ≫ qs :=
    tensorNormalizedHomologyZeroIsoPathComponents_hom_naturality.{0, 0, p}
      ℤ X X transposition
  have coefficient_square : hc ≫ e.hom = e.hom ≫ qc :=
    tensorNormalizedHomologyZeroIsoPathComponents_hom_coefficient_naturality.{0, 0, 0, p}
      ℤ ℤ X double
  have mixed_square : (hs ≫ hc) ≫ e.hom = e.hom ≫ qm :=
    tensorNormalizedHomologyZeroIsoPathComponents_hom_mixed_naturality.{0, 0, 0, p}
      ℤ ℤ X X transposition double
  change e.hom (hs z) = _ ∧ e.hom (hc z) = _ ∧ e.hom (hc (hs z)) = _
  refine ⟨?_, ?_, ?_⟩
  · calc
      e.hom (hs z) = qs (e.hom z) := ConcreteCategory.congr_hom space_square z
      _ = qs (Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R)
          (ZerothHomotopy.mk i) (ULift.up (1 : ℤ))) := congrArg (fun x => qs x) vertex
      _ = Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R)
          (ZerothHomotopy.mk (transposition i)) (ULift.up (1 : ℤ)) := by
        change (Sigma.ι _ (ZerothHomotopy.mk i) ≫ qs) (ULift.up (1 : ℤ)) = _
        dsimp only [qs]
        rw [Sigma.ι_comp_map']
        rfl
  · calc
      e.hom (hc z) = qc (e.hom z) := ConcreteCategory.congr_hom coefficient_square z
      _ = qc (Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R)
          (ZerothHomotopy.mk i) (ULift.up (1 : ℤ))) := congrArg (fun x => qc x) vertex
      _ = Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R)
          (ZerothHomotopy.mk i) (ULift.up (2 : ℤ)) := by
        change (Sigma.ι _ (ZerothHomotopy.mk i) ≫ qc) (ULift.up (1 : ℤ)) = _
        dsimp only [qc]
        rw [Sigma.ι_comp_map']
        rfl
  · calc
      e.hom (hc (hs z)) = qm (e.hom z) := ConcreteCategory.congr_hom mixed_square z
      _ = qm (Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R)
          (ZerothHomotopy.mk i) (ULift.up (1 : ℤ))) := congrArg (fun x => qm x) vertex
      _ = Sigma.ι (fun _ : ZerothHomotopy (Fin 2) => R)
          (ZerothHomotopy.mk (transposition i)) (ULift.up (2 : ℤ)) := by
        change (Sigma.ι _ (ZerothHomotopy.mk i) ≫ qm) (ULift.up (1 : ℤ)) = _
        dsimp only [qm]
        rw [Sigma.ι_comp_map']
        rfl

end TopCat
