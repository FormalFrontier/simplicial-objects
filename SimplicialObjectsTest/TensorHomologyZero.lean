/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SimplicialObjects.TensorHomologyZeroConnected
import SimplicialObjects.TensorHomologyZeroEmpty

/-!
# Interval endpoint maps and the empty boundary

The integral endpoint family uses the normalized tensor-chain functor
on the two constant maps from the standard point to the standard interval.
The boundary of the identity edge identifies their homology maps. The interval
collapse is a common retraction, so these maps are nonzero on the lifted integral
coefficient one. The empty boundary is a separate zero case.

The endpoint family and its retraction argument reuse the integral interval
example of Formal Frontier Agents. The component comparison uses Mathlib's
normalization and degree-zero simplicial homology constructions, notably the
work of Joël Riou.
-/

@[expose] public section

open CategoryTheory Limits
open scoped Simplicial TensorProduct

namespace SimplicialObjectsTest

/-- The two endpoint maps from the coefficient module to the component
coproduct of the standard simplicial interval. -/
private noncomputable def intervalEndpointComponentMaps :
    Fin 2 →
      ((ModuleCat.of ℤ (ULift.{0} ℤ) : ModuleCat.{0} ℤ) ⟶
        ∐ (fun _ : SSet.π₀ (Δ[1] : SSet.{0}) =>
          (ModuleCat.of ℤ (ULift.{0} ℤ) : ModuleCat.{0} ℤ))) :=
  fun i =>
    (SSet.tensorNormalizedHomologyZeroIsoCoefficient.{0,0,0}
      ℤ (Δ[0] : SSet.{0}) SSet.stdSimplex.isTerminalObj₀).inv ≫
    ((SSet.tensorNormalizedChainComplexFunctor.{0,0,0} ℤ) ⋙
      HomologicalComplex.homologyFunctor
        (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 0).map
          (SSet.const (SSet.stdSimplex.obj₀Equiv.symm i) :
            (Δ[0] : SSet.{0}) ⟶ (Δ[1] : SSet.{0})) ≫
    (SSet.tensorNormalizedHomologyZeroIsoComponents.{0,0,0}
      ℤ (Δ[1] : SSet.{0})).hom

/-- The interval collapse gives the same retraction for either endpoint map. -/
private theorem intervalEndpointComponentMaps_retraction (i : Fin 2) :
    intervalEndpointComponentMaps i ≫
      ((SSet.tensorNormalizedHomologyZeroIsoComponents.{0,0,0}
          ℤ (Δ[1] : SSet.{0})).inv ≫
        ((SSet.tensorNormalizedChainComplexFunctor.{0,0,0} ℤ) ⋙
          HomologicalComplex.homologyFunctor
            (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 0).map
              (SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{0})) ≫
        (SSet.tensorNormalizedHomologyZeroIsoCoefficient.{0,0,0}
          ℤ (Δ[0] : SSet.{0}) SSet.stdSimplex.isTerminalObj₀).hom) =
      𝟙 (ModuleCat.of ℤ (ULift.{0} ℤ) : ModuleCat.{0} ℤ) := by
  let G := (SSet.tensorNormalizedChainComplexFunctor.{0,0,0} ℤ) ⋙
    HomologicalComplex.homologyFunctor
      (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 0
  let s : (Δ[0] : SSet.{0}) ⟶ (Δ[1] : SSet.{0}) :=
    SSet.const (SSet.stdSimplex.obj₀Equiv.symm i)
  let r := SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{0})
  -- Use the functor's object endpoints for both canonical comparisons.
  let Φ : G.obj (Δ[0] : SSet.{0}) ≅
      (ModuleCat.of ℤ (ULift.{0} ℤ) : ModuleCat.{0} ℤ) := by
    dsimp only [G, Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      SSet.tensorNormalizedChainComplexFunctor_obj]
    exact SSet.tensorNormalizedHomologyZeroIsoCoefficient.{0,0,0}
      ℤ (Δ[0] : SSet.{0}) SSet.stdSimplex.isTerminalObj₀
  let E : G.obj (Δ[1] : SSet.{0}) ≅
      ∐ (fun _ : SSet.π₀ (Δ[1] : SSet.{0}) =>
        (ModuleCat.of ℤ (ULift.{0} ℤ) : ModuleCat.{0} ℤ)) := by
    dsimp only [G, Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      SSet.tensorNormalizedChainComplexFunctor_obj]
    exact SSet.tensorNormalizedHomologyZeroIsoComponents.{0,0,0}
      ℤ (Δ[1] : SSet.{0})
  have hs : s ≫ r = 𝟙 (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  change (Φ.inv ≫ G.map s ≫ E.hom) ≫ (E.inv ≫ G.map r ≫ Φ.hom) = _
  calc
    _ = Φ.inv ≫ (G.map s ≫ G.map r) ≫ Φ.hom := by
      simp only [Category.assoc, E.hom_inv_id_assoc]
    _ = Φ.inv ≫ G.map (s ≫ r) ≫ Φ.hom := by
      exact congrArg
        (fun f : G.obj (Δ[0] : SSet.{0}) ⟶ G.obj (Δ[0] : SSet.{0}) =>
          Φ.inv ≫ f ≫ Φ.hom) (G.map_comp s r).symm
    _ = Φ.inv ≫ 𝟙 (G.obj (Δ[0] : SSet.{0})) ≫ Φ.hom := by
      rw [hs, G.map_id]
    _ = _ := by rw [Category.id_comp, Φ.inv_hom_id]

/-- Each endpoint sends the lifted integral coefficient one to a nonzero class. -/
private theorem intervalEndpointComponentMaps_one_ne_zero (i : Fin 2) :
    intervalEndpointComponentMaps i (ULift.up (1 : ℤ)) ≠ 0 := by
  let R :=
    (SSet.tensorNormalizedHomologyZeroIsoComponents.{0,0,0}
        ℤ (Δ[1] : SSet.{0})).inv ≫
      ((SSet.tensorNormalizedChainComplexFunctor.{0,0,0} ℤ) ⋙
        HomologicalComplex.homologyFunctor
          (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 0).map
            (SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{0})) ≫
      (SSet.tensorNormalizedHomologyZeroIsoCoefficient.{0,0,0}
        ℤ (Δ[0] : SSet.{0}) SSet.stdSimplex.isTerminalObj₀).hom
  have hsplit : intervalEndpointComponentMaps i ≫ R =
      𝟙 (ModuleCat.of ℤ (ULift.{0} ℤ) : ModuleCat.{0} ℤ) :=
    intervalEndpointComponentMaps_retraction i
  intro h
  have hone := congrArg
    (fun f : (ModuleCat.of ℤ (ULift.{0} ℤ) : ModuleCat.{0} ℤ) ⟶
        (ModuleCat.of ℤ (ULift.{0} ℤ) : ModuleCat.{0} ℤ) =>
      f (ULift.up (1 : ℤ))) hsplit
  have hRzero : R 0 = 0 := R.hom.map_zero
  rw [ModuleCat.comp_apply, ModuleCat.id_apply, h, hRzero] at hone
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (congrArg ULift.down hone)

-- The two nonzero endpoint maps agree by the boundary of the identity edge.
example : intervalEndpointComponentMaps 0 = intervalEndpointComponentMaps 1 := by
  let K₀ := SSet.tensorNormalizedChainComplex.{0, 0, 0} ℤ (Δ[0] : SSet.{0})
  let K₁ := SSet.tensorNormalizedChainComplex.{0, 0, 0} ℤ (Δ[1] : SSet.{0})
  let Φ := SSet.tensorNormalizedHomologyZeroIsoCoefficient.{0, 0, 0}
    ℤ (Δ[0] : SSet.{0}) SSet.stdSimplex.isTerminalObj₀
  let E := SSet.tensorNormalizedHomologyZeroIsoComponents.{0, 0, 0}
    ℤ (Δ[1] : SSet.{0})
  let ν (i : Fin 2) : (Δ[0] : SSet.{0}) ⟶ (Δ[1] : SSet.{0}) :=
    SSet.const (SSet.stdSimplex.obj₀Equiv.symm i)
  let v : (Δ[0] : SSet.{0}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm 0
  let c (w : (Δ[1] : SSet.{0}) _⦋0⦌) (x : ℤ) : K₁.homology 0 :=
    K₁.homologyπ₀
      (ULift.up ((Δ[1] : SSet.{0}).normalizedIntegralSimplex w ⊗ₜ[ℤ] x))
  have hclass (i : Fin 2) (x : ℤ) :
      HomologicalComplex.homologyMap
          (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} ℤ (ν i)) 0
        (Φ.inv (ULift.up x)) = c (SSet.stdSimplex.obj₀Equiv.symm i) x := by
    dsimp only [Φ]
    rw [SSet.tensorNormalizedHomologyZeroIsoCoefficient_inv_up.{0, 0, 0}
      ℤ (Δ[0] : SSet.{0}) SSet.stdSimplex.isTerminalObj₀ v x]
    let φ : K₀ ⟶ K₁ :=
      SSet.tensorNormalizedChainComplexMap.{0, 0, 0} ℤ (ν i)
    let z₀ : K₀.X 0 :=
      ULift.up ((Δ[0] : SSet.{0}).normalizedIntegralSimplex v ⊗ₜ[ℤ] x)
    let z₁ : K₁.X 0 :=
      ULift.up ((Δ[1] : SSet.{0}).normalizedIntegralSimplex
        (SSet.stdSimplex.obj₀Equiv.symm i) ⊗ₜ[ℤ] x)
    have hν : (ν i).app _ v = SSet.stdSimplex.obj₀Equiv.symm i := by
      have hv : v = SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) := by
        apply SSet.stdSimplex.obj₀Equiv.injective
        exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
      rw [hv]
      change SSet.yonedaEquiv (ν i) = _
      exact SSet.yonedaEquiv_const _
    have hz : φ.f 0 z₀ = z₁ := by
      exact
        (SSet.tensorNormalizedChainComplexMap_f_simplex.{0, 0, 0}
          ℤ (ν i) v x).trans
              (congrArg (fun w : (Δ[1] : SSet.{0}) _⦋0⦌ =>
                (ULift.up ((Δ[1] : SSet.{0}).normalizedIntegralSimplex w ⊗ₜ[ℤ] x)
                  : K₁.X 0)) hν)
    change HomologicalComplex.homologyMap φ 0 (K₀.homologyπ₀ z₀) =
      K₁.homologyπ₀ z₁
    have hnat : (K₀.homologyπ₀ ≫ HomologicalComplex.homologyMap φ 0) z₀ =
        (φ.f 0 ≫ K₁.homologyπ₀) z₀ :=
      ConcreteCategory.congr_hom (ChainComplex.homologyπ₀_naturality φ) z₀
    simp only [ModuleCat.comp_apply] at hnat
    rw [hz] at hnat
    exact hnat
  let e : (Δ[1] : SSet.{0}) _⦋1⦌ :=
    SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)
  have hδ₀ : (Δ[1] : SSet.{0}).δ (0 : Fin 2) e =
      SSet.stdSimplex.obj₀Equiv.symm 1 := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    rfl
  have hδ₁ : (Δ[1] : SSet.{0}).δ (1 : Fin 2) e =
      SSet.stdSimplex.obj₀Equiv.symm 0 := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    rfl
  have hends (x : ℤ) : c (SSet.stdSimplex.obj₀Equiv.symm 0) x =
      c (SSet.stdSimplex.obj₀Equiv.symm 1) x := by
    have h := SSet.tensorNormalizedHomologyZeroClass_endpoints.{0, 0, 0}
      ℤ (Δ[1] : SSet.{0}) e x
    rw [hδ₀, hδ₁] at h
    exact h.symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rcases z with ⟨x⟩
  change E.hom
      (HomologicalComplex.homologyMap
        (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} ℤ (ν 0)) 0
        (Φ.inv (ULift.up x))) =
    E.hom
      (HomologicalComplex.homologyMap
        (SSet.tensorNormalizedChainComplexMap.{0, 0, 0} ℤ (ν 1)) 0
        (Φ.inv (ULift.up x)))
  rw [hclass, hclass, hends]

example : IsZero ((SSet.tensorNormalizedChainComplex.{0, 0, 0}
    ℤ (∂Δ[0] : SSet.{0})).homology 0) :=
  SSet.tensorNormalizedHomologyZero_boundary_zero_isZero.{0, 0, 0} ℤ

end SimplicialObjectsTest
