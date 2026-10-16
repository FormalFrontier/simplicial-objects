/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex

/-!
# Normalized maps for arbitrary morphisms of split simplicial objects

The normalized complex, projection and section are mathlib's existing
`SimplicialObject.Splitting.nondegComplex`, `toNondegComplex` and
`fromNondegComplex`. The construction here allows every morphism between the
underlying simplicial objects, without requiring it to preserve the chosen
nondegenerate summands.

A supplied splitting contains the coproduct data; the construction needs only
preadditivity. The projection equation characterizes descent, and its degreewise
quotient property is expressed by vanishing on elementary degeneracies.

## References

Mathlib's Dold–Kan projector and splitting constructions, notably
`Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject`, supply the normalized
objects and strict retract identities. The map generalizes the simplicial-set
normalized-map construction to coefficient-valued simplicial morphisms. May,
*A Concise Course in Algebraic Topology*, revised edition, §16.1 motivates the
degeneracy-quotient characterization.
-/

@[expose] public section

universe v v' u u' w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.Splitting

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {X Y Z : SimplicialObject C} (s : Splitting X) (t : Splitting Y) (r : Splitting Z)

/-- The normalized chain map induced by any underlying simplicial morphism.
The section, alternating-face map, and projection are the three stock chain maps. -/
noncomputable def nondegComplexMap (f : X ⟶ Y) : s.nondegComplex ⟶ t.nondegComplex :=
  s.fromNondegComplex ≫ (alternatingFaceMapComplex C).map f ≫ t.toNondegComplex

/-- Degreewise formula for the constructed normalized map. -/
@[reassoc]
theorem nondegComplexMap_f (f : X ⟶ Y) (n : ℕ) :
    (s.nondegComplexMap t f).f n = s.fromNondegComplex.f n ≫
      f.app (op ⦋n⦌) ≫ t.toNondegComplex.f n := rfl

/-- The quotient projection is natural for every underlying simplicial morphism. -/
@[reassoc]
theorem toNondegComplex_nondegComplexMap (f : X ⟶ Y) :
    s.toNondegComplex ≫ s.nondegComplexMap t f =
      (alternatingFaceMapComplex C).map f ≫ t.toNondegComplex := by
  have h : (alternatingFaceMapComplex C).map f ≫ DoldKan.PInfty =
      DoldKan.PInfty ≫ (alternatingFaceMapComplex C).map f :=
    (DoldKan.natTransPInfty C).naturality f
  unfold nondegComplexMap
  rw [← Category.assoc, s.toNondegComplex_fromNondegComplex, ← Category.assoc,
    ← h, Category.assoc, t.PInfty_toNondegComplex]

/-- The projection equation characterizes the constructed map uniquely. -/
theorem nondegComplexMap_eq_iff (f : X ⟶ Y) (g : s.nondegComplex ⟶ t.nondegComplex) :
    g = s.nondegComplexMap t f ↔
      s.toNondegComplex ≫ g = (alternatingFaceMapComplex C).map f ≫ t.toNondegComplex := by
  constructor
  · rintro rfl
    exact s.toNondegComplex_nondegComplexMap t f
  · intro h
    apply (cancel_epi s.toNondegComplex).1
    exact h.trans (s.toNondegComplex_nondegComplexMap t f).symm

/-- Normalization preserves the identity underlying simplicial morphism. -/
theorem nondegComplexMap_id : s.nondegComplexMap s (𝟙 X) = 𝟙 _ := by
  symm
  apply (s.nondegComplexMap_eq_iff s (𝟙 X) (𝟙 _)).2
  simp only [Functor.map_id, Category.comp_id, Category.id_comp]

/-- Normalization preserves composition, without compatibility of the splittings. -/
theorem nondegComplexMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    s.nondegComplexMap r (f ≫ g) = s.nondegComplexMap t f ≫ t.nondegComplexMap r g := by
  symm
  apply (s.nondegComplexMap_eq_iff r (f ≫ g)
    (s.nondegComplexMap t f ≫ t.nondegComplexMap r g)).2
  rw [← Category.assoc, s.toNondegComplex_nondegComplexMap t f, Category.assoc,
    t.toNondegComplex_nondegComplexMap r g, Functor.map_comp, Category.assoc]

/-- In every degree, the stock projection is the quotient by elementary degeneracies.
In degree zero the degeneracy condition is vacuous. -/
theorem degeneraciesVanish_iff_existsUnique (n : ℕ) {T : C} (a : X _⦋n⦌ ⟶ T) :
    DoldKan.DegeneraciesVanish a ↔
      ∃! b : s.N n ⟶ T, s.toNondegComplex.f n ≫ b = a := by
  change DoldKan.DegeneraciesVanish a ↔
    ∃! b : s.nondegComplex.X n ⟶ T, s.toNondegComplex.f n ≫ b = a
  constructor
  · intro ha
    have hQ := (DoldKan.degeneraciesVanish_iff_QInfty_f_comp a).mp ha
    have hP : (DoldKan.PInfty (X := X)).f n ≫ a = a := by
      have h := DoldKan.PInfty_f_add_QInfty_f (X := X) n =≫ a
      simpa only [Preadditive.add_comp, hQ, add_zero, Category.id_comp] using h
    have hqj : s.toNondegComplex.f n ≫ s.fromNondegComplex.f n =
        (DoldKan.PInfty (X := X)).f n := by
      simpa only [HomologicalComplex.comp_f] using
        HomologicalComplex.congr_hom s.toNondegComplex_fromNondegComplex n
    have hjq : s.fromNondegComplex.f n ≫ s.toNondegComplex.f n =
        𝟙 (s.nondegComplex.X n) := by
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
        HomologicalComplex.congr_hom s.fromNondegComplex_toNondegComplex n
    refine ⟨s.fromNondegComplex.f n ≫ a, ?_, ?_⟩
    · change s.toNondegComplex.f n ≫ (s.fromNondegComplex.f n ≫ a) = a
      rw [← Category.assoc, hqj]
      exact hP
    · intro b hb
      calc
        b = (s.fromNondegComplex.f n ≫ s.toNondegComplex.f n) ≫ b := by
          rw [hjq, Category.id_comp]
        _ = s.fromNondegComplex.f n ≫ a := by rw [Category.assoc, hb]
  · rintro ⟨b, hb, _⟩
    have hq : DoldKan.DegeneraciesVanish (s.toNondegComplex.f n) := by
      rw [s.toNondegComplex_f]
      exact (DoldKan.degeneraciesVanishPInfty_f X n).comp _
    rw [← hb]
    exact hq.comp b

/-- The universal factor of a map vanishing on degeneracies is given by the stock section. -/
@[reassoc]
theorem toNondegComplex_f_factor (n : ℕ) {T : C} (a : X _⦋n⦌ ⟶ T)
    (ha : DoldKan.DegeneraciesVanish a) :
    s.toNondegComplex.f n ≫ s.fromNondegComplex.f n ≫ a = a := by
  have hQ := (DoldKan.degeneraciesVanish_iff_QInfty_f_comp a).mp ha
  have hP := DoldKan.PInfty_f_add_QInfty_f (X := X) n =≫ a
  have hqj : s.toNondegComplex.f n ≫ s.fromNondegComplex.f n =
      (DoldKan.PInfty (X := X)).f n := by
    simpa only [HomologicalComplex.comp_f] using
      HomologicalComplex.congr_hom s.toNondegComplex_fromNondegComplex n
  rw [← Category.assoc, hqj]
  simpa only [Preadditive.add_comp, hQ, add_zero, Category.id_comp] using hP

end CategoryTheory.SimplicialObject.Splitting

namespace CategoryTheory.SimplicialObject.Split

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {S₁ S₂ : Split C} (Φ : S₁ ⟶ S₂)

/-- For a morphism compatible with the splittings, the normalized map agrees with
mathlib's functor on split simplicial objects. -/
theorem nondegComplexMap_eq_nondegComplexFunctor_map :
    S₁.s.nondegComplexMap S₂.s Φ.F = nondegComplexFunctor.map Φ := by
  symm
  apply (S₁.s.nondegComplexMap_eq_iff S₂.s Φ.F _).2
  ext n
  change S₁.s.toNondegComplex.f n ≫ Φ.f n =
    Φ.F.app (op ⦋n⦌) ≫ S₂.s.toNondegComplex.f n
  rw [S₁.s.toNondegComplex_f, S₂.s.toNondegComplex_f]
  change (DoldKan.PInfty.f n ≫
      S₁.s.πSummand (Splitting.IndexSet.id (op ⦋n⦌))) ≫ Φ.f n =
    Φ.F.app (op ⦋n⦌) ≫ DoldKan.PInfty.f n ≫
      S₂.s.πSummand (Splitting.IndexSet.id (op ⦋n⦌))
  rw [S₁.s.PInfty_comp_πSummand_id, S₂.s.PInfty_comp_πSummand_id]
  apply S₁.s.hom_ext'
  intro A
  erw [cofan_inj_naturality_symm_assoc Φ A]
  by_cases h : A.EqId
  · dsimp at h
    subst h
    change (S₁.s.cofan (op ⦋n⦌)).inj (Splitting.IndexSet.id (op ⦋n⦌)) ≫
        S₁.s.πSummand (Splitting.IndexSet.id (op ⦋n⦌)) ≫ Φ.f n =
      Φ.f n ≫ (S₂.s.cofan (op ⦋n⦌)).inj (Splitting.IndexSet.id (op ⦋n⦌)) ≫
        S₂.s.πSummand (Splitting.IndexSet.id (op ⦋n⦌))
    erw [S₁.s.cofan_inj_πSummand_eq_id_assoc, S₂.s.cofan_inj_πSummand_eq_id]
    erw [Category.comp_id]
  · erw [S₁.s.cofan_inj_πSummand_eq_zero_assoc _ _ (Ne.symm h),
      S₂.s.cofan_inj_πSummand_eq_zero _ _ (Ne.symm h), zero_comp, comp_zero]

end

end CategoryTheory.SimplicialObject.Split

namespace SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : SSet.{w}} (f : X ⟶ Y) (R : C)

/-- The generic normalized map agrees with mathlib's existing map for simplicial sets.
The map `f` need not preserve nondegenerate simplices. -/
theorem nondegComplexMap_eq_normalizedChainComplexMap :
    (X.splitting.map (sigmaConst.obj R)).nondegComplexMap
        (Y.splitting.map (sigmaConst.obj R)) (Functor.whiskerRight f (sigmaConst.obj R)) =
      normalizedChainComplexMap f R := by
  symm
  apply ((X.splitting.map (sigmaConst.obj R)).nondegComplexMap_eq_iff
    (Y.splitting.map (sigmaConst.obj R))
    (Functor.whiskerRight f (sigmaConst.obj R)) _).2
  exact toNormalizedChainComplex_normalizedChainComplexMap f R

section CoefficientComparison

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasCoproducts.{w} D]
  (L : C ⥤ D) [L.Additive]
  [∀ (T : Type w), PreservesColimitsOfShape (Discrete T) L]

@[reassoc]
private lemma map_PInfty_chainComplexFunctorObjCompMapIso_hom_app (S : SSet.{w}) :
    (L.mapHomologicalComplex (.down ℕ)).map
        (DoldKan.PInfty (X := S ⋙ sigmaConst.obj R)) ≫
        (chainComplexFunctorObjCompMapIso L R).hom.app S =
      (chainComplexFunctorObjCompMapIso L R).hom.app S ≫ DoldKan.PInfty := by
  ext n
  have h := DoldKan.PInfty_f_naturality n
    (X := ((SimplicialObject.whiskering C D).obj L).obj (S ⋙ sigmaConst.obj R))
    (Functor.whiskerLeft S (sigmaConstObjCompIso L R).hom)
  rw [DoldKan.map_PInfty_f L (S ⋙ sigmaConst.obj R) n] at h
  simpa [chainComplexFunctorObjCompMapIso] using h.symm

/-- Normalized chains commute with an additive functor preserving the indexed coproducts.
The components use the normalization section and projection and the all-simplex
coefficient comparison. -/
noncomputable def normalizedChainComplexFunctorObjCompMapIso :
    normalizedChainComplexFunctorObj R ⋙ L.mapHomologicalComplex (.down ℕ) ≅
      normalizedChainComplexFunctorObj (L.obj R) :=
  NatIso.ofComponents (fun S ↦
    { hom := (L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
        (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
          S.toNormalizedChainComplex (L.obj R)
      inv := S.fromNormalizedChainComplex (L.obj R) ≫
        (chainComplexFunctorObjCompMapIso L R).inv.app S ≫
          (L.mapHomologicalComplex (.down ℕ)).map (S.toNormalizedChainComplex R)
      hom_inv_id := by
        change ((L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
            (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
              S.toNormalizedChainComplex (L.obj R)) ≫
            (S.fromNormalizedChainComplex (L.obj R) ≫
              (chainComplexFunctorObjCompMapIso L R).inv.app S ≫
                (L.mapHomologicalComplex (.down ℕ)).map (S.toNormalizedChainComplex R)) =
          𝟙 ((L.mapHomologicalComplex (.down ℕ)).obj (S.normalizedChainComplex R))
        simp only [Category.assoc, toNormalizedChainComplex_fromNormalizedChainComplex_assoc]
        rw [← map_PInfty_chainComplexFunctorObjCompMapIso_hom_app_assoc R L S]
        simp only [Iso.hom_inv_id_app_assoc]
        rw [← S.toNormalizedChainComplex_fromNormalizedChainComplex R]
        simp [← Functor.map_comp]
      inv_hom_id := by
        change (S.fromNormalizedChainComplex (L.obj R) ≫
            (chainComplexFunctorObjCompMapIso L R).inv.app S ≫
              (L.mapHomologicalComplex (.down ℕ)).map (S.toNormalizedChainComplex R)) ≫
            ((L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
              (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
                S.toNormalizedChainComplex (L.obj R)) =
          𝟙 (S.normalizedChainComplex (L.obj R))
        simp only [Category.assoc]
        rw [← (L.mapHomologicalComplex (.down ℕ)).map_comp_assoc
          (S.toNormalizedChainComplex R) (S.fromNormalizedChainComplex R),
          toNormalizedChainComplex_fromNormalizedChainComplex,
          map_PInfty_chainComplexFunctorObjCompMapIso_hom_app_assoc R L S]
        simp })
    (by
      intro S T g
      change (L.mapHomologicalComplex (.down ℕ)).map (normalizedChainComplexMap g R) ≫
          ((L.mapHomologicalComplex (.down ℕ)).map (T.fromNormalizedChainComplex R) ≫
            (chainComplexFunctorObjCompMapIso L R).hom.app T ≫
              T.toNormalizedChainComplex (L.obj R)) =
        ((L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
            (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
              S.toNormalizedChainComplex (L.obj R)) ≫
          normalizedChainComplexMap g (L.obj R)
      simp only [normalizedChainComplexMap, Functor.map_comp, Category.assoc]
      rw [← (L.mapHomologicalComplex (.down ℕ)).map_comp_assoc
        (T.toNormalizedChainComplex R) (T.fromNormalizedChainComplex R),
        toNormalizedChainComplex_fromNormalizedChainComplex,
        map_PInfty_chainComplexFunctorObjCompMapIso_hom_app_assoc R L T,
        PInfty_toNormalizedChainComplex,
        toNormalizedChainComplex_fromNormalizedChainComplex_assoc,
        ← chainComplexMap_PInfty_assoc, PInfty_toNormalizedChainComplex]
      simpa only [Functor.comp_map, Category.assoc] using
        (L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫=
          ((chainComplexFunctorObjCompMapIso L R).hom.naturality g =≫
            T.toNormalizedChainComplex (L.obj R)))

/-- The comparison respects the normalization projection. -/
@[reassoc]
theorem toNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app
    (S : SSet.{w}) :
    (L.mapHomologicalComplex (.down ℕ)).map (S.toNormalizedChainComplex R) ≫
        (normalizedChainComplexFunctorObjCompMapIso R L).hom.app S =
      (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
        S.toNormalizedChainComplex (L.obj R) := by
  change (L.mapHomologicalComplex (.down ℕ)).map (S.toNormalizedChainComplex R) ≫
      ((L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
        (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
          S.toNormalizedChainComplex (L.obj R)) = _
  rw [← Functor.map_comp_assoc, toNormalizedChainComplex_fromNormalizedChainComplex,
    map_PInfty_chainComplexFunctorObjCompMapIso_hom_app_assoc R L S,
    PInfty_toNormalizedChainComplex]

/-- The comparison respects the normalization section. -/
@[reassoc]
theorem normalizedChainComplexFunctorObjCompMapIso_hom_app_fromNormalizedChainComplex
    (S : SSet.{w}) :
    (normalizedChainComplexFunctorObjCompMapIso R L).hom.app S ≫
        S.fromNormalizedChainComplex (L.obj R) =
      (L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
        (chainComplexFunctorObjCompMapIso L R).hom.app S := by
  change ((L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
      (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
        S.toNormalizedChainComplex (L.obj R)) ≫
      S.fromNormalizedChainComplex (L.obj R) = _
  simp only [Category.assoc, toNormalizedChainComplex_fromNormalizedChainComplex]
  rw [← map_PInfty_chainComplexFunctorObjCompMapIso_hom_app R L S,
    ← Functor.map_comp_assoc, ← S.toNormalizedChainComplex_fromNormalizedChainComplex R]
  simp only [← Category.assoc, fromNormalizedChainComplex_toNormalizedChainComplex,
    Category.id_comp]

/-- On every normalized simplex generator, including a degenerate simplex's zero class,
the comparison is the canonical coefficient coproduct map. -/
@[reassoc]
theorem map_ιNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app_f
    (S : SSet.{w}) {n : ℕ} (x : S _⦋n⦌) :
    L.map (S.ιNormalizedChainComplex (R := R) x) ≫
        ((normalizedChainComplexFunctorObjCompMapIso R L).hom.app S).f n =
      S.ιNormalizedChainComplex x := by
  let b : (L.mapHomologicalComplex (.down ℕ)).obj (S.normalizedChainComplex R) ⟶
      S.normalizedChainComplex (L.obj R) :=
    (normalizedChainComplexFunctorObjCompMapIso R L).hom.app S
  change L.map (S.ιNormalizedChainComplex (R := R) x) ≫ b.f n = _
  calc
    L.map (S.ιNormalizedChainComplex (R := R) x) ≫ b.f n =
        L.map (S.ιChainComplex (R := R) x) ≫
          L.map ((S.toNormalizedChainComplex R).f n) ≫ b.f n := by
      rw [← L.map_comp_assoc, ιChainComplex_toNormalizedChainComplex_f]
    _ = L.map (S.ιChainComplex (R := R) x) ≫
        ((chainComplexFunctorObjCompMapIso L R).hom.app S).f n ≫
          (S.toNormalizedChainComplex (L.obj R)).f n :=
      L.map (S.ιChainComplex (R := R) x) ≫=
        HomologicalComplex.congr_hom
          (toNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app R L S) n
    _ = S.ιNormalizedChainComplex x := by
      rw [map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f_assoc,
        ιChainComplex_toNormalizedChainComplex_f]

end CoefficientComparison

end SSet
