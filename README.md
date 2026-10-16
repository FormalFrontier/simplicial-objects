# Simplicial objects

Authors: Formal Frontier Agents.

This Lean library constructs the augmented left décalage and its canonical
extra degeneracy for **every simplicial object `X : SimplicialObject C`** in
an arbitrary `[Category* C]`. No terminal or zero object, additivity or limit
assumptions are required. Its public import is `SimplicialObjects`, which
exports `SimplicialObjects.LeftDecalage`,
`SimplicialObjects.FiniteFiberTransfer` and `SimplicialObjects.Normalization`,
but no private test declarations.
The transfer construction uses coefficient objects in a preadditive category
with coproducts, and is compatible with identity, reverse-order composition,
pullback base change and coefficient maps.

## Headline results

- **Augmented left décalage.** [`augmented X`](SimplicialObjects/LeftDecalage.lean) has ordinary degree
  `P(X)ₙ = Xₙ₊₁` and augmentation target `X₀`. Its augmentation takes the
  new initial vertex: at degree zero `ε₀ = X.δ 1`, **not** `X.δ 0`.
- **Canonical extra degeneracy.** [`extraDegeneracy X`](SimplicialObjects/LeftDecalage.lean) builds mathlib's
  `SimplicialObject.Augmented.ExtraDegeneracy (augmented X)` from the
  original zeroth degeneracies. All five defining equations, including the
  exceptional degree-zero face, hold. Mathlib then supplies `.section_`,
  `.splitEpi`, `.homotopy` and postcomposition `.map F`; these are not new
  implementations in this repository.
- **Functoriality and naturality.** [`functor C`](SimplicialObjects/LeftDecalage.lean) makes the augmented
  construction functorial; [`projection X`](SimplicialObjects/LeftDecalage.lean)
  is the natural ordinary simplicial `X.δ 0` projection, distinct in general
  from the augmentation. The section, higher extra-degeneracy components and
  projection have explicit naturality equations.

- **Finite-fiber transfers.** [`FiniteFiberTransfer`](SimplicialObjects/FiniteFiberTransfer.lean)
  constructs coproduct, diagram and all-simplex chain transfers with arbitrary
  coefficient objects in a preadditive category with coproducts. For an
  equifibered simplicial map only vertex fibers must be finite; no fixed
  sheet number is required. The coproduct generator maps to the sum over its
  fiber, compatibly with postcomposition, pullback base change and coefficient
  maps. Identity maps have identity coproduct transfer, and transfers compose in
  reverse order on coproducts, equifibered diagrams, simplicial chains and homology.
  Composite fibers are finite by the constituent finite-fiber hypotheses alone.
  Transfer followed by pushforward counts the fiber. If every vertex
  fiber has cardinality `d`, this composite is `d` times the identity on chains
  and on natural-number-graded homology, when the coefficient category has
  homology. Normalized coefficient compatibility is supplied by the
  normalization module below; no topological comparison is asserted.
  The private client `SimplicialObjectsTest.FiniteFiberTransfer` computes the
  two-sheet integral generator, its coordinates and its pushforward, and
  computes the six-sheet two-step transfer through three sheets, and checks empty
  sheets, zero coefficients and independent coefficient/index universes.
- **Change of coefficient category.**
  [`SSet.chainComplexTransfer_mapHomologicalComplex`](SimplicialObjects/FiniteFiberTransfer.lean)
  proves compatibility of the all-simplex chain transfer with Mathlib's
  coefficient-comparison isomorphism for an additive functor `C ⥤ D` preserving
  coproducts indexed by types in the simplex universe. The source and target
  categories are preadditive and have those coproducts; only vertex fibers of
  the equifibered simplicial map need be finite.
  No preservation of homology or exactness is assumed. The private two-sheet
  client tensors integral coefficients with `ZMod 4`: both coordinates are
  `1 ⊗ 1`, nonzero by the left unitor, and pushforward gives two modulo four.
  These generator computations are independent of the compatibility theorem.

- **Normalized descent.** [`Normalization`](SimplicialObjects/Normalization.lean)
  constructs maps between mathlib's normalized complexes for any morphism
  `f : X ⟶ Y` of simplicial objects in a preadditive category, given splittings
  `s` and `t`. The formula is `s.fromNondegComplex ≫ K(f) ≫ t.toNondegComplex`,
  where `K` is the alternating-face-map complex; `f` need not preserve the chosen
  nondegenerate summands. Its API comprises the projection equation,
  characterization of descent, identity and composition, the degreewise quotient
  property for elementary degeneracies, the explicit factor `s.fromNondegComplex.f n ≫ a`,
  and agreement with mathlib's simplicial-set normalized map. It also agrees with
  mathlib's `Split.nondegComplexFunctor` on morphisms compatible with the splittings,
  without an additional finite-coproduct assumption. The private integral
  `Δ[1]` model has normalized groups `ℤ ⊞ ℤ` and `ℤ` in degrees zero and one,
  boundary `a ↦ (-a,a)`, and collapse to `Δ[0]` zero in degree one but nonzero in
  degree zero.
- **Normalized change of coefficient category.**
  [`SSet.normalizedChainComplexFunctorObjCompMapIso`](SimplicialObjects/Normalization.lean)
  identifies normalized chains with coefficients `R`, followed by
  `L.mapHomologicalComplex (.down ℕ)`, with normalized chains with coefficient
  object `L.obj R`, naturally on `SSet.{w}`.
  Here `C : Type u` and `D : Type u'` have `Category.{v}` and `Category.{v'}`
  structures, are preadditive and have `HasCoproducts.{w}`; `R : C` and `L : C ⥤ D`
  is additive with exactly
  `[∀ T : Type w, PreservesColimitsOfShape (Discrete T) L]`.
  All five universes `u`, `v`, `u'`, `v'`, `w` are independent; no exactness or
  Abelian assumption is needed. The comparison respects the normalization
  projection `q` and section `j`, and has the canonical coefficient formula on
  every simplex generator, including degenerate zero classes. Its naturality
  includes collapse maps, without preservation of nondegenerate simplices.
  The private `Δ[1]` client tensors the integral normalized interval with `ZMod 4`;
  its target coefficient object is `ℤ ⊗[ℤ] ZMod 4`. Independent coordinates of
  both degree-one edges are `1 ⊗ 1`, sent to `1 mod 4` by the left unitor, so both
  edges are nonzero; collapse annihilates both. The generator law sends the
  source edge to the target edge.
- **Coherence of normalized coefficient comparison.**
  [`Normalization`](SimplicialObjects/Normalization.lean) proves three further
  equalities with the same coefficient-category and coproduct hypotheses:
  `normalizedChainComplexFunctorObjCompMapIso_nondegComplexMap` commutes with
  an arbitrary coefficient-valued simplicial morphism, transported through the
  coproduct comparison, without a `Split.Hom` compatibility assumption;
  `normalizedChainComplexFunctorObjCompMapIso_finiteFiberTransfer` commutes with
  normalized transfer for an equifibered simplicial map with finite vertex fibers;
  and `normalizedChainComplexFunctorObjCompMapIso_naturality` commutes with any
  natural transformation `θ : L ⟶ M`, where both functors are additive and preserve
  exactly the same indexed coproducts. The transformation acts on the normalized
  source and coefficientwise on the target. These laws are consequences of
  Mathlib's splitting retract and all-simplex comparison, not extra exactness or
  homology-preservation results.
  The private tensor client applies the first law to `2 • id + const(v₀)` on the
  coefficient-valued interval, which does not preserve the raw nondegenerate
  summand. The second compares the two-sheet interval transfer, with both sheet
  coordinates one modulo four and pushforward two modulo four, nonzero. The third
  uses the tensor transformation induced by multiplication by two on `ZMod 4`:
  it is not the identity, and the changed original edge has coordinate two modulo
  four, nonzero. No full arbitrary-Abelian tensor/Finsupp dictionary is asserted.

See the [left décalage guide](docs/LeftDecalage.md) for indexing, exact
equations, construction and example clients. The homotopy is
**combinatorial**; no geometric realization, general-relative contraction,
exactness, spectra, K-theory theorem or source-coverage claim follows here.

## Use

Add the library to your `lakefile.toml`:

```toml
[[require]]
name = "simplicial-objects"
git = "https://github.com/FormalFrontier/simplicial-objects.git"
rev = "main"
```

Lake records the resolved release commit in `lake-manifest.json` until you
update the dependency. Replace `main` with a particular release commit to pin
it explicitly.

```lean
import SimplicialObjects.LeftDecalage

open CategoryTheory Opposite SimplicialObjects.LeftDecalage
open scoped Simplicial

example {C : Type*} [Category* C] (X : SimplicialObject C) :
    (augmented X).left _⦋0⦌ = X _⦋1⦌ := path_obj X 0

example {C : Type*} [Category* C] (X : SimplicialObject C) :
    (augmented X).hom.app (op ⦋0⦌) = X.δ (1 : Fin 2) := augmentation_zero X

example {C : Type*} [Category* C] (X : SimplicialObject C) :
    (projection X).app (op ⦋0⦌) = X.δ (0 : Fin 2) := projection_zero X
```

The ordinary-import private client `SimplicialObjectsTest.LeftDecalage`
checks these generic statements, section, homotopy and transport,
functoriality and naturality, a nonterminal `Bool` example and unequal first
faces on the standard simplicial edge. It is a maintained verification target,
not part of the public root.

## Reproduce and verification

The pinned Lean toolchain is `leanprover/lean4:v4.34.0-rc2`; the only direct
dependency is GitHub mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`.
In a checkout, use the committed `lake-manifest.json` and fetch matching
precompiled mathlib artifacts **before** building:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build SimplicialObjects SimplicialObjectsTest
```

**Verification targets:** The two maintained roots include ordinary-import
private clients for the decalage, transfer and normalization APIs.
[`formalization.yaml`](formalization.yaml) is a public API index, not a
source-passage coverage map. See [`CONTRIBUTORS.md`](CONTRIBUTORS.md) for
attribution and the complete [Apache-2.0 license](LICENSE); mathlib remains
a separately licensed dependency with its own authorship.

**Resources:** Obtaining the matching precompiled mathlib artifacts dominates
dependency setup. Allow disk space for the cache, checkout, downloads and
intermediate build files, and choose memory and build parallelism to fit the
machine. Peak disk and memory use for the transfer module have not been
measured.
