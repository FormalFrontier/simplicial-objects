# Simplicial objects

This Lean library develops augmented left décalage, finite-fiber transfers,
integral all-simplex coordinates and normalized simplicial chains. It also gives
integral tensor presentations, coefficient functoriality and degree-zero
component comparisons for simplicial sets and singular simplices.

Detailed statements, APIs, formulas, examples and universe conventions are in
[Constructions and mathematical APIs](docs/Constructions.md); indexing and all
five extra-degeneracy equations are in the [left décalage guide](docs/LeftDecalage.md).

## Headline results

- **Integral all-simplex chain coordinates**
  ([`chainGroupIsoFinsupp`](SimplicialObjects/ChainCoordinates.lean),
  [`chainComplexIsoFinsupp`](SimplicialObjects/ChainComplexCoordinates.lean)).
  For any ring `R`, `AlgebraicTopology.finsuppChainComplexFunctor R` gives the
  ordinary-Finsupp alternating-face chain complex, with independent ring and
  simplex universes. Over `ℤ`, `chainComplexIsoFinsupp` is a natural isomorphism
  from the existing `SSet.chainComplexFunctor` at the original coefficient object
  `(ModuleCat.uliftFunctor.{u} ℤ).obj (ModuleCat.of ℤ ℤ)` to this functor.
  For every `X : SSet.{u}` and degree `n`, its evaluation isomorphism is exactly
  `chainGroupIsoFinsupp X n`: both forward and inverse degree maps are the
  original maps on every chain, not merely on generators. The two summand laws
  still compute lifted integers and unit basis chains. Naturality holds for
  every simplicial map and every chain; pushforwards add coefficients of
  coincident images, without finite-fiber or injectivity assumptions.
  In every degree the [boundary coordinates](SimplicialObjects/ChainBoundaryCoordinates.lean)
  are the signed sum of face pushforwards. This comparison concerns all simplices,
  not normalized chains or homology. The
  [standard-point chain](SimplicialObjectsTest/ChainCoordinates.lean) is nonzero;
  the [identity edge of `Δ[1]`](SimplicialObjectsTest/ChainBoundaryCoordinates.lean)
  has boundary `[v₁] - [v₀]`, nonzero as a chain, not as a homology class.
- **Augmented left décalage and its canonical extra degeneracy**
  ([`LeftDecalage`](SimplicialObjects/LeftDecalage.lean)).
  For every simplicial object in any category, `P(X)ₙ = Xₙ₊₁` augments to `X₀`,
  with `ε₀ = X.δ 1`, not in general the ordinary projection `X.δ 0`.
  No terminal/zero objects, additivity or limits are required. Functoriality and
  naturality are explicit; Mathlib supplies the section and combinatorial homotopy.
- **Finite-fiber transfers and coefficient comparison**
  ([`FiniteFiberTransfer`](SimplicialObjects/FiniteFiberTransfer.lean)).
  In a preadditive category with simplex-indexed coproducts, equifibered simplicial
  maps with finite vertex fibers admit reverse-composing transfers. No fixed sheet
  number is needed. A constant vertex-fiber cardinality `d` gives pushforward
  after transfer equal to `d • id` on chains and, with homology, in every degree.
  Additive functors preserving those coproducts commute with transfer; no exactness
  or homology preservation is assumed. Pullback and coefficient laws are included.
- **Normalized descent and change of coefficient category**
  ([`Normalization`](SimplicialObjects/Normalization.lean)).
  Morphisms between split simplicial objects in a preadditive category descend
  without preserving chosen nondegenerate summands. For preadditive coefficient
  categories with `HasCoproducts.{w}`, additive functors preserving exactly
  `Discrete T` colimits for `T : Type w` compare normalized chains naturally,
  compatibly with projection, section, transfers and natural transformations.
  All five category/simplex universes are independent; no exactness or Abelian
  assumption is needed. These are distinct from the integral tensor presentation.
- **Integral tensor chains, simplicial maps and homotopies**
  ([`TensorCoefficients`](SimplicialObjects/TensorCoefficients.lean),
  [`TensorMaps`](SimplicialObjects/TensorMaps.lean),
  [`TensorHomotopies`](SimplicialObjects/TensorHomotopies.lean)).
  For every abelian group `A` and simplicial set `S`, the independently defined
  alternating tensor boundary gives a complex naturally isomorphic to normalized
  chains with lifted coefficients. Coefficient, simplex and padding universes are
  independent; no finiteness, flatness, field or nonemptiness is assumed.
  Simplicial monomorphisms give monic chain maps without flatness of `A`.
  Combinatorial or cylinder homotopies give chain homotopies and equal homology maps;
  two-sided simplicial homotopy inverses and extra-degenerate augmentations give
  quasi-isomorphisms. For normalized chains the coefficient category need only be
  preadditive with coproducts and homology; augmentation targets need not be terminal.
  [Cokernel comparison](SimplicialObjects/TensorCokernels.lean) applies to all arrows;
  its nonzero omitted-vertex example concerns chain cokernels, not homology.
- **Additive and exact change of abelian coefficients**
  ([`TensorCoefficientMaps`](SimplicialObjects/TensorCoefficientMaps.lean),
  [`TensorCoefficientFunctor`](SimplicialObjects/TensorCoefficientFunctor.lean),
  [`TensorCoefficientSequences`](SimplicialObjects/TensorCoefficientSequences.lean)).
  Arbitrary additive maps act by `id ⊗ g`, naturally in both variables, on the
  original tensor carriers and boundary. The coefficient-curried functor is
  additive and preserves finite limits and colimits. Any exact coefficient pair
  stays exact degreewise; injective and surjective endpoints give chain Mono/Epi
  and short exactness. Universes remain independent with common balanced padding;
  no coefficient flatness or endpoint assumption is added to middle exactness.
  This is exactness of a chain-valued functor, not exactness after homology.
- **Degree-zero homology, components and path components**
  ([`TensorHomologyZero`](SimplicialObjects/TensorHomologyZero.lean),
  [`SingularHomologyZero`](SimplicialObjects/SingularHomologyZero.lean)).
  For every abelian `A` and simplicial set `S`, tensor `H₀` is the coproduct of
  `ModuleCat.of ℤ (ULift.{max w p} A)` over `SSet.π₀ S`, naturally in simplicial
  and additive coefficient maps, with independent `a`, `w`, `p` and no finiteness,
  flatness, field, basis or nonemptiness hypotheses. For singular simplices of any
  topological space this gives the coproduct over `ZerothHomotopy X`, naturally in
  continuous and coefficient maps, without local path connectedness. The direct
  [path-component functor](SimplicialObjects/PathComponents.lean) agrees naturally
  with singular components via Mathlib's equivalence.
- **Degree-zero normalized homology of binary products**
  ([`tensorNormalizedHomologyZeroProductIso`](SimplicialObjects/TensorHomologyZeroProducts.lean)).
  For arbitrary abelian groups `A`, `B` and simplicial sets `K`, `L`,
  `H₀ᴺ(K; A) ⊗ℤ H₀ᴺ(L; B) ≅ H₀ᴺ(K × L; A ⊗ℤ B)`, using canonical
  universe lifts with independent coefficient, simplex and padding universes.
  Pure tensors of vertex classes map to the paired vertex class with pure tensor
  coefficient; inverse formulas, extensionality and uniqueness characterize the maps.
  [Forward and inverse naturality](SimplicialObjects/TensorHomologyZeroProductNaturality.lean)
  hold for simplicial maps in both factors and arbitrary additive maps in both
  coefficient groups, with balanced padding for coefficient change. No finiteness,
  flatness, connectedness or nonemptiness is assumed. A
  [discrete two-by-two example](SimplicialObjectsTest/TensorHomologyZeroProducts.lean)
  distinguishes the four nonzero vertex tensors and their four product classes,
  and evaluates simplicial and coefficient maps on them.
- **Component folds, terminal sets and dimension vanishing**
  ([`TensorHomologyZeroConnected`](SimplicialObjects/TensorHomologyZeroConnected.lean),
  [`TensorHomologyZeroEmpty`](SimplicialObjects/TensorHomologyZeroEmpty.lean),
  [`PointHomology`](SimplicialObjects/PointHomology.lean)).
  The fold agrees with collapse and terminal coefficient evaluation for every
  source, including the empty one. Connectedness makes the fold an isomorphism.
  Terminal sets have the lifted coefficient object in degree zero and zero
  positive homology. More generally `S.HasDimensionLT d` gives vanishing in
  degrees `n ≥ d`; `H₀(∂Δ[0])` is zero. Arbitrary abelian coefficients and independent
  coefficient/simplex/padding universes are retained.
- **Coefficient naturality of ordinary simplicial `H₀`**
  ([`HomologyZero`](SimplicialObjects/HomologyZero.lean)).
  Mathlib's `SSet.homology₀Iso` and its inverse commute with every coefficient
  morphism in any preadditive category with `HasCoproducts.{w}` and homology,
  with independent object, morphism and simplex universes. The all-degree
  coefficient-generator law needs no homology assumption. This is separate from
  normalized tensor homology and asserts no singular or relative comparison.

## Using the library

Import `SimplicialObjects` for the public API, or import a module directly.
For the integral chain-complex comparison and boundary formulas, import
`SimplicialObjects.ChainComplexCoordinates`.

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

`SimplicialObjectsTest.LeftDecalage` also checks section, homotopy, transport and
naturality, a nonterminal `Bool` example and unequal first faces on the standard
simplicial edge. Example modules are not part of the public root.

<a id="reproduce-and-verification"></a>
## Building

The pinned Lean toolchain is `leanprover/lean4:v4.34.0-rc2`; the direct
dependencies are GitHub mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`
and [`projective-modules`](https://github.com/FormalFrontier/projective-modules)
`08efdc3703d199727871d0f3dbd5d3c9c4fde8bb`.
In a checkout, use the committed `lake-manifest.json` and fetch matching
precompiled mathlib artifacts **before** building:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build SimplicialObjects SimplicialObjectsTest
```

**Verification targets:** The two maintained roots include example modules for
the decalage, transfer, normalization and integral tensor APIs.
[`formalization.yaml`](formalization.yaml) is a public API index, not a
source-passage coverage map. See [`CONTRIBUTORS.md`](CONTRIBUTORS.md) for
attribution and the complete [Apache-2.0 license](LICENSE); mathlib remains
a separately licensed dependency with its own authorship.

**Resources:** Obtaining the matching precompiled mathlib artifacts dominates
dependency setup. Allow disk space for the cache, checkout, downloads and
intermediate build files, and choose memory and build parallelism to fit the
machine. Peak disk and memory use for the transfer module have not been
measured.

## Contents

| Module | Interface |
| --- | --- |
| `SimplicialObjects.ChainCoordinates` | Integral all-simplex degree coordinates and the two summand laws |
| `SimplicialObjectsTest.ChainCoordinates` | A nonzero lifted integer vertex chain on the standard point |
| `SimplicialObjects.ChainBoundaryCoordinates` | Alternating face pushforwards in integral all-simplex coordinates |
| `SimplicialObjects.ChainComplexCoordinates` | Ordinary-Finsupp chain-complex functor for any ring and the integral natural isomorphism with the original degree coordinates |
| `SimplicialObjectsTest.ChainBoundaryCoordinates` | The genuine standard identity-edge boundary and its nonvanishing as a chain |
| `SimplicialObjects.TensorMaps` | Simplicial degree maps, chain maps and the fixed-coefficient natural comparison |
| `SimplicialObjects.TensorCokernels` | All-arrow cokernel natural comparison, component compatibility and projection laws |
| `SimplicialObjects.TensorHomotopies` | Chain homotopies, component formulas, homology invariance and quasi-isomorphisms from homotopy inverses or extra-degenerate augmentations |
| `SimplicialObjectsTest.TensorMaps` | Identity, collapse, tensor-boundary, augmentation and proper-face chain-cokernel examples |
| `SimplicialObjects.TensorCoefficientMaps` | Abelian coefficient operations, additivity, degreewise exactness, endpoint preservation and compatibility laws |
| `SimplicialObjects.TensorCoefficientFunctor` | Additive coefficient-curried tensor-chain functor, characteristic equations, short-complex evaluation and finite limit/colimit preservation |
| `SimplicialObjects.TensorCoefficientSequences` | Coefficient short complexes, seven characteristic equations, chain Mono/Epi and short exactness |
| `SimplicialObjectsTest.TensorCoefficientMaps` | Additive and exact coefficient-functor controls, reduction modulo two, coefficient inputs and short-complex nonzero generators and boundaries |
| `SimplicialObjectsTest.TensorCoefficientEndpoints` | The five endpoint and short-exactness specializations on the point and interval |
| `SimplicialObjects.PointHomology` | Terminal-set degree-zero comparisons, inverse and class laws, naturality and dimension vanishing |
| `SimplicialObjectsTest.PointHomology` | Reduction modulo two through point homology and positive-degree vanishing |
| `SimplicialObjects.TensorHomologyZero` | Component isomorphism, raw vertex classes, signed edge boundary and endpoint equality |
| `SimplicialObjects.TensorHomologyZeroNaturality` | All-map simplicial naturality of the component isomorphism and its inverse |
| `SimplicialObjects.TensorHomologyZeroCoefficientMaps` | Universe-balanced additive coefficient and mixed naturality squares |
| `SimplicialObjects.TensorHomologyZeroConnected` | All-source fold, connected coefficient isomorphism and terminal compatibility |
| `SimplicialObjects.TensorHomologyZeroEmpty` | Zero degree-zero homology of the empty standard boundary |
| `SimplicialObjects.TensorHomologyZeroProducts` | Binary product isomorphism, forward and inverse vertex-class laws, pure-tensor extensionality and uniqueness |
| `SimplicialObjects.TensorHomologyZeroProductNaturality` | Forward and inverse simplicial and balanced additive-coefficient naturality squares |
| `SimplicialObjectsTest.TensorHomologyZeroProducts` | Four distinct nonzero classes of a discrete two-by-two product and evaluations of the product comparison and its naturality |
| `SimplicialObjects.SingularHomologyZero` | Singular normalized tensor homology by path components and the singular-vertex formula |
| `SimplicialObjects.SingularHomologyZeroNaturality` | Forward and inverse continuous-map naturality |
| `SimplicialObjects.SingularHomologyZeroCoefficientMaps` | Balanced additive coefficient and mixed naturality |
| `SimplicialObjectsTest.SingularHomologyZero` | Discrete two-point vertex classes and space/coefficient map evaluations |
| `SimplicialObjects.HomologyZero` | Degree-zero chain projection, simplicial naturality, all-degree coefficient-generator law and coefficient naturality of the zeroth-homology isomorphism and inverse |
| `SimplicialObjectsTest.HomologyZeroPoint` | Forward and inverse naturality evaluated on the point class and component generator, with integer augmentation and reduction modulo two |

## Conventions and limitations

All-simplex coordinates retain degenerate simplices; normalized integral
coordinates use `S.nonDegenerate n →₀ ℤ`, killing degenerate classes.
The zeroth face has positive sign: on `Δ[1]`, `∂[edge] = [v₁] - [v₀]`.
The coefficient lift and outer tensor-carrier lift are distinct; see the
[exact formulas and balanced universes](docs/Constructions.md#integral-tensor-chains-and-coordinates).
Simplicial components mean vertex classes under edge zigzags, not components of
an asserted realization. Homology here is ordinary and nonnegatively indexed;
no reduced/relative theory, long exact sequence, general topological chain
identification, geometric realization, spectra or K-theory theorem is supplied.
No source-wide coverage claim is made.
SphereTopology versions defining the four integral coordinates independently
cannot co-import with this home; use matching versions reexporting this home.
The [detailed guide](docs/Constructions.md) retains the precise scopes and examples.

## References

- J. Peter May, *A Concise Course in Algebraic Topology*, revised author edition,
  §§13.1, 16.1 and 16.4 (mathematical background; not a source-wide formalization).
- [ProjectiveModules](https://github.com/FormalFrontier/projective-modules),
  especially `ModuleCat.freeOn`, for ordinary free modules with independent ring
  and generator universes.
- Mathlib's simplicial, normalization, categorical homology and colimit APIs;
  attribution and the role of the existing formalizations are detailed below
  and in the [mathematical guide](docs/Constructions.md).

## Credits and license

Authors: Formal Frontier Agents. This is AI-assisted mathematical formalization, using Mathlib's
simplicial, Dold–Kan normalization and homology constructions, notably Joël Riou's normalization and
degree-zero component formalization, and this library's integral tensor comparison and terminal
coefficient API. Formal Frontier Agents, including Prism, wrote the integral all-simplex coordinates,
using Mathlib's module-category colimits, lifted module functor and Finsupp linear equivalences.
The chain-complex comparison uses ProjectiveModules' `ModuleCat.freeOn`, which generalizes
Mathlib's free-module functor to independent ring and generator universes. Kim Morrison
and Johan Commelin developed the Mathlib construction.
May's *A Concise Course in Algebraic Topology*, revised edition, provides the mathematical background cited above; no source-wide formalization is claimed. Existing contributor
and source credit is retained in [CONTRIBUTORS.md](CONTRIBUTORS.md). Licensed under
[Apache-2.0](LICENSE); Mathlib retains its own license and authorship.
