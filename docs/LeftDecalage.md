# Augmented left décalage

For any category `C` and simplicial object `X : SimplicialObject C`,
`SimplicialObjects.LeftDecalage.augmented X` constructs the augmented left décalage
`P(X) ⟶ const(X₀)`. No terminal object, zero object, additivity, or limits
in `C` are required. Its ordinary degrees are `P(X)ₙ = Xₙ₊₁`, so **ordinary
degree zero is `X₁`, not the augmentation object `X₀`**.

The native augmented simplex category supplies the empty ordinal; `index`
adjoins a new *initial* vertex, sending that ordinal to `[0]`. The functor
`AugmentedSimplexCategory.equivAugmentedSimplicialObject` converts precomposition
by `index.op` to the augmented object. On a nonempty simplex morphism `α`,
`prependMap α` fixes vertex zero and maps `j + 1` to `α(j) + 1`: this is the
left ordinal sum with `[0]`, expressed with canonical degree objects.

## Mathematical API

Import `SimplicialObjects.LeftDecalage` and open
`SimplicialObjects.LeftDecalage` and the `Simplicial` scope. The value, face, and
degeneracy readbacks are `path_obj`, `path_face`, and `path_degeneracy`:

```text
P(X)ₙ = Xₙ₊₁
dᵖᵢ = dˣᵢ₊₁        sᵖᵢ = sˣᵢ₊₁
εₙ = X([0] → [n+1], 0 ↦ 0)       ε₀ = dˣ₁
qₙ = dˣ₀ : P(X)ₙ → Xₙ            q₀ = dˣ₀
```

`augmentation_app` and `augmentation_zero` read the augmentation; `projection`
and `projection_zero` read the ordinary simplicial projection. In general
`ε₀ ≠ q₀`: they select opposite ends of an edge. The private client proves
this inequality for the standard simplicial 1-simplex. `functor C` acts on
morphisms by the original components in shifted degrees and in degree zero
on augmentation objects (`functor_map_left_app`, `functor_map_right`).
`naturalProjection C` proves that `q` varies naturally in `X`.
`extraDegeneracy_s'_naturality` and `extraDegeneracy_s_naturality` give
the section and higher-component naturality equations in `X`.

`extraDegeneracy X` is **mathlib's own**
`SimplicialObject.Augmented.ExtraDegeneracy (augmented X)`, not a new homotopy
formalism. Its section `s' : X₀ ⟶ P(X)₀` and every `sₙ : P(X)ₙ ⟶ P(X)ₙ₊₁`
are the original `sˣ₀`. The structure proves its five equations, including
the exceptional degree-zero boundary:

```text
s' ≫ ε₀ = id       s₀ ≫ dᵖ₁ = ε₀ ≫ s'
sₙ ≫ dᵖ₀ = id     sₙ₊₁ ≫ dᵖᵢ₊₁ = dᵖᵢ ≫ sₙ
sₙ ≫ sᵖᵢ₊₁ = sᵖᵢ ≫ sₙ₊₁
```

In the fourth equation `0 ≤ i ≤ n + 1`; in the fifth `0 ≤ i ≤ n`.
Use `(extraDegeneracy X).section_`, its `section_comp_hom` or `splitEpi`,
and `(extraDegeneracy X).homotopy` for the native combinatorial homotopy
`ε ≫ section_ ~ id` on `P(X)`. These generic constructions are imported
from mathlib; this module proves their input data, rather than reproving
the generic contraction. For a functor `F : C ⥤ D`, native
`(extraDegeneracy X).map F` transports these data to the postcomposed
augmented object. No strict identification with `augmented (X ⋙ F)` is claimed.

## Usage

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

The ordinary-import private client
`SimplicialObjectsTest.LeftDecalage` also checks
generic functoriality, projection naturality, native section/homotopy,
postcomposition transport, a nonterminal two-point simplicial set, and
the distinct endpoints of the standard simplicial edge.

## Reproduction and provenance

At **2026-09-29**, the original isolated producer, client and guide at
`FormalFrontier/incubator@6ac4e97edc37f52f53f6c97388943a18d0c10075`
had independent mathematical/API review and focused cache-first build and
standard-axiom evidence in that **donor** project. Separately, the initial
destination revision `cdbbde4f237d09ff1f3afbf107b71106fec29fe8` received
independent destination-code review and a successful native both-root build and
complete transitive standard-three axiom audit, including private/generated
declarations. Prism accepted that revision as **code**; this historical fact
does not assert acceptance of a later exact release candidate or any private
or public publication.
The project pins Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` in its Lake files. In a
checkout of this project, install the pinned toolchain, fetch the matching
precompiled mathlib cache **before** building, then build the public producer
and its ordinary-import private client:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build SimplicialObjects SimplicialObjectsTest
```

For the measured cache-first workload and explicitly estimated disk planning
guidance (not a memory benchmark), see [expected cost and resources](../README.md#reproduce-and-verification).

The general categorical construction and proof were written for this library
contribution by Formal Frontier worker-b Task
`hive-request-70d06877e5e699898b36dbe11641b7ec79738c70`
(UID `225bab0c-cabe-4d59-bd27-8bfb56fbd142`), based on standard ordinal
identities and mathlib's simplex-category, augmentation-equivalence and
extra-degeneracy APIs. The contributed files use the repository's Apache-2.0
license; native mathlib definitions retain their own upstream attribution.
No private source research record is needed to use or understand the API.
See [contributors and provenance](../CONTRIBUTORS.md) for the exact mapped
files and the original independent reviewer and destination assembler.

This is a combinatorial simplicial homotopy, **not** a realization or
topological contractibility theorem. No generic relative pullback contraction,
Waldhausen/exact-category construction, spectra, or source-specific K-theory
statement is implemented or asserted here.
