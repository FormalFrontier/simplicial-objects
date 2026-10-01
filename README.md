# Simplicial objects: augmented left décalage

Authors: Formal Frontier Agents.

This Lean library constructs the augmented left décalage and its canonical
extra degeneracy for **every simplicial object `X : SimplicialObject C`** in
an arbitrary `[Category* C]`. No terminal or zero object, additivity or limit
assumptions are required. Its public import is `SimplicialObjects`, which
exports `SimplicialObjects.LeftDecalage` but no private test declarations.

## Headline results

- [`augmented X`](SimplicialObjects/LeftDecalage.lean) has ordinary degree
  `P(X)ₙ = Xₙ₊₁` and augmentation target `X₀`. Its augmentation takes the
  new initial vertex: at degree zero `ε₀ = X.δ 1`, **not** `X.δ 0`.
- [`extraDegeneracy X`](SimplicialObjects/LeftDecalage.lean) builds mathlib's
  native `SimplicialObject.Augmented.ExtraDegeneracy (augmented X)` from the
  original zeroth degeneracies. All five defining equations, including the
  exceptional degree-zero face, hold. Mathlib then supplies `.section_`,
  `.splitEpi`, `.homotopy` and postcomposition `.map F`; these are not new
  implementations in this repository.
- [`functor C`](SimplicialObjects/LeftDecalage.lean) makes the augmented
  construction functorial; [`projection X`](SimplicialObjects/LeftDecalage.lean)
  is the natural ordinary simplicial `X.δ 0` projection, distinct in general
  from the augmentation. The section, higher extra-degeneracy components and
  projection have explicit naturality equations.

See the [left décalage guide](docs/LeftDecalage.md) for indexing, exact
equations, native construction and example clients. The homotopy is
**combinatorial**; no geometric realization, general-relative contraction,
exactness, spectra, K-theory theorem or source-coverage claim follows here.

## Use

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
checks these generic statements, native section, homotopy and transport,
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

**Artifact and verification:** The initial published artifact has a parentless
release history, separate from the development history, with the same file tree
as its independently reviewed internal release candidate. Its native checks
built both maintained roots and audited the complete transitive axiom inventory,
including private/generated declarations; only `propext`, `Classical.choice`
and `Quot.sound` occur. This is historical evidence for that artifact, not
review or release of subsequent documentation edits. See
[`CONTRIBUTORS.md`](CONTRIBUTORS.md) for distinct author, reviewer and
packaging credit; [`formalization.yaml`](formalization.yaml) inventories the
24 public names, not source-passage coverage. The complete license is
[Apache-2.0](LICENSE); mathlib remains a separately licensed dependency and
its own definitions retain upstream attribution.

**Expected cost and resources:** In that native check, with pinned Lean and the
matching *precompiled* mathlib cache, fetching/decompressing the cache took
40.565 s, checking it with a no-build Mathlib target took 5.637 s, and building
both library roots took 6.337 s (1,328 jobs). The 108 s total run also
included setup and axiom audits; these are measurements of
one cached workflow, **not** a clean-machine benchmark or a promise for other
hardware/network conditions. Cache evidence recorded 8,892 decompressed files
and 127,865 artifact paths totaling 6,674,961,684 *logical file bytes*
(about 6.22 GiB), **not** measured occupied disk blocks or peak disk use.
As a conservative *planning estimate*, allow at least 15 GiB of free disk for
the cache, checkout, downloads and intermediate build files; actual peak disk
use and peak memory were not measured. Choose memory and build parallelism to
fit the machine rather than treating these receipts as a RAM requirement;
runtime thread counts do not bound aggregate processes or memory.
