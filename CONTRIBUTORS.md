# Contributors and provenance

Authors: Formal Frontier Agents. This AI-assisted Formal Frontier work is
distributed under the complete [Apache-2.0 license](LICENSE).

A Formal Frontier author agent wrote the original mathematical statements and
proofs in [`SimplicialObjects/LeftDecalage.lean`](SimplicialObjects/LeftDecalage.lean),
the ordinary-import client in
[`SimplicialObjectsTest/LeftDecalage.lean`](SimplicialObjectsTest/LeftDecalage.lean)
and the [mathematical guide](docs/LeftDecalage.md). Distinct agents independently
reviewed the mathematical development, package code and publication artifacts;
the reviewers were different from the author and from one another. This review
credit concerns left decalage, not the finite-fiber transfer module.

Other agents adapted namespaces and imports, assembled package roots and
[metadata](formalization.yaml), and edited the [README](README.md), guide and
attribution. These are assembly and editorial contributions, not new proof
authorship. Prism coordinated the original intake, integration, acceptance and
publication decisions, rather than mathematical authorship or independent
review. The repository is maintained collectively by the Formal Frontier source
maintainers.

Formal Frontier agents also wrote the finite-fiber transfer formalization in
[`SimplicialObjects/FiniteFiberTransfer.lean`](SimplicialObjects/FiniteFiberTransfer.lean)
and its [private client](SimplicialObjectsTest/FiniteFiberTransfer.lean).

Pinned mathlib is an imported, separately licensed dependency. Its underlying
simplex-category and extra-degeneracy definitions, section, split-epimorphism,
combinatorial homotopy and postcomposition transport are upstream constructions,
not new implementations here; mathlib retains its own authorship and license.
No third-party proof text, book pages or other third-party source assets were
copied into this package.
