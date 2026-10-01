# Contributors and provenance

Authors: Formal Frontier Agents. This is AI-assisted Formal Frontier project
work distributed under the complete [Apache-2.0 license](LICENSE), without
asserting an unverified copyright holder or independent human review. Distinct
contributions to the initial published library are:

- **Original author:** a Formal Frontier author agent wrote the mathematical
  statements and proofs in [`SimplicialObjects/LeftDecalage.lean`](SimplicialObjects/LeftDecalage.lean),
  the ordinary-import client in
  [`SimplicialObjectsTest/LeftDecalage.lean`](SimplicialObjectsTest/LeftDecalage.lean)
  and the [mathematical guide](docs/LeftDecalage.md), including the 24 public
  declarations. Their proof expression retains this original credit.
- **Original independent reviewer:** a different Formal Frontier agent
  reviewed the mathematics, API, client and provenance in the isolated
  predecessor project, not the destination package.
- **Destination assembler:** a Formal Frontier agent transferred the original
  mathematics into this standalone package with namespace/import relocation,
  maintained roots, [metadata](formalization.yaml) and adapted documentation;
  the transfer is not a new proof contribution.
- **Destination independent code reviewer:** another agent independently
  reviewed the initial package's mathematics, API, provenance and packaging
  before its code acceptance. This was not the final release review.
- **First-release readiness editor:** an agent revised the [README](README.md),
  guide, metadata and attribution after code integration, without changing
  proofs or build configuration.
- **Final release reviewer:** a fresh independent Formal Frontier agent
  reviewed the exact original internal and parentless public artifacts before
  their separate release decisions. The original reviewers and author are
  distinct executions even when service identities are reused.
- **Responsible maintainer:** Prism coordinated intake, protected integration
  and separate acceptance and publication decisions; these roles do not
  reattribute mathematical proofs or supply independent review.

Pinned mathlib is an imported, separately licensed dependency. Its underlying
simplex-category and extra-degeneracy definitions, section, split-epimorphism,
combinatorial homotopy and postcomposition transport are upstream constructions,
not new implementations here; mathlib retains its own authorship and license.
No third-party proof text, book pages or other third-party source assets were
copied into this package. The guide and API stand independently of any
source-specific research or coverage decision. Later documentation edits need
their own review and applicable verification before release.
