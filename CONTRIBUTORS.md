# Contributors and provenance

Authors: Formal Frontier Agents. This library's original mathematical Lean
statements, proofs, tests and guide are Formal Frontier project work distributed
under the complete [Apache-2.0 license](LICENSE), without claiming an
unverified copyright owner. Pinned mathlib is an imported dependency: its
underlying simplex-category and extra-degeneracy definitions, section,
split-epimorphism, combinatorial homotopy and transport are not copied here;
their license and authorship remain with mathlib. No third-party proof text,
book pages or other third-party source assets were copied into this package.

- Original author: Formalization Worker B, Hive Task
  `hive-request-70d06877e5e699898b36dbe11641b7ec79738c70` (UID
  `225bab0c-cabe-4d59-bd27-8bfb56fbd142`), wrote all 24 public declarations,
  proof bodies, the ordinary-import client and mathematical guide.
- Original independent reviewer: Formalization Worker A, Hive Task
  `hive-request-30f42bb5a6fe5e651b1362bbd0d91d0644653c65` (UID
  `76263885-a1d7-4ec2-99e6-882d015f71ec`), reviewed the isolated donor
  mathematics, API, private client and provenance, **not** this destination.
- Destination assembler: Formalization Worker B, Hive Task
  `hive-request-eb54cde8568c51131011c53b74ecb1e405a76b4b` (UID
  `4e718ef8-5d9c-4a2a-ad2b-01a84a1645e9`), relocated exact donor code
  with namespaces/imports mapped, wrote standalone packaging, metadata and
  updated documentation; no new mathematical proof is attributed to this move.
- Destination independent code reviewer: Formalization Worker A, Hive Task
  `hive-request-1e0cd9d36c59c56c6db94205825d16964ed8138f` (UID
  `57a71275-ee94-4473-92bd-4bfdb3ed64f1`), reviewed exact initial destination
  revision `cdbbde4f237d09ff1f3afbf107b71106fec29fe8` and approved its
  mathematics, API, provenance and packaging for destination-code acceptance.
  This review did not approve a later exact release candidate or publication.
- First-release readiness editor: Formalization Worker B, Hive Task
  `hive-request-035b9db51b8718f37e626475f3aae502cdc7d593` (UID
  `ca0e5b05-418a-440a-8052-8012c47c3361`), updated only the README,
  mathematical guide's historical status, metadata lifecycle fields and
  this attribution after initial code integration; no mathematical proof
  or build configuration is attributed to this documentation change.
- Prism is responsible maintainer for destination intake, review, integration
  and any release decision. Prism accepted the reviewed, native-checked initial
  destination revision as code; this does not itself approve or publish a release.

The exact accepted isolated predecessor is `FormalFrontier/incubator` commit
`6ac4e97edc37f52f53f6c97388943a18d0c10075`:

| This repository | Original project file |
| --- | --- |
| `SimplicialObjects/LeftDecalage.lean` | `Incubator/AlgebraicTopology/SimplicialObject/LeftDecalage.lean` |
| `SimplicialObjectsTest/LeftDecalage.lean` | `IncubatorTest/AlgebraicTopology/SimplicialObject/LeftDecalage.lean` |
| `docs/LeftDecalage.md` | `Incubator/AlgebraicTopology/SimplicialObject/LeftDecalage/README.md` |

The two Lean files preserve all original statements, proofs, attributes,
universe parameters and native types; only the project author/SPDX module
headers, namespace, and the private client's focused import change. The
guide's mathematics and examples remain, with module references, dated
status and reproduction commands adapted to this package. Public proof
expression retains the original author's credit; documentation, package
assembly, initial destination review and readiness editing retain distinct
credit. No incubator Git ancestry was copied onto
the destination branch. This construction is useful independently of any
source-specific research or coverage decision.
