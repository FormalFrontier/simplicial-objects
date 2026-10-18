# Simplicial objects

Authors: Formal Frontier Agents.

This Lean library develops augmented left décalage, finite-fiber transfers
and normalized simplicial chains. Décalage and its canonical extra degeneracy
apply to **every simplicial object `X : SimplicialObject C`** in an arbitrary
`[Category* C]`, without terminal or zero objects, additivity or limits.
Transfers use coefficient objects in a preadditive category with coproducts.
For any simplicial set and abelian coefficient group, the library also constructs
an integral tensor chain complex and an isomorphism to normalized coefficient chains.
These complexes are functorial in simplicial sets and additively functorial in
abelian coefficient groups.

The public import `SimplicialObjects` exports `SimplicialObjects.LeftDecalage`,
`SimplicialObjects.FiniteFiberTransfer`, `SimplicialObjects.Normalization`,
`SimplicialObjects.TensorCoefficients`, `SimplicialObjects.TensorMaps`,
`SimplicialObjects.TensorCoefficientMaps`, `SimplicialObjects.TensorHomotopies`,
`SimplicialObjects.TensorCoefficientFunctor`, `SimplicialObjects.PointHomology` and
`SimplicialObjects.TensorCoefficientSequences`; example modules have a separate root.

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
  `SimplicialObjectsTest.FiniteFiberTransfer` computes two- and six-sheet examples,
  empty sheets and zero coefficients, with independent coefficient/index universes.
- **Change of coefficient category.**
  [`SSet.chainComplexTransfer_mapHomologicalComplex`](SimplicialObjects/FiniteFiberTransfer.lean)
  proves compatibility of the all-simplex chain transfer with Mathlib's
  coefficient-comparison isomorphism for an additive functor `C ⥤ D` preserving
  coproducts indexed by types in the simplex universe. The source and target
  categories are preadditive and have those coproducts; only vertex fibers of
  the equifibered simplicial map need be finite.
  No preservation of homology or exactness is assumed. The two-sheet `ZMod 4`
  example independently computes coordinates `1 ⊗ 1`, nonzero by the left unitor,
  and pushforward two modulo four.

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
  without an additional finite-coproduct assumption. The integral
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
  On `Δ[1]`, tensoring with `ZMod 4` gives target coefficient object `ℤ ⊗[ℤ] ZMod 4`.
  Both edge coordinates are independently `1 ⊗ 1`, nonzero by the left unitor;
  collapse kills both, and the generator law sends source edge to target edge.
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
  The interval examples apply these laws to `2 • id + const(v₀)`, which does not
  preserve the raw nondegenerate summand, to the two-sheet transfer with nonzero
  pushforward two modulo four, and to the nonidentity tensor transformation induced
  by multiplication by two on `ZMod 4`. These coefficient-comparison laws are
  distinct from the integral tensor presentation below.
- **Integral tensor presentation of normalized chains.**
  [`TensorCoefficients`](SimplicialObjects/TensorCoefficients.lean) constructs
  `SSet.tensorNormalizedChainComplex` for every `A : Type a` with `[AddCommGroup A]`
  and `S : SSet.{w}`, using only the canonical `ℤ`-module structure.
  `SSet.tensorNormalizedChainIso` identifies this complex, with its independently
  defined alternating tensor boundary, with Mathlib's normalized chains with
  lifted coefficients. The coefficient, simplex and padding universes `a`, `w`, `p`
  are independent; no finiteness, flatness, field or nonemptiness hypothesis is needed.
- **Simplicial maps on integral tensor chains.**
  [`TensorMaps`](SimplicialObjects/TensorMaps.lean) defines the integral degree map
  by `[s] ↦ [f(s)]` and tensors it with the coefficient identity. Degenerate image
  classes are zero; `f : S ⟶ T` is arbitrary in `SSet.{w}`.
  It also constructs whole chain maps and a functor using the existing normalized
  chain map and chain comparison. The component and naturality statements relate
  this construction to the independently specified tensor-degree maps and boundary.
- **Chain homotopies of integral tensor maps.**
  [`TensorHomotopies`](SimplicialObjects/TensorHomotopies.lean) constructs a
  Mathlib `Homotopy` between the original tensor maps from a combinatorial
  simplicial homotopy, and adapts cylinder homotopies through the existing
  combinatorial conversion. The component formula displays the tensor
  comparisons and normalization section and projection around Mathlib's
  all-simplex chain homotopy. Only `[AddCommGroup A]` is needed, with independent
  coefficient, simplex and padding universes. Combinatorial or cylinder homotopies
  therefore give equal induced maps on natural-number-graded homology. The interval example computes
  the chosen degree-zero component as the negative edge tensor over `ZMod 4`,
  with distinct endpoint chain images and the independent terminal-minus-initial
  boundary. No relative or topological singular-homology identification is asserted.

- **Change of abelian coefficients.**
  [`TensorCoefficientMaps`](SimplicialObjects/TensorCoefficientMaps.lean) defines
  the degree operation `id ⊗ g` for every additive homomorphism `g : A →+ B`,
  with independent coefficient universes `a`, `b`, simplex universe `w` and padding `p`.
  The corresponding chain morphism conjugates the normalized coefficient morphism
  by the integral tensor comparison, without replacing the tensor boundary.
  Generator, uniqueness, identity and composition laws accompany both operations.
  The comparison is natural in coefficients, the raw tensor operation commutes
  with the alternating boundary, and the chain morphism has that operation as
  each component. Reduction modulo two on the standard interval
  kills a nonzero coefficient-two tensor and preserves a nonzero coefficient-one
  tensor; the reduced edge has nonzero boundary independently of those statements.
- **Additive functoriality in abelian coefficients.**
  [`TensorCoefficientFunctor`](SimplicialObjects/TensorCoefficientFunctor.lean) constructs
  `SSet.tensorNormalizedChainComplexCoefficientFunctor`, a functor from
  `AddCommGrpCat.{a}` to `SSet.{w} ⥤ ChainComplex (ModuleCat.{max a w p} ℤ) ℕ`.
  The coefficient, simplex and padding universes `a`, `w`, `p` are independent;
  simplicial sets and abelian groups are arbitrary. Both its fixed-coefficient
  objects and coefficient-map components use the common padding `q = max a p`.
  The five characteristic equations, with prefix
  `tensorNormalizedChainComplexCoefficientFunctor`, are `_obj`, `_obj_obj`,
  `_obj_map`, `_map_app` and `_map_app_f`. They identify the existing
  fixed-coefficient `tensorNormalizedChainComplexFunctor`, its tensor complexes
  and simplicial maps, and the coefficient natural transformation's components
  `tensorNormalizedChainComplexCoefficientMap` and raw degree operations
  `tensorNormalizedCoefficientMap` (`id ⊗ g`), respectively. Thus the existing
  pure-tensor and simplex formulas apply, with unchanged carriers and independently
  specified differentials. The functor data uses the existing identity,
  composition and mixed naturality laws. Its `Functor.Additive` instance is derived
  degreewise from `tensorNormalizedCoefficientMap_add`: the raw operation satisfies
  `C_(g+h) = C_g + C_h` for arbitrary additive homomorphisms `g,h : A →+ B`, with
  independent `a`, `b`, `w`, `p`, source padding `max b p` and target padding `max a p`.
  Both degree objects lie in `ModuleCat.{max a b w p} ℤ` on the original tensor carriers.
  Mathlib's `Functor.map_add` gives the corresponding equality of coefficient
  natural transformations; its generic additive-functor API also supplies zero,
  negation, subtraction, integer-multiple and finite-sum laws.

- **Exactness in abelian coefficients.**
  [`SSet.tensorNormalizedCoefficientMap_exact`](SimplicialObjects/TensorCoefficientMaps.lean)
  sends any pair `g : A →+ B`, `h : B →+ C` with `Function.Exact g h` to an
  exact pair of the existing tensor-degree maps, for every simplicial set and
  every degree. The three coefficient groups are arbitrary abelian groups in
  independent universes, with no coefficient-flatness, finiteness, injectivity
  or surjectivity assumption. Mathlib's `Module.Flat.lTensor_exact` applies to
  the free first factor `S.nonDegenerate n →₀ ℤ`; the outer lifts use common
  padding `max a b c w p`. The integer doubling/reduction sequence specializes
  this result to the standard point and interval.
- **Coefficient endpoints and short exact sequences.**
  [`TensorCoefficientMaps`](SimplicialObjects/TensorCoefficientMaps.lean) preserves
  injectivity and surjectivity in every tensor degree. In
  [`TensorCoefficientSequences`](SimplicialObjects/TensorCoefficientSequences.lean),
  the corresponding whole chain maps are monomorphisms and epimorphisms.
  `SSet.tensorNormalizedChainComplexCoefficientShortComplex` constructs a short
  complex from any exact coefficient pair, without endpoint assumptions. Its
  seven characteristic equations identify the three objects, both arrows and
  both raw degree components. An injective first coefficient map, exact middle
  and surjective second map give `ShortExact` on these same complexes, with
  independent `a`, `b`, `c`, `w`, `p` and common padding `max a b c w p`.
  The zero coefficient map gives the zero chain map. The point and interval
  doubling/reduction examples use the same coefficient inputs and retain
  their nonzero integer and reduced generators. Endpoint preservation reuses the
  existing free-Finsupp degree-exactness proof (`Module.Flat.finsupp` and
  `Module.Flat.lTensor_exact`), Mathlib's functional exactness and module-category
  endpoint criteria, and its degreewise short-exactness theorem for complexes.

- **Homology of terminal simplicial sets.**
  [`PointHomology`](SimplicialObjects/PointHomology.lean) gives
  `SSet.tensorNormalizedHomologyZeroIsoCoefficient : H₀(K) ≅ C`, with mutually
  inverse comparison morphisms, for every abelian `A : Type a` and every terminal
  `T : SSet.{w}`, with independent coefficient, simplex and padding universes `a`, `w`, `p`.
  Here `K = SSet.tensorNormalizedChainComplex.{a,w,p} A T` is the original
  normalized integral tensor complex, and `C = ModuleCat.of ℤ (ULift.{max w p} A)`
  lies in `ModuleCat.{max a w p} ℤ`. This coefficient lift is distinct from the
  raw degree carrier `ULift.{max a w p} ((T.nonDegenerate n →₀ ℤ) ⊗[ℤ] A)`.
  The comparison sends the class of a vertex tensor `[v] ⊗ x` to `ULift.up x`;
  its inverse recovers that class. The API includes balanced coefficient
  naturality and naturality for maps between terminal simplicial sets.
  All positive homology `Hₙ₊₁(K)` vanishes. More generally, for arbitrary
  `S : SSet.{w}` with `S.HasDimensionLT d`, its tensor homology vanishes in
  every degree `n ≥ d`.

The mixed naturality statements in `TensorCoefficientMaps` express simultaneous
simplicial and coefficient change: `T_A(f) ≫ C_g(T) = C_g(S) ≫ T_B(f)`, both in
each raw tensor degree and for whole chain morphisms. They use source padding
`max b p` and target padding `max a p`, with independent `a`, `b`, `w`, `p`.
The interval collapse and multiplication by two on `ZMod 4` give the same named
clients at the degree and chain levels; a coefficient-one vertex maps to a
nonzero coefficient-two vertex by a computation independent of these statements.

| Module | Interface |
| --- | --- |
| `SimplicialObjects.TensorMaps` | Simplicial degree maps, chain maps and naturality laws |
| `SimplicialObjects.TensorHomotopies` | Chain homotopies, component formulas and equality of induced homology maps |
| `SimplicialObjectsTest.TensorMaps` | Identity, collapse and tensor-boundary examples |
| `SimplicialObjects.TensorCoefficientMaps` | Abelian coefficient operations, additivity, degreewise exactness, endpoint preservation and compatibility laws |
| `SimplicialObjects.TensorCoefficientFunctor` | Additive coefficient-curried tensor-chain functor and five characteristic equations |
| `SimplicialObjects.TensorCoefficientSequences` | Coefficient short complexes, seven characteristic equations, chain Mono/Epi and short exactness |
| `SimplicialObjectsTest.TensorCoefficientMaps` | Additive coefficient-functor controls, reduction modulo two, coefficient inputs and short-complex nonzero generators and boundaries |
| `SimplicialObjectsTest.TensorCoefficientEndpoints` | The five endpoint and short-exactness specializations on the point and interval |
| `SimplicialObjects.PointHomology` | Terminal-set degree-zero comparisons, inverse and class laws, naturality and dimension vanishing |
| `SimplicialObjectsTest.PointHomology` | Reduction modulo two through point homology and positive-degree vanishing |

See the [left décalage guide](docs/LeftDecalage.md) for indexing, exact
equations, construction and example clients. The homotopy is
**combinatorial**; no geometric realization, general-relative contraction,
long exact sequence, spectra, K-theory theorem or source-coverage claim follows here.

The point-homology statements concern **simplicial normalized chains** and
nonnegatively indexed ordinary homology only. They do not supply a `TopCat` or
singular-chain comparison, reduced or relative homology, a long exact sequence,
or all the results of May's cited sections, and make no source-wide coverage claim.
Their mathematical background is J. Peter May's *A Concise Course in Algebraic
Topology*, revised author edition, §§13.1 and 16.4. The constructions use
Mathlib's categorical homology, dimension bounds, Finsupp coordinates and terminal
transport, together with this library's existing integral tensor formalization.

## Integral tensor chains and coordinates

Import `SimplicialObjects.TensorCoefficients`; these declarations are in `SSet`.
Write `Nₙ = S.nonDegenerate n` and `Bₙ = Nₙ →₀ ℤ`. The class `[s]`,
`normalizedIntegralSimplex S s`, is the basis vector of a nondegenerate simplex
and zero for a degenerate one. The linear map `normalizedIntegralBoundary S n` is
`∂ℤ : Bₙ₊₁ →ₗ[ℤ] Bₙ`, specified on nondegenerate generators by
`∂ℤ [s] = ∑ᵢ (-1)ⁱ [δᵢ s]` for `i = 0, …, n + 1`.
The zeroth face is positive and degenerate faces contribute zero; `_single` gives
this formula and `_eq_iff` characterizes the boundary uniquely.

The degree object `tensorNormalizedChainComplexX.{a,w,p} A S n` is
`ModuleCat.of ℤ (ULift.{max a w p} (Bₙ ⊗[ℤ] A))`.
`tensorNormalizedBoundary` lifts `(∂ℤ).rTensor A`: a lifted `z ⊗ x` maps to the
lift of `∂ℤ z ⊗ x`. `tensorNormalizedDifferential` uses this boundary only from
`n + 1` to `n`, and is zero elsewhere, including all outgoing degree-zero maps.
`tensorNormalizedDifferential_comp` gives square-zero. The assembled complex has
object, pure-tensor differential and off-shape laws `tensorNormalizedChainComplex_X`,
`tensorNormalizedChainComplex_d_tmul` and `tensorNormalizedChainComplex_d_eq_zero`.

`normalizedChainComplexXIsoFinsupp` identifies the **whole normalized degree**
with `Nₙ →₀ M`, for any ring `R : Type r` and `M : ModuleCat.{max w v} R`, with
independent `r`, `w`, `v`. It composes Mathlib's normalized cofan universal property,
coproduct/direct-sum isomorphism and inverse Finsupp/direct-sum isomorphism.
`tensorNormalizedChainComplexXIsoFinsupp` uses `TensorProduct.finsuppScalarLeft`:
the coordinate at `s` of a lifted `z ⊗ x` is `ULift.up (z s • x)`.
The canonical comparison `Ψₙ = tensorNormalizedChainComplexXIso A S n` is tensor coordinates
followed by inverse normalized coordinates, landing in the whole normalized degree
with coefficient object `ModuleCat.of ℤ (ULift.{max w p} A)`.
`tensorNormalizedChainComplexXIso_hom_d` gives `Ψᵢ ≫ dᴺ = dᵀ ≫ Ψⱼ`, yielding
`tensorNormalizedChainIso`; the boundary is not defined by transport through Ψ.
`tensorNormalizedChainIso_hom_f_apply` sends every `[s] ⊗ x` to the normalized
inclusion of `s` with coefficient `ULift.up x`, including zero degenerate classes.
`tensorNormalizedChainIso_inv_f_ι` recovers nondegenerate tensors. The coordinate
inclusion/single/inverse laws, degreewise hom-extensionality and
`tensorNormalizedChainIso_eq_iff` let users compute and characterize these maps.

The [interval examples](SimplicialObjectsTest/TensorCoefficients.lean) compute
`∂[edge] = [v₁] - [v₀]` on `Δ[1]`, with a **nonzero boundary over `ZMod 4`**,
and evaluate Ψ and its inverse. Pushforward of the existing two-sheet all-simplex
transfer, followed by normalization, has vertex coefficient two modulo four;
inverse tensor coordinates recover a nonzero tensor with coefficient two.
This is coordinate recovery, not a new arbitrary tensor transfer chain map or
naturality theorem. Degenerate edges, outgoing degree-zero maps and empty sheets
give zero. May's *A Concise Course in Algebraic Topology*, revised edition, §16.1
motivates the integral tensor presentation; no topological singular-chain
identification or homology comparison is asserted.

## Simplicial maps in tensor coordinates

Import `SimplicialObjects.TensorMaps`. For `f : S ⟶ T`,
`SSet.normalizedIntegralMap f n` is the linear map from `S.nonDegenerate n →₀ ℤ`
to `T.nonDegenerate n →₀ ℤ` sending a basis vector to
`T.normalizedIntegralSimplex (f.app (op ⦋n⦌) s.val)`. The `_single`, `_simplex`
and `_eq_iff` laws compute and characterize it, including degenerate images.
`tensorNormalizedChainComplexXMap.{a,w,p} A f n` is its lifted right tensor with
`A`; `_tmul`, `_single`, `_simplex` and `_eq_iff` give its characteristic API.
Extensionality is the existing `tensorNormalizedChainComplexX_hom_ext`.

`tensorNormalizedChainComplexMap A f` conjugates Mathlib's normalized-chain map
by the existing `tensorNormalizedChainIso` at source and target. It acts between
the specified tensor complexes; it changes neither their carriers nor their
positive-zeroth-face boundary. Identity and composition give
`tensorNormalizedChainComplexFunctor A`. The statement
`tensorNormalizedChainComplexMap_f` identifies its components with the raw
tensor-degree maps. `tensorNormalizedChainComplexXIso_hom_naturality` states
`Ψ_S ≫ N(f) = T(f) ≫ Ψ_T` in each whole `ModuleCat` degree;
`tensorNormalizedChainComplexXMap_d` states compatibility with the independent
differential, and `tensorNormalizedChainIso_hom_naturality` is the whole-chain
square. All retain independent `a`, `w`, `p` and arbitrary abelian coefficients,
without injectivity, finite fibers, flatness or nonemptiness assumptions.

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

`SimplicialObjectsTest.LeftDecalage` also checks section, homotopy, transport and
naturality, a nonterminal `Bool` example and unequal first faces on the standard
simplicial edge. Example modules are not part of the public root.

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
