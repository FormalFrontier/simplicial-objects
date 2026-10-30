# Constructions and mathematical APIs

[Library overview and build instructions](../README.md).
The descriptions below distinguish all-simplex chains, normalized chains and
homology, including their coefficient objects and independent universes.

This Lean library develops augmented left décalage, finite-fiber transfers,
integral all-simplex coordinates and normalized simplicial chains. Décalage and its
canonical extra degeneracy apply to **every simplicial object `X : SimplicialObject C`** in an arbitrary
`[Category* C]`, without terminal or zero objects, additivity or limits.
Transfers use coefficient objects in a preadditive category with coproducts.
For any simplicial set and abelian coefficient group, the library also constructs
an integral tensor chain complex and an isomorphism to normalized coefficient chains.
These complexes are functorial in simplicial sets and additively functorial in
abelian coefficient groups. Their degree-zero homology is the coproduct of the
lifted coefficient object over simplicial components, naturally in both variables.
For singular simplices this gives the coproduct over topological path components,
naturally in continuous maps and additive coefficient homomorphisms.

The public import `SimplicialObjects` exports `SimplicialObjects.LeftDecalage`,
`SimplicialObjects.PathComponents`,
`SimplicialObjects.FiniteFiberTransfer`, `SimplicialObjects.ChainCoordinates`,
`SimplicialObjects.Normalization`,
`SimplicialObjects.TensorCoefficients`, `SimplicialObjects.TensorMaps`,
`SimplicialObjects.TensorCokernels`,
`SimplicialObjects.TensorCoefficientMaps`, `SimplicialObjects.TensorHomotopies`,
`SimplicialObjects.TensorCoefficientFunctor`, `SimplicialObjects.PointHomology`,
`SimplicialObjects.TensorHomologyZero`, `SimplicialObjects.TensorHomologyZeroNaturality`,
`SimplicialObjects.TensorHomologyZeroCoefficientMaps`,
`SimplicialObjects.TensorHomologyZeroConnected`, `SimplicialObjects.TensorHomologyZeroEmpty`,
`SimplicialObjects.TensorCoefficientSequences`, `SimplicialObjects.SingularHomologyZero`,
`SimplicialObjects.SingularHomologyZeroNaturality`,
`SimplicialObjects.SingularHomologyZeroCoefficientMaps` and `SimplicialObjects.HomologyZero`;
example modules have a separate root.

For the full reexport list, see the [public root](../SimplicialObjects.lean).

## Headline results

- **Integral all-simplex coordinates.**
  [`AlgebraicTopology.chainGroupIsoFinsupp`](../SimplicialObjects/ChainCoordinates.lean)
  identifies each degree of every simplicial set's chains with finitely supported
  integer functions on its simplices. The coefficient object is the universe-lifted
  integer module; the two summand laws compute lifted coefficients and unit basis
  chains. This is a degreewise module isomorphism, not a chain or natural isomorphism.
- **Path components and singular components.** For every topological space and continuous map,
  [`ZerothHomotopy.map`](../SimplicialObjects/PathComponents.lean) acts directly on path classes.
  `TopCat.zerothHomotopyFunctor` is naturally isomorphic, via Mathlib's singular-component
  equivalence, to `TopCat.toSSet ⋙ SSet.π₀Functor`. A
  [discrete two-point transposition](../SimplicialObjectsTest/PathComponents.lean) exchanges
  distinct components and illustrates the naturality square.
- **Augmented left décalage.** [`augmented X`](../SimplicialObjects/LeftDecalage.lean) has ordinary degree
  `P(X)ₙ = Xₙ₊₁` and augmentation target `X₀`. Its augmentation takes the
  new initial vertex: at degree zero `ε₀ = X.δ 1`, **not** `X.δ 0`.
- **Canonical extra degeneracy.** [`extraDegeneracy X`](../SimplicialObjects/LeftDecalage.lean) builds mathlib's
  `SimplicialObject.Augmented.ExtraDegeneracy (augmented X)` from the
  original zeroth degeneracies. All five defining equations, including the
  exceptional degree-zero face, hold. Mathlib then supplies `.section_`,
  `.splitEpi`, `.homotopy` and postcomposition `.map F`; these are not new
  implementations in this repository.
- **Functoriality and naturality.** [`functor C`](../SimplicialObjects/LeftDecalage.lean) makes the augmented
  construction functorial; [`projection X`](../SimplicialObjects/LeftDecalage.lean)
  is the natural ordinary simplicial `X.δ 0` projection, distinct in general
  from the augmentation. The section, higher extra-degeneracy components and
  projection have explicit naturality equations.

- **Finite-fiber transfers.** [`FiniteFiberTransfer`](../SimplicialObjects/FiniteFiberTransfer.lean)
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
  [`SSet.chainComplexTransfer_mapHomologicalComplex`](../SimplicialObjects/FiniteFiberTransfer.lean)
  proves compatibility of the all-simplex chain transfer with Mathlib's
  coefficient-comparison isomorphism for an additive functor `C ⥤ D` preserving
  coproducts indexed by types in the simplex universe. The source and target
  categories are preadditive and have those coproducts; only vertex fibers of
  the equifibered simplicial map need be finite.
  No preservation of homology or exactness is assumed. The two-sheet `ZMod 4`
  example independently computes coordinates `1 ⊗ 1`, nonzero by the left unitor,
  and pushforward two modulo four.

- **Normalized descent.** [`Normalization`](../SimplicialObjects/Normalization.lean)
  constructs maps between mathlib's normalized complexes for any morphism
  `f : X ⟶ Y` of simplicial objects in a preadditive category, given splittings
  `s` and `t`. The formula is `s.fromNondegComplex ≫ K(f) ≫ t.toNondegComplex`,
  where `K` is the alternating-face-map complex; `f` need not preserve the chosen
  nondegenerate summands. Its API comprises the projection equation,
  characterization of descent, identity and composition, the degreewise quotient
  property for elementary degeneracies, the explicit factor `s.fromNondegComplex.f n ≫ a`,
  and agreement with mathlib's simplicial-set normalized map. It also agrees with
  mathlib's `Split.nondegComplexFunctor` on morphisms compatible with the splittings,
  without an additional finite-coproduct assumption. For simplicial sets, the inverse
  normalization homotopy equivalence is natural on homology in every degree. The integral
  `Δ[1]` model has normalized groups `ℤ ⊞ ℤ` and `ℤ` in degrees zero and one,
  boundary `a ↦ (-a,a)`, and collapse to `Δ[0]` zero in degree one but nonzero in
  degree zero.
- **Normalized change of coefficient category.**
  [`SSet.normalizedChainComplexFunctorObjCompMapIso`](../SimplicialObjects/Normalization.lean)
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
  [`Normalization`](../SimplicialObjects/Normalization.lean) proves three further
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
  [`TensorCoefficients`](../SimplicialObjects/TensorCoefficients.lean) constructs
  `SSet.tensorNormalizedChainComplex` for every `A : Type a` with `[AddCommGroup A]`
  and `S : SSet.{w}`, using only the canonical `ℤ`-module structure.
  `SSet.tensorNormalizedChainIso` identifies this complex, with its independently
  defined alternating tensor boundary, with Mathlib's normalized chains with
  lifted coefficients. The coefficient, simplex and padding universes `a`, `w`, `p`
  are independent; no finiteness, flatness, field or nonemptiness hypothesis is needed.
- **Simplicial maps on integral tensor chains.**
  [`TensorMaps`](../SimplicialObjects/TensorMaps.lean) defines the integral degree map
  by `[s] ↦ [f(s)]` and tensors it with the coefficient identity. Degenerate image
  classes are zero; `f : S ⟶ T` is arbitrary in `SSet.{w}`.
  It also constructs whole chain maps and a functor using the existing normalized
  chain map and chain comparison. The component and naturality statements relate
  this construction to the independently specified tensor-degree maps and boundary.
  If `f` is a monomorphism, every tensor degree map is injective and the whole
  chain morphism is monic, for arbitrary `[AddCommGroup A]` and independent
  coefficient, simplex and padding universes. These results use coproduct monicity
  and the natural normalization retract, without a flatness hypothesis on `A`.
- **Natural tensor-chain comparison and cokernels.**
  [`SSet.tensorNormalizedChainNatIso`](../SimplicialObjects/TensorMaps.lean) bundles
  the original chain comparisons into a natural isomorphism from the fixed-`A`
  tensor-chain functor to normalized chains with coefficient object
  `ModuleCat.of ℤ (ULift.{max w p} A)`, in `ModuleCat.{max a w p} ℤ` chain complexes.
  Only `[AddCommGroup A]` is needed, with independent `a`, `w`, `p`.
  [`SSet.tensorNormalizedChainCokerNatIso`](../SimplicialObjects/TensorCokernels.lean)
  transports this comparison along Mathlib's arrow and cokernel functors on all
  simplicial arrows, not just monomorphisms. Its components agree with
  `cokernel.mapIso`, with forward and inverse projection formulas. The standard
  face `δ₁ : Δ[0] ⟶ Δ[1]` over `ZMod 4` has a nonzero omitted-vertex class in
  chain degree zero, detected using evaluation preserving cokernels; this is
  not a nonvanishing claim about homology.
- **Chain homotopies of integral tensor maps.**
  [`TensorHomotopies`](../SimplicialObjects/TensorHomotopies.lean) constructs a
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
- **Quasi-isomorphisms from simplicial homotopy inverses.**
  A simplicial map with a two-sided simplicial homotopy inverse induces a
  quasi-isomorphism of normalized chains. The coefficient category can be any
  preadditive category with coproducts and homology, without an abelian-category
  hypothesis. The original integral tensor chain map is therefore a
  quasi-isomorphism for every abelian coefficient group, with independent
  coefficient, simplex and padding universes. The standard interval augmentation
  illustrates both results over `ZMod 4`, although it identifies distinct vertices.
- **Extra-degenerate augmentations.**
  [`SSet.quasiIso_normalizedChainComplexMap_of_extraDegeneracy`](../SimplicialObjects/Normalization.lean)
  and [`SSet.quasiIso_tensorNormalizedChainComplexMap_of_extraDegeneracy`](../SimplicialObjects/TensorHomotopies.lean)
  apply these results directly to an augmented simplicial set `U` with Mathlib's
  `ExtraDegeneracy U`, using its stock section and combinatorial homotopy.
  The map is the original `U.hom` to the constant simplicial set on arbitrary
  `U.right`, not necessarily a terminal set. The generic coefficient-category
  scope and the tensor theorem's independent universes are unchanged. Examples
  use the stock extra degeneracy on every standard simplex and the existing
  Bool-target left décalage augmentation.

- **Change of abelian coefficients.**
  [`TensorCoefficientMaps`](../SimplicialObjects/TensorCoefficientMaps.lean) defines
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
  [`TensorCoefficientFunctor`](../SimplicialObjects/TensorCoefficientFunctor.lean) constructs
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

- **Finite exactness of the coefficient functor.**
  [`TensorCoefficientFunctor`](../SimplicialObjects/TensorCoefficientFunctor.lean) gives
  `CategoryTheory.Limits.PreservesFiniteLimits` and `PreservesFiniteColimits`
  instances for `SSet.tensorNormalizedChainComplexCoefficientFunctor.{a,w,p}`,
  with independent coefficient, simplex and padding universes and no additional
  assumptions. Evaluation identifies all three objects and both arrows of a
  mapped exact coefficient row with the existing tensor coefficient short complex.
  The existing short-exactness theorem and Mathlib's additive exact-functor
  criterion then give both preservation classes pointwise. The integer doubling
  and binary reduction sequence uses these instances through
  `ShortComplex.ShortExact.map_of_exact`; its point and interval rows retain the
  same whole complexes, both arrows, nonzero generators and signed boundary.
  This is categorical exactness of the chain-valued coefficient functor, not
  exactness after taking homology.

- **Exactness in abelian coefficients.**
  [`SSet.tensorNormalizedCoefficientMap_exact`](../SimplicialObjects/TensorCoefficientMaps.lean)
  sends any pair `g : A →+ B`, `h : B →+ C` with `Function.Exact g h` to an
  exact pair of the existing tensor-degree maps, for every simplicial set and
  every degree. The three coefficient groups are arbitrary abelian groups in
  independent universes, with no coefficient-flatness, finiteness, injectivity
  or surjectivity assumption. Mathlib's `Module.Flat.lTensor_exact` applies to
  the free first factor `S.nonDegenerate n →₀ ℤ`; the outer lifts use common
  padding `max a b c w p`. The integer doubling/reduction sequence specializes
  this result to the standard point and interval.
- **Coefficient endpoints and short exact sequences.**
  [`TensorCoefficientMaps`](../SimplicialObjects/TensorCoefficientMaps.lean) preserves
  injectivity and surjectivity in every tensor degree. In
  [`TensorCoefficientSequences`](../SimplicialObjects/TensorCoefficientSequences.lean),
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

- **Coefficient naturality of zeroth simplicial homology.**
  [`HomologyZero`](../SimplicialObjects/HomologyZero.lean) proves that Mathlib's
  `SSet.homology₀Iso` and its inverse commute with every coefficient morphism
  `a : R ⟶ R'`, for arbitrary `S : SSet.{w}` and coefficient objects `R R' : C`.
  Here `C : Type u` has `[Category.{v} C]`, `[HasCoproducts.{w} C]`,
  `[Preadditive C]` and `[CategoryWithHomology C]`, with independent `u`, `v`, `w`.
  The two squares compare `HomologicalComplex.homologyMap` in degree zero of
  `((SSet.chainComplexFunctor C).map a).app S` with the fixed-component map
  `Sigma.map (fun _ : SSet.π₀ S => a)`. The all-degree generator law
  `SSet.ιChainComplex_coefficient_naturality`, with its reassociated form, needs
  no `CategoryWithHomology` assumption. These results use Mathlib's simplicial
  homology API of Joël Riou and Andrew Yang and its categorical coproduct API,
  without tensor chains or normalization.
  `SimplicialObjectsTest.HomologyZeroPoint` evaluates the forward square on the
  standard point's integer vertex class and the inverse square on its
  coefficient-one component generator. The augmentation detects the nonzero
  integer class; the same map `ULift ℤ → ULift (ZMod 2)` kills two and preserves one.
  This concerns ordinary simplicial homology, distinct from the normalized tensor
  homology below; no singular, topological, relative or reduced comparison is asserted.

- **Degree-zero homology and simplicial components.**
  [`TensorHomologyZero`](../SimplicialObjects/TensorHomologyZero.lean) constructs
  `SSet.tensorNormalizedHomologyZeroIsoComponents` for every `A : Type a` with `[AddCommGroup A]`
  and every `S : SSet.{w}`: `H₀(SSet.tensorNormalizedChainComplex.{a,w,p} A S) ≅ ∐ (fun _ : SSet.π₀
  S => ModuleCat.of ℤ (ULift.{max w p} A))`. The coefficient object lies in `ModuleCat.{max a w p}
  ℤ`; its lift is distinct from the raw outer `ULift.{max a w p}` of the tensor groups. The
  universes `a`, `w`, `p` are independent, with no finiteness, flatness, field, basis or
  nonemptiness hypotheses. This is an `Iso` with hom, inverse and both inverse identities, composed
  from three existing factors: the tensor chain comparison on homology, Mathlib's normalization
  homotopy equivalence in the direction from normalized to all-simplex chains, and Mathlib's
  `S.homology₀Iso`.

- **Vertex classes and the signed edge boundary.** `ChainComplex.homologyπ₀`, from
  [`HomologyZero`](../SimplicialObjects/HomologyZero.lean), projects degree-zero chains to homology.
  With prefix
  `SSet.tensorNormalizedHomologyZeroIsoComponents`, `_hom_class` sends the class of every original
  `[v] ⊗ x` to `Sigma.ι _ (SSet.π₀.mk v) (ULift.up x)`, and `_inv_ι` recovers that class.
  `SSet.tensorNormalizedChainComplex_d_one_single` and
  `SSet.tensorNormalizedChainComplex_d_one_simplex` compute the raw boundary as face zero minus face
  one, including degenerate edges; `SSet.tensorNormalizedHomologyZeroClass_endpoints` equates their
  endpoint classes.

- **Naturality of the component isomorphism.**
  [`TensorHomologyZeroNaturality`](../SimplicialObjects/TensorHomologyZeroNaturality.lean) proves
  `SSet.tensorNormalizedHomologyZeroIsoComponents_hom_naturality` and its inverse square for every
  simplicial morphism, including maps with degenerate simplex images. The coproduct map is
  `Sigma.map' (SSet.mapπ₀ f)` with identity coefficients. Independently,
  [`TensorHomologyZeroCoefficientMaps`](../SimplicialObjects/TensorHomologyZeroCoefficientMaps.lean)
  proves `SSet.tensorNormalizedHomologyZeroIsoComponents_hom_coefficient_naturality` for every
  additive `g : A →+ B` and `SSet.tensorNormalizedHomologyZeroIsoComponents_hom_mixed_naturality`
  for simultaneous simplicial and coefficient change. For independent `a`, `b`, `w`, `p`, source
  padding is `max b p`, target padding is `max a p`, and the coefficient objects are `ModuleCat.of ℤ
  (ULift.{max w b p} A)` and `ModuleCat.of ℤ (ULift.{max w a p} B)` in `ModuleCat.{max a b w p} ℤ`.
  The mixed coproduct map reindexes by `SSet.mapπ₀` and sends `ULift.up x` to `ULift.up (g x)` on
  each summand. These coefficient and mixed squares use raw degree-zero generators, not the separate
  simplicial-naturality theorem; simplicial and coefficient maps also commute on homology and on the
  coproducts. The one-factor class-image laws
  `SSet.tensorNormalizedHomologyZeroMap_class` and
  `SSet.tensorNormalizedHomologyZeroCoefficientMap_class` compute these induced maps
  directly on vertex classes and are reused by product naturality.

- **Binary products in degree-zero normalized tensor homology.**
  [`TensorHomologyZeroProducts`](../SimplicialObjects/TensorHomologyZeroProducts.lean)
  constructs `SSet.tensorNormalizedHomologyZeroProductIso` for arbitrary abelian
  groups `A : Type a`, `B : Type b` and simplicial sets `K : SSet.{w}`, `L : SSet.{v}`.
  Its source is the algebraic integer tensor product of their original degree-zero
  tensor homology modules with independent paddings `pK`, `pL`. Its target is
  degree-zero tensor homology with coefficients `A ⊗[ℤ] B` of the categorical
  product of `(SSet.uliftFunctor.{v,w}).obj K` and
  `(SSet.uliftFunctor.{w,v}).obj L`, with padding `max pK pL`.
  No finiteness, flatness, connectedness or nonemptiness is required.
  The construction uses the component coproduct descriptions, Mathlib's
  tensor/direct-sum distribution, lifted coefficient equivalences and the
  component equivalence of a binary product.

  With prefix `SSet.tensorNormalizedHomologyZeroProductIso`, `_hom_class` sends
  a pure tensor of vertex classes with coefficients `x`, `y` to the paired vertex
  class with coefficient `x ⊗ₜ[ℤ] y`, and `_inv_class` recovers the source tensor.
  `SSet.tensorNormalizedHomologyZeroProduct_ext` determines a linear map to any
  independently-universed integer module from these tensors. The `_hom_unique`
  and `_inv_unique` statements characterize both comparison maps without an
  invertibility premise on the competing maps.

  [`TensorHomologyZeroProductNaturality`](../SimplicialObjects/TensorHomologyZeroProductNaturality.lean)
  gives all four squares: `_hom_naturality` and `_inv_naturality` for arbitrary
  simplicial maps in both factors, and `_hom_coefficient_naturality` and
  `_inv_coefficient_naturality` for arbitrary additive coefficient maps
  `A →+ A'`, `B →+ B'`. The latter use source paddings `max a' pK`, `max b' pL`
  and target paddings `max a pK`, `max b pL`, retaining all independent universes.
  The [discrete two-by-two example](../SimplicialObjectsTest/TensorHomologyZeroProducts.lean)
  separates the four nonzero integer vertex tensors and product classes, evaluates
  the comparison on all four, and computes the induced flip/collapse and
  coefficient-doubling/tripling maps.

- **Singular homology in degree zero and path components.**
  [`SingularHomologyZero`](../SimplicialObjects/SingularHomologyZero.lean) constructs
  `TopCat.tensorNormalizedHomologyZeroIsoPathComponents` for every topological space
  `X : TopCat.{w}` and abelian group `A : Type a`. Its source is degree-zero homology of
  `SSet.tensorNormalizedChainComplex.{a,w,p} A (TopCat.toSSet.obj X)`; its target is the
  coproduct of `ModuleCat.of ℤ (ULift.{max w p} A)` indexed by `ZerothHomotopy X`.
  The isomorphism composes the tensor comparison above with the singular-component
  equivalence. Its vertex formula sends each singular vertex tensor to the summand
  of the corresponding point's path component. The space and coefficient universes
  remain independent, with no local path connectedness or nonemptiness hypothesis.
  [`SingularHomologyZeroNaturality`](../SimplicialObjects/SingularHomologyZeroNaturality.lean)
  and [`SingularHomologyZeroCoefficientMaps`](../SimplicialObjects/SingularHomologyZeroCoefficientMaps.lean)
  give both orientations of the continuous, balanced coefficient and mixed squares,
  using the direct map on path components. A
  [discrete two-point example](../SimplicialObjectsTest/SingularHomologyZero.lean) separates
  both nonzero vertex classes for every padding universe and evaluates these maps.

- **Component fold and connected coefficients.**
  [`TensorHomologyZeroConnected`](../SimplicialObjects/TensorHomologyZeroConnected.lean) identifies the
  component comparison followed by `Sigma.desc (fun _ => 𝟙 _)` with collapse to `Δ[0]` followed by
  terminal coefficient evaluation, for every source, including the empty one.
  `SSet.tensorNormalizedHomologyZeroIsoComponents_hom_fold_to_terminal` holds for any map
  to any terminal simplicial set;
  `SSet.tensorNormalizedHomologyZeroIsoComponents_hom_fold_normalization` expresses the same
  fold through the tensor comparison, normalized-chain
  inclusion and homology augmentation. For `[S.IsConnected]`,
  `SSet.tensorNormalizedHomologyZeroIsoCoefficientOfIsConnected` is an isomorphism to `ModuleCat.of
  ℤ (ULift.{max w p} A)`, with vertex and inverse class formulas; on terminal sets it agrees with
  `SSet.tensorNormalizedHomologyZeroIsoCoefficient`. Only invertibility of the fold needs
  connectedness.

- **The empty standard boundary.**
  [`TensorHomologyZeroEmpty`](../SimplicialObjects/TensorHomologyZeroEmpty.lean) proves
  `SSet.tensorNormalizedHomologyZero_boundary_zero_isZero`: the degree-zero tensor homology of
  `(∂Δ[0] : SSet.{w})` is zero for arbitrary abelian coefficients and independent `a`, `w`, `p`,
  using its empty component coproduct.

- **Homology of terminal simplicial sets.**
  [`PointHomology`](../SimplicialObjects/PointHomology.lean) gives
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

See the [left décalage guide](../docs/LeftDecalage.md) for indexing, exact
equations, construction and example clients. The homotopy is
**combinatorial**; no geometric realization, general-relative contraction,
long exact sequence, spectra, K-theory theorem or source-coverage claim follows here.

Here `SSet.π₀ S` means simplicial components, the quotient of vertices by edge
zigzags, not components of a topological realization. The component and
point-homology statements concern **simplicial normalized chains** and
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

The [interval examples](../SimplicialObjectsTest/TensorCoefficients.lean) compute
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

`tensorNormalizedChainNatIso A` has these same pointwise chain comparisons as
components. Its `_app`, `_hom_app` and `_inv_app` simp laws lead to the existing
generator and coordinate API; naturality and reassociated naturality are the
standard natural-transformation laws. Import `SimplicialObjects.TensorCokernels`
for `tensorNormalizedChainCokerNatIso A` on
`(tensorNormalizedChainComplexFunctor A).mapArrow ⋙ Limits.coker _` and the analogous
normalized-chain functor. The component theorem identifies `cokernel.mapIso` of
the original comparisons. Both projection laws compute the cokernel comparison
without unfolding it, and stock naturality applies to every commuting square.
These constructions reuse Mathlib's `NatIso.ofComponents`, `Functor.mapArrowFunctor`
and `Functor.isoWhiskerRight`, rather than a separate transport or quotient construction.

## All-simplex integral coordinates

Import `SimplicialObjects.ChainCoordinates`; its coordinate declarations are in
`AlgebraicTopology`. For `X : SSet.{u}` and `n : ℕ`, the original coefficient object is
`integerCoefficients = (ModuleCat.uliftFunctor.{u} ℤ).obj (ModuleCat.of ℤ ℤ)`.
It is a `ModuleCat.{u} ℤ` object, with the original given module structure on
`ULift.{u} ℤ`, not a replacement coefficient model. The degreewise isomorphism is

```text
chainGroupIsoFinsupp X n :
  (X.chainComplex integerCoefficients).X n ≅ ModuleCat.of ℤ (X _⦋n⦌ →₀ ℤ)
```

Its construction uses the chain coproduct cofan, Mathlib's module-category
Finsupp cofan, `Finsupp.mapRange.linearEquiv` and `ULift.moduleEquiv`.
The morphism-level law `ι_chainGroupIsoFinsupp_hom` says

```text
X.ιChainComplex (R := integerCoefficients) x ≫ (chainGroupIsoFinsupp X n).hom
  = ModuleCat.ofHom ((Finsupp.lsingle x).comp ULift.moduleEquiv.toLinearMap).
```

Thus a lifted integer `ULift.up z` in the `x` summand has coordinate
`Finsupp.single x z`. The second summand law,
`chainGroupIsoFinsupp_hom_ι`, computes the unit coefficient as
`Finsupp.single x 1`. These are integral coordinates on **all** simplices,
including degenerate simplices: they are not normalized coordinates and do not
construct a chain isomorphism or a natural isomorphism.

The [standard-point example](../SimplicialObjectsTest/ChainCoordinates.lean)
uses `(Δ[0] : SSet.{0})`, its vertex
`SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)` and this same coefficient object.
The chain with coefficient `ULift.up (1 : ℤ)` is nonzero, since its coordinate
is the unit basis function. This is a nonzero chain calculation, not an
additional homology comparison.

SphereTopology versions defining these four coordinates independently cannot
co-import with this home; use matching versions reexporting this home.

## Credits and license

Authors: Formal Frontier Agents. This is AI-assisted mathematical formalization, using Mathlib's
simplicial, Dold–Kan normalization and homology constructions, notably Joël Riou's normalization and
degree-zero component formalization, and this library's integral tensor comparison and terminal
coefficient API. Formal Frontier Agents, including Prism, wrote the integral all-simplex coordinates,
using Mathlib's module-category colimits, lifted module functor and Finsupp linear equivalences.
May's *A Concise Course in Algebraic Topology*, revised edition, provides the mathematical background cited above; no source-wide formalization is claimed. Existing contributor
and source credit is retained in [CONTRIBUTORS.md](../CONTRIBUTORS.md). Licensed under
[Apache-2.0](../LICENSE); Mathlib retains its own license and authorship.
