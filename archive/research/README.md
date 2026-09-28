# Lean sources migrated from `dzackgarza/research`

Migrated 2026-09-28 from `dzackgarza/research` at `4754e93`. Nothing under `archive/` is part
of the `LeanCategories` library or its build; the files are kept verbatim as provenance.

## Ported into the library

| Research source | Library owner | Change |
| --- | --- | --- |
| `formalization/coble-enriques/NodeCriteria.lean` | `LeanCategories/AlgebraicGeometry/HessianSingular.lean` | generalized from 3 variables to any finite `σ`; the rank bound is `≤ |σ| - 1` and needs only the vanishing of the partials |
| `computations/scripts/sterk-enriques-cusps/lean/Atoms.lean`, §§ Doubling, DiscriminantGaussSum, MilgramSteps (F1.15, F1.16) | `LeanCategories/Algebra/QuadraticGaussSum.lean` | the modulus theorem `|G(q)|² = |A|` for any finite abelian `A`, value group `T` and character `ψ : T → S¹`; three redundant hypotheses dropped |
| `Atoms.lean` § Indecomposable (V1) | `LeanCategories/Algebra/MatrixIndecomposable.lean` | new: decomposable ⇔ the support graph is not preconnected |
| `Atoms.lean` § PadicSemigroup (Pa1) | `LeanCategories/Modules/Quadratic/Valued/IsometryClasses.lean` | generalized to `IsometryClass R W`, isomorphism classes of `QuadModuleCat R W`, a commutative monoid under orthogonal sum; `qu(ℤ_p)` is `finiteFreeClasses` at `R = W = ℤ_p` |
| `Atoms.lean` §§ LorentzCone, LorentzConvexity (Lo1, Lo10) | `LeanCategories/Topology/LorentzCone.lean` | unchanged |
| `Atoms.lean` §§ AnalyticSets, Normality, DimensionStratification (AF10, AF14–AF19) | `LeanCategories/Analytic/LocalModel.lean` | unchanged |

## Superseded by existing declarations (not ported)

| `Atoms.lean` declaration | Existing owner |
| --- | --- |
| `orthogonalGroup` (F1.13) | `LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.OrthogonalGroup` |
| `quadraticOrthogonalGroup` (F2.14) | `LeanCategories.Modules.Quadratic.Valued.OrthogonalGroup` |
| `divisorIdeal`, `HasDivisorOne` (F1.14) | `LeanCategories.Lattices.Valued.divisibility` (`= ⊤` for divisor one) |
| `DeckTransformation`, `IsInvolution` (E14) | `LeanCategories.Topology.deckGroup`; an involution is an element with `d * d = 1` |
| `codimOnePoints`, `WeilDivisor` (E15) | `LeanCategories.Schemes.WeilDivisor` over `PrimeDivisor` (codimension via `Order.coheight`, as in the source) |
| `LeanCategoryDslSpike/AristotleFinitePairNumbering.lean` | Mathlib `finProdFinEquiv` composed with `Equiv.prodCongr` |

## Archived here

- `lean_category_dsl_spike/`: the category-DSL proof of concept (Lean `v4.32.0`, its own Lake
  project, not built here). It is prior art for `cc-resolve`: a persistent environment extension
  enumerating functor edges, the home category of an object read off its type head, and path
  application. Its `prefer` rule selects a path by priority, which CC-RESOLVE forbids (ambiguity
  is an error), and its `Std` layer re-declares categories Mathlib owns; neither is ported.
- `algebraic-geometry/AdjointRootData.lean`: roots relative to a diagonalizable subgroup as the
  nonzero weights of a restricted adjoint representation. It imports
  `LeanCategories.AlgebraicGeometry.DiagonalizableWeightData`, which exists in no revision of
  this repository, so it never built. The mathematics is formalized in TauCeti
  (`TauCeti/Algebra/AlgebraicGroup/DiagonalizableGroup/Weight.lean`,
  `.../Tangent/RootSpace.lean`, over `Comodule` and `GroupLike`) on Lean `v4.35.0-rc3`; see
  COMPLAINTS ("Comodules, weights and roots of affine group schemes").

## Left in `dzackgarza/research`

- `formalization/coble-enriques/IsotropicPlanes.lean`: statements only, every proof `sorry`,
  and both statements false as written (research's own README; corrected mathematics in its
  `notes/topics/isotropic-vector-orbits/`). It is a research record, not library content.
