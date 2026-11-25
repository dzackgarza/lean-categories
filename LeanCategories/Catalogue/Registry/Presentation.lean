/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.RouteDiscovery

/-!
# The registry's presentation: generating 1-cells, product sources, and pullback classification

The three remaining bullets of issue #99's revised acceptance, as corrected by the later comments
(6474191513, 6476290045).

**The 2-computad.** `EdgeRef` is a generating 1-cell and `Route` a composite of them
(`Route.steps`, `Route.refs`); `EdgeRef.exists_kind` proves that every generating 1-cell is one of
exactly three forms -- a registered structural functor row, a classifier's forgetful functor, or a
functorial-constructor image of one of those -- and `ComputadPresentation` bundles the three levels
from a state. `CellEntry` is the generating 2-cell, and `ComparisonWitness`
(`RouteDiscovery.lean:81`) is what keeps it as data rather than as a relation of a quotient.

**Finite-product sources.** The issue worries that a quiver admits only one-input operations. It
does not apply here in the way the issue's earlier comment assumed and does apply in another way:
`ConstructorEntry.signature` can be `#[.category, .category]` (`ConstructorRegistration.lean:113`,
`ConstructorId.functorCategory`), so a two-input category constructor *is* expressible, but
`SemanticState.edgesFrom` derives `c(U) : c(A) → c(B)` only for the single-argument pattern
`#[.category inner]` (`Semantic.lean:1701-1712`). A generating 1-cell out of a two-input node
therefore carries no constructor-induced edges, and `ConstructorEntry.hasMultipleCategoryArguments`
records which rows are of that shape. The probe
`PresentationProbes.id99.twoInputEdgeNotDerived` measures the difference.

**Pullbacks: strict or iso-comma.** The registry's only pullback-shaped construction is a
classifier's reindexing `F^* A`, and it is *not* a strict 1-categorical pullback:
`Classifier.reindex` builds `Cat.of (CategoricalPullback F A.forget)`
(`CategoryTheory/OneCat/CategoricalPullback.lean:47-55`),
whose objects are triples `(c, a, F c ≅ A.forget a)`
(`Mathlib/CategoryTheory/Limits/Shapes/Pullback/Categorical/Basic.lean:74-88`), i.e. the iso-comma
of the cospan. `PullbackKind` records the classification, and every registered classifier's
reindexing is classified `isoComma` (`reindexingPullbacks_isoComma`). Consequences the issue asks
for are therefore not available at this pin, and are recorded here rather than assumed:

* isofibration evidence is *not* carried and *not* required: a strict pullback of categories exists
  whatever the legs are, and an isofibration leg is only a sufficient condition for the strict
  pullback to agree with the iso-comma (issue comment 6476290045);
* the agreement itself is not proved, and cannot be stated at this pin: Mathlib here has no
  `IsIsoFibration`, `IsoFibration` or `IsoComma` declaration (searched: `rg 'IsoFibration'`,
  `rg 'IsoComma'` over `Mathlib/`, no hits), and the repository has no strict `Cat` pullback
  (`rg 'IsStrictPullback'`, no hits);
* a composite's classification is not derived from its factors' by closure, which the issue records
  as merely sufficient; `reindexingPullbacks` classifies each row directly.
-/

@[expose] public section

namespace CasCatalogue

/-! ## Generating 1-cells and the presentation -/

/-- The three forms a generating 1-cell takes. -/
inductive OneCellKind
  /-- A registered structural functor row. -/
  | structuralFunctor (id : FunctorId)
  /-- The forgetful functor `total(c) → host(c)` of a registered classifier. -/
  | classifierForget (id : ClassifierId)
  /-- A functorial-constructor image of a generating 1-cell. -/
  | constructorImage (constructor : ConstructorId)
  deriving DecidableEq, Repr, Inhabited

/-- The form of a generating 1-cell. -/
def EdgeRef.kind : EdgeRef → OneCellKind
  | .functor id => .structuralFunctor id
  | .classifierForget id => .classifierForget id
  | .constructMap constructor _ => .constructorImage constructor

/-- Every generating 1-cell is one of the three forms: the registry's 1-dimensional presentation is
exactly these rows, with no fourth kind of edge. -/
theorem EdgeRef.exists_kind (ref : EdgeRef) :
    (∃ id : FunctorId, ref = .functor id) ∨
      (∃ id : ClassifierId, ref = .classifierForget id) ∨
        (∃ (constructor : ConstructorId) (inner : EdgeRef),
          ref = .constructMap constructor inner) := by
  cases ref with
  | functor id => exact Or.inl ⟨id, rfl⟩
  | classifierForget id => exact Or.inr (Or.inl ⟨id, rfl⟩)
  | constructMap constructor inner => exact Or.inr (Or.inr ⟨constructor, inner, rfl⟩)

/-- The three levels of the registry's presentation, extracted from a state: the category
expressions that appear as vertices, the generating 1-cells, and the generating 2-cells. -/
structure ComputadPresentation where
  /-- The registered categories and opaque categories, as the 0-cells the rows name. -/
  zeroCells : Array CategoryExpr
  /-- The generating 1-cells: structurally registered functor rows and classifier forgettings. -/
  oneCells : Array StructuralEdge
  /-- The generating 2-cells: the registered cell rows. -/
  twoCells : Array CellEntry

/-- The presentation of a state. Constructor-induced edges are *derived* from these 1-cells at each
construct node (`Semantic.lean:1698-1713`), not registered: that is why they are not listed here. -/
def SemanticState.presentation (state : SemanticState) : ComputadPresentation :=
  { zeroCells := state.categories.map (·.expression) ++
      state.opaqueCategories.map fun entry => CategoryExpr.opaque entry.id
    oneCells := state.structuralEdges
    twoCells := state.cells }

theorem presentation_oneCells (state : SemanticState) :
    state.presentation.oneCells = state.structuralEdges := rfl

theorem presentation_twoCells (state : SemanticState) :
    state.presentation.twoCells = state.cells := rfl

/-- A route is a composite of generating 1-cells: its steps are the generating edges and its labels
are the generating 1-cells themselves. -/
theorem Route.steps_are_oneCells (route : Route) :
    route.steps.map (·.ref) = route.refs := rfl

/-! ## Finite-product sources -/

/-- A constructor row with more than one category argument: a generating 1-cell out of such a node
has a finite-product source, not a single category. -/
def ConstructorEntry.hasMultipleCategoryArguments (entry : ConstructorEntry) : Bool :=
  (entry.signature.filter (· == .category)).size > 1

/-- The rows of a state whose source would be a finite product. -/
def SemanticState.productSourceConstructors (state : SemanticState) : Array ConstructorEntry :=
  state.constructors.filter (·.hasMultipleCategoryArguments)

/-! ## Pullback classification -/

/-- How a registered pullback-shaped construction is classified. The kind is data: the two
constructions are not interchangeable, and the issue records that a strict pullback exists whatever
the legs are while an isofibration is only a sufficient condition for the two to agree. -/
inductive PullbackKind
  /-- The strict (1-categorical) pullback: objects are pairs with `F c = A a` on the nose. -/
  | strict
  /-- The iso-comma (pseudo-pullback): objects are triples `(c, a, F c ≅ A a)`. -/
  | isoComma
  deriving DecidableEq, Repr, Inhabited

/-- The pullback a classifier reindexing takes, classified with the construction it uses. -/
structure ReindexingPullback where
  classifier : ClassifierId
  kind : PullbackKind
  /-- The Lean construction the row is built from. -/
  construction : Lean.Name

/-- Every registered classifier's reindexing, classified directly from its construction: `reindex`
builds `Cat.of (CategoricalPullback F A.forget)`, whose objects carry an isomorphism
`F.obj fst ≅ G.obj snd`, so the construction is the iso-comma and not the strict pullback. -/
def SemanticState.reindexingPullbacks (state : SemanticState) : Array ReindexingPullback :=
  state.classifiers.map fun entry =>
    { classifier := entry.id, kind := .isoComma
      construction := ``LeanCategories.Classifier.reindex }

/-- Every classifier row's reindexing is an iso-comma: the classification is not a convention that a
later row could contradict, it is the construction's kind. -/
theorem reindexingPullbacks_isoComma (state : SemanticState) {row : ReindexingPullback}
    (hmem : row ∈ state.reindexingPullbacks) : row.kind = .isoComma := by
  rcases Array.mem_map.mp hmem with ⟨entry, _, heq⟩
  exact (congrArg ReindexingPullback.kind heq).symm

/-- The two kinds are different data, so a row cannot be read as either by default. -/
theorem pullbackKind_strict_ne_isoComma : PullbackKind.strict ≠ PullbackKind.isoComma := by
  decide

end CasCatalogue
