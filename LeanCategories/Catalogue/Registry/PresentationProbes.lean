/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Presentation
public meta import LeanCategories.Catalogue.Registry.Presentation
public import LeanCategories.Catalogue.Semantics.ConstructorRegistration

/-!
# Presentation probes: product sources, the presentation's 1-cells, and the pullback kind

The smallest states that decide issue #99's remaining revised-acceptance bullets.

* `id99.oneCellPresentation`: a two-edge specimen's presentation has exactly its two registered
  structural rows as 1-cells, and the derived constructor edges are not registered (`:rfl` facts).
* `id99.twoInputEdgeNotDerived`: `edgesFrom` derives one edge at a unary constructor node and *no*
  edge at a two-input node -- the exact behaviour of `Semantic.lean:1702-1712`, which matches on
  `#[.category inner]` only.
* `id99.registryProductSources` / `id99.registryReindexingIsoComma`: on the real registry, the
  constructor rows whose source is a finite product, and the classification of every classifier's
  reindexing.
-/

@[expose] public section

namespace CasCatalogue.PresentationProbes

open CasCatalogue

/-- A unary and a two-input constructor row, each with a functorial action, and one structural
functor `a → b`: the smallest state in which a derived unary edge and the absence of a derived
two-input edge can both be observed. -/
def constructorSpecimen : SemanticState :=
  { constructors := #[
      { id := ⟨"ctor.probe.unary"⟩, signature := #[ConstructorArgKind.category]
        semantics := ``sameEndpoint, functorialAction := some ``sameEndpoint },
      { id := ⟨"ctor.probe.binary"⟩, signature := #[ConstructorArgKind.category,
          ConstructorArgKind.category]
        semantics := ``sameEndpoint, functorialAction := some ``sameEndpoint }]
    functors := #[
      { id := ⟨"fun.probe.ab"⟩, source := .atom ⟨"cat.a"⟩, target := .atom ⟨"cat.b"⟩
        declaration := ``sameEndpoint, realization := ``sameEndpoint
        expression := .atomic ⟨"fun.probe.ab"⟩, structural := true }] }

/-! The four checks below are evaluated at elaboration, not proved by `native_decide`:
`SemanticState.edgesFrom` is a `partial def` (`Registry/Semantic.lean:1698`), so neither kernel
`decide` nor `rfl` can reduce it, and `native_decide` would carry `Lean.ofReduceBool`, which the
kernel-axiom audit rejects (`Tools/AxiomAudit.lean`, permitted `[propext, Classical.choice,
Quot.sound]`). A wrong value fails the build, and no axiom enters the environment. -/

/-- The two-row specimen's presentation: one generating 1-cell (the structural row), no 2-cell. -/
def id99.oneCellPresentationCheck : Bool :=
  constructorSpecimen.presentation.oneCells.size == 1 &&
    constructorSpecimen.presentation.twoCells.size == 0

/-- The unary constructor node carries the derived edge `unary(a) → unary(b)`. -/
def id99.unaryEdgeDerivedCheck : Bool :=
  (constructorSpecimen.edgesFrom
    (.construct ⟨"ctor.probe.unary"⟩ #[ConstructorArg.category (.atom ⟨"cat.a"⟩)])).size == 1

/-- The two-input node carries none: `edgesFrom` matches the single-argument pattern only, so a
generating 1-cell out of a finite-product source gets no constructor-induced edges. -/
def id99.twoInputEdgeNotDerivedCheck : Bool :=
  (constructorSpecimen.edgesFrom
    (.construct ⟨"ctor.probe.binary"⟩ #[ConstructorArg.category (.atom ⟨"cat.a"⟩),
      ConstructorArg.category (.atom ⟨"cat.b"⟩)])).size == 0

/-- Only the two-input row counts as a product-source constructor. -/
def id99.productSourceRowsCheck : Bool :=
  constructorSpecimen.productSourceConstructors.map (·.id.raw) == #["ctor.probe.binary"]

open Lean Elab Command in
run_cmd
  liftTermElabM do
    let checks : List (Name × String) :=
      [(``id99.oneCellPresentationCheck, "the specimen's presentation is not one 1-cell"),
       (``id99.unaryEdgeDerivedCheck, "the unary constructor node derives no edge"),
       (``id99.twoInputEdgeNotDerivedCheck, "the two-input constructor node derives an edge"),
       (``id99.productSourceRowsCheck, "the product-source rows are not exactly the binary row")]
    for (name, message) in checks do
      let e ← Lean.Elab.Term.elabTerm (← `($(mkIdent name))) (some (mkConst ``Bool))
      let value ← unsafe Lean.Meta.evalExpr Bool (mkConst ``Bool) e
      unless value do
        throwError "issue #99 probe {name}: {message}"

open Lean Meta in
run_meta do
  let state ← semanticState
  -- The registry's product-source constructor rows, and the classification of every classifier's
  -- reindexing. Both are facts about the registered rows, checked at registration time.
  let products := state.productSourceConstructors
  unless products.size == 1 && products[0]?.map (·.id) == some ConstructorId.functorCategory do
    throwError "expected exactly the functor-category constructor as a product source, got \
      {products.map (·.id.raw)}"
  let pullbacks := state.reindexingPullbacks
  unless pullbacks.size > 0 do
    throwError "the registry registers no classifier, so no reindexing pullback is classified"
  for row in pullbacks do
    unless row.kind == .isoComma do
      throwError "reindexing of {row.classifier.raw} is not classified as the iso-comma"
    unless row.construction == ``LeanCategories.Classifier.reindex do
      throwError "reindexing of {row.classifier.raw} names another construction"

/-! ### A 1-cell with a finite-product source -/

/-- The smallest state in which a generating 1-cell has a product source: one structural functor
row out of `P × Q`, written as the two-argument construct node. -/
def productSourceSpecimen : SemanticState where
  functors := #[
    { id := ⟨"fun.prod"⟩
      source := .construct ⟨"ctor.prod"⟩
        #[.category (.atom ⟨"cat.p"⟩), .category (.atom ⟨"cat.q"⟩)]
      target := .atom ⟨"cat.r"⟩
      declaration := ``sameEndpoint, realization := ``sameEndpoint
      expression := .atomic ⟨"fun.prod"⟩, structural := true }]

/-- A generating 1-cell may have a finite-product source: the row is one of the presentation's
1-cells. -/
def id99.productSourceIsOneCellCheck : Bool :=
  (productSourceSpecimen.structuralEdges).size == 1

/-- The search treats the product-source vertex as a vertex: the route out of `P × Q` is found. -/
def id99.productSourceRouteCheck : Bool :=
  (productSourceSpecimen.routes
    (.construct ⟨"ctor.prod"⟩ #[.category (.atom ⟨"cat.p"⟩), .category (.atom ⟨"cat.q"⟩)])
    (.atom ⟨"cat.r"⟩) 2).any fun route => route.refs.size == 1

open Lean Elab Command in
run_cmd
  liftTermElabM do
    let checks : List (Name × String) :=
      [(``id99.productSourceIsOneCellCheck,
        "the product-source row is not a generating 1-cell of the presentation"),
       (``id99.productSourceRouteCheck,
        "the search did not find the route out of the product-source vertex")]
    for (name, message) in checks do
      let e ← Lean.Elab.Term.elabTerm (← `($(mkIdent name))) (some (mkConst ``Bool))
      let value ← unsafe Lean.Meta.evalExpr Bool (mkConst ``Bool) e
      unless value do
        throwError "issue #99 probe {name}: {message}"

end CasCatalogue.PresentationProbes
