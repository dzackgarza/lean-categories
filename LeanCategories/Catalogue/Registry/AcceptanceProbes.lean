/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.EnumerationCompleteness
public import LeanCategories.Catalogue.Registry.ComparisonProbes
public import LeanCategories.Catalogue.Registry.PresentationProbes

/-!
# Acceptance probes for issue #99

The smallest kernel-checked inputs that settle the two items this unit's own modules decide, with
the other items' probes in the imported files:

* item 1 — a generating step labelled by a functorial constructor keeps that exact label in
  `Route.refs` (`id99.routeLabelsRetained`, kernel `decide`);
* item 3 — the depth-bounded enumeration of `EnumerationCompleteness` contains every continuation of
  the complete two-vertex graph up to the fuel (`id99.enumerationComplete`,
  `id99.walkEnumerated`, kernel `decide`);
* items 2 and 4 and the revised-acceptance bullets — `ComparisonProbes` and `PresentationProbes`,
  imported above, run at elaboration.
-/

@[expose] public section

namespace CasCatalogue.AcceptanceProbes

open CasCatalogue

/-- One generating 1-cell: the constructor image `Arr(fun.ab)` of a structural edge. -/
def mapEdge : StructuralEdge where
  source := .construct ⟨"ctor.arr"⟩ #[ConstructorArg.category (.atom ⟨"cat.a"⟩)]
  target := .construct ⟨"ctor.arr"⟩ #[ConstructorArg.category (.atom ⟨"cat.b"⟩)]
  expression := .constructMap ⟨"ctor.arr"⟩ (.atomic ⟨"fun.ab"⟩)
  ref := .constructMap ⟨"ctor.arr"⟩ (.functor ⟨"fun.ab"⟩)

/-- The one-step route along it. -/
def mapRoute : Route where
  source := mapEdge.source
  target := mapEdge.target
  steps := #[mapEdge]

/-- Item 1: the route keeps the constructor-image label, not a name for the composite. -/
theorem id99.routeLabelsRetained :
    mapRoute.refs = #[EdgeRef.constructMap ⟨"ctor.arr"⟩ (EdgeRef.functor ⟨"fun.ab"⟩)] := by
  simp [Route.refs, mapRoute, mapEdge]

/-- Item 3: over the complete two-vertex graph, the continuations of length at most `2` are exactly
`[], [0], [1], [0,0], [0,1], [1,0], [1,1]`. -/
theorem id99.enumerationComplete :
    (RouteDiscovery.boundedWalks (fun _ : Fin 2 => [0, 1]) 2 0).length = 7 := by
  decide

/-- Item 3: a specific length-2 continuation is among them. -/
theorem id99.walkEnumerated :
    ([1, 0] : List (Fin 2)) ∈ RouteDiscovery.boundedWalks (fun _ : Fin 2 => [0, 1]) 2 0 := by
  decide

/-! ### The enumeration finds a chain, and respects its fuel -/

/-- Two structural edges `a → b → c`: the smallest state with a two-edge route. -/
def chainSpecimen : SemanticState where
  categories := #[]
  functors := #[
    { id := ⟨"fun.ab"⟩, source := .atom ⟨"cat.a"⟩, target := .atom ⟨"cat.b"⟩
      declaration := ``sameEndpoint, realization := ``sameEndpoint
      expression := .atomic ⟨"fun.ab"⟩, structural := true },
    { id := ⟨"fun.bc"⟩, source := .atom ⟨"cat.b"⟩, target := .atom ⟨"cat.c"⟩
      declaration := ``sameEndpoint, realization := ``sameEndpoint
      expression := .atomic ⟨"fun.bc"⟩, structural := true }]

/-- `SemanticState.routes` is a plain `def` built on the structurally recursive `routeSteps`, and at
fuel `2` it returns the two-edge route `a → b → c`: the completeness theorem's conclusion on the
smallest instance. -/
def id99.searchFindsChainCheck : Bool :=
  (chainSpecimen.routes (.atom ⟨"cat.a"⟩) (.atom ⟨"cat.c"⟩) 2).any fun route =>
    route.steps.size == 2

/-- At fuel `1` the same pair yields no route of length two: the fuel is a real bound, and
`routes_steps_le` says nothing longer can appear whatever the fuel. -/
def id99.searchRespectsFuelCheck : Bool :=
  !((chainSpecimen.routes (.atom ⟨"cat.a"⟩) (.atom ⟨"cat.c"⟩) 1).any fun route =>
    route.steps.size == 2)

open Lean Elab Command in
run_cmd
  liftTermElabM do
    let checks : List (Name × String) :=
      [(``id99.searchFindsChainCheck, "the search did not return the two-edge route a → b → c"),
       (``id99.searchRespectsFuelCheck, "the search returned a two-edge route within fuel 1")]
    for (name, message) in checks do
      let e ← Lean.Elab.Term.elabTerm (← `($(mkIdent name))) (some (mkConst ``Bool))
      let value ← unsafe Lean.Meta.evalExpr Bool (mkConst ``Bool) e
      unless value do
        throwError "issue #99 probe {name}: {message}"

/-! ### The rewritten search against the pre-rewrite algorithm -/

/-- The pre-rewrite algorithm, transcribed from the former `partial def SemanticState.routes`:
stop at the target, else recurse through `fuel - 1` with an explicit subscript accumulator. Kept
only to compare against the total `SemanticState.routeSteps`. -/
partial def legacyRouteSteps (state : SemanticState) (target : CategoryExpr)
    (current : CategoryExpr) (visited : List CategoryExpr) (fuel : Nat) :
    Array (Array StructuralEdge) :=
  if current.syntacticEq target then #[#[]]
  else if fuel = 0 then #[]
  else
    (state.edgesFrom current).foldl (init := #[]) fun acc edge =>
      if !(visited.any (·.syntacticEq edge.target)) then
        acc ++ (legacyRouteSteps state target edge.target (edge.target :: visited)
          (fuel - 1)).map (#[edge] ++ ·)
      else acc

/-- The pre-rewrite search, packaged as routes. -/
def legacyRoutes (state : SemanticState) (source target : CategoryExpr)
    (fuel : Nat := 32) : Array Route :=
  (legacyRouteSteps state target source [source] fuel).map fun steps => { source, target, steps }

/-- A cyclic three-vertex graph: it exercises the target short-circuit, the pruning gate and several
competing routes at once. -/
def rewriteSpecimen : SemanticState where
  functors := #[
    { id := ⟨"fun.ab"⟩, source := .atom ⟨"cat.a"⟩, target := .atom ⟨"cat.b"⟩
      declaration := ``sameEndpoint, realization := ``sameEndpoint
      expression := .atomic ⟨"fun.ab"⟩, structural := true },
    { id := ⟨"fun.ba"⟩, source := .atom ⟨"cat.b"⟩, target := .atom ⟨"cat.a"⟩
      declaration := ``sameEndpoint, realization := ``sameEndpoint
      expression := .atomic ⟨"fun.ba"⟩, structural := true },
    { id := ⟨"fun.bc"⟩, source := .atom ⟨"cat.b"⟩, target := .atom ⟨"cat.c"⟩
      declaration := ``sameEndpoint, realization := ``sameEndpoint
      expression := .atomic ⟨"fun.bc"⟩, structural := true },
    { id := ⟨"fun.ac"⟩, source := .atom ⟨"cat.a"⟩, target := .atom ⟨"cat.c"⟩
      declaration := ``sameEndpoint, realization := ``sameEndpoint
      expression := .atomic ⟨"fun.ac"⟩, structural := true }]

/-- The routes a search returns, rendered by their edge labels: comparable without an equality on
`Route`. -/
def routeKeys (routes : Array Route) : List (List String) :=
  routes.toList.map fun route => route.refs.toList.map EdgeRef.label

/-- The rewrite preserves the search's answers: over the cyclic specimen, the new `routes` and the
pre-rewrite algorithm return the same routes, in the same order, for every pair and fuel here. -/
def id99.rewritePreservesSearchCheck : Bool :=
  let pairs : List (CategoryExpr × CategoryExpr) :=
    [(.atom ⟨"cat.a"⟩, .atom ⟨"cat.c"⟩), (.atom ⟨"cat.a"⟩, .atom ⟨"cat.a"⟩),
      (.atom ⟨"cat.b"⟩, .atom ⟨"cat.c"⟩), (.atom ⟨"cat.c"⟩, .atom ⟨"cat.a"⟩)]
  let fuels : List Nat := [0, 1, 2, 3, 5]
  pairs.all fun (source, target) =>
    fuels.all fun fuel =>
      routeKeys (rewriteSpecimen.routes source target fuel) ==
        routeKeys (legacyRoutes rewriteSpecimen source target fuel)

open Lean Elab Command in
run_cmd
  liftTermElabM do
    let e ← Lean.Elab.Term.elabTerm (← `(id99.rewritePreservesSearchCheck))
      (some (mkConst ``Bool))
    let value ← unsafe Lean.Meta.evalExpr Bool (mkConst ``Bool) e
    unless value do
      throwError "issue #99 probe: the rewritten search disagrees with the pre-rewrite algorithm"

end CasCatalogue.AcceptanceProbes
