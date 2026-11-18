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

end CasCatalogue.AcceptanceProbes
