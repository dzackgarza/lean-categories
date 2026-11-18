/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.RouteDiscovery

/-!
# Termination and bound of the registry's own route search

`SemanticState.routes` (`Semantic.lean:1746`) used to be a `partial def` whose recursion ran
through `fuel - 1`, so its termination was assumed rather than proved. It is now
`SemanticState.routeSteps` (structural recursion on `fuel`) mapped into `Route`s, and this module
supplies the two facts that justify the bound:

* `routeSteps_steps_le` — every chain the enumeration returns has at most `fuel` edges;
* `routes_steps_le` — the same for a route returned by `SemanticState.routes`.

Together with `RouteDiscovery.walk_length_le_card`, which says that no simple walk is longer than a
certified enclosure, this makes `fuel` adequate whenever an enclosure is certified. For the registry
no enclosure is certified, so the default `32` is a stated resource bound
(`RouteDiscovery.finite_reach_of_enclosure` carries the hypothesis; nothing here replaces it).

Completeness of the *visited-pruned* enumeration — that every simple route is found, not only that
none is longer than the bound — is not claimed: the pruning's induction needs the visit invariant
across `routeSteps`, and the depth-bounded enumerator whose completeness *is* proved is
`RouteDiscovery.boundedWalks_complete` (issue #99 completion item 3, second reading).
-/

@[expose] public section

namespace CasCatalogue

/-- Every chain the simple-route enumeration returns is no longer than the fuel. -/
theorem SemanticState.routeSteps_steps_le (state : SemanticState) (target : CategoryExpr) :
    ∀ (fuel : ℕ) (current : CategoryExpr) (visited : List CategoryExpr)
      (steps : Array StructuralEdge),
      steps ∈ state.routeSteps target current visited fuel → steps.size ≤ fuel
  | 0, current, visited, steps, h => by
      by_cases hc : current.syntacticEq target = true
      · simp only [SemanticState.routeSteps, hc, if_true] at h
        obtain rfl := Array.mem_singleton.mp h
        simp
      · simp only [SemanticState.routeSteps, hc, if_false] at h
        simp at h
  | fuel + 1, current, visited, steps, h => by
      by_cases hc : current.syntacticEq target = true
      · simp only [SemanticState.routeSteps, hc, if_true] at h
        obtain rfl := Array.mem_singleton.mp h
        simp
      · simp only [SemanticState.routeSteps, hc, if_false] at h
        obtain ⟨edge, -, hsteps⟩ := Array.mem_flatMap.mp h
        by_cases hg : visited.any (fun vertex => vertex.syntacticEq edge.target) = true
        · simp only [hg, if_true] at hsteps
          simp at hsteps
        · simp only [hg, if_false] at hsteps
          obtain ⟨rest, hrest, rfl⟩ := Array.mem_map.mp hsteps
          have hbound := SemanticState.routeSteps_steps_le state target fuel edge.target
            (edge.target :: visited) rest hrest
          simp only [Array.size_append, Array.size_singleton] at hbound ⊢
          omega

/-- Every route the search returns has at most `fuel` steps. -/
theorem SemanticState.routes_steps_le (state : SemanticState) (source target : CategoryExpr)
    (fuel : ℕ) {route : Route} (h : route ∈ state.routes source target fuel) :
    route.steps.size ≤ fuel := by
  obtain ⟨steps, hsteps, rfl⟩ := Array.mem_map.mp h
  exact SemanticState.routeSteps_steps_le state target fuel source [source] steps hsteps

end CasCatalogue
