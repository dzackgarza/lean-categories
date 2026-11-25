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

Completeness of the *visited-pruned* enumeration is `routeSteps_complete`: a walk that follows
`edgesFrom`, stops at `target` and is not pruned by the enumeration's own gate is enumerated, with
`GateOpen` the gate condition in the orientation `routeSteps` tests it. The pruning never removes a
walk whose gate is open, so together with `walk_length_le_card` a certified enclosure makes the fuel
adequate for every simple route.
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

/-! ## Completeness of the visited-pruned enumeration -/

/-- The targets of an edge chain, in order. -/
def chainTargets : List StructuralEdge → List CategoryExpr
  | [] => []
  | edge :: rest => edge.target :: chainTargets rest

/-- `chain` follows `edgesFrom` from its start vertex, ending at `to`. -/
inductive ChainTo (state : SemanticState) :
    CategoryExpr → List StructuralEdge → CategoryExpr → Prop
  /-- The empty chain ends where it starts. -/
  | nil {vertex : CategoryExpr} : ChainTo state vertex [] vertex
  /-- One edge of the structural graph out of the current vertex, then the rest. -/
  | cons {start finish : CategoryExpr} {edge : StructuralEdge} {rest : List StructuralEdge} :
      edge ∈ state.edgesFrom start → ChainTo state edge.target rest finish →
        ChainTo state start (edge :: rest) finish

/-- Along the chain, the enumeration's stop test is `false` before the last step and `true` at the
end: the search neither stops early nor runs past the target. -/
def StopsAt (target : CategoryExpr) : CategoryExpr → List StructuralEdge → Prop
  | current, [] => current.syntacticEq target = true
  | current, edge :: rest => current.syntacticEq target = false ∧ StopsAt target edge.target rest

/-- The enumeration's pruning gate accepts every step of the chain, in the orientation `routeSteps`
tests it: the target of each step is not among the vertices already visited. This is the condition
a simple route satisfies, read in the direction the gate checks it. -/
def GateOpen : List CategoryExpr → List StructuralEdge → Prop
  | _, [] => True
  | visited, edge :: rest =>
      visited.any (fun vertex => vertex.syntacticEq edge.target) = false ∧
        GateOpen (edge.target :: visited) rest

/-- The equation of `routeSteps` at a literal fuel, definitional in the fuel argument. -/
theorem SemanticState.routeSteps_eq_zero (state : SemanticState) (target current : CategoryExpr)
    (visited : List CategoryExpr) :
    state.routeSteps target current visited 0 =
      (if current.syntacticEq target then #[#[]] else #[]) := rfl

/-- The equation of `routeSteps` at a successor fuel. -/
theorem SemanticState.routeSteps_eq_succ (state : SemanticState) (target current : CategoryExpr)
    (visited : List CategoryExpr) (fuel : ℕ) :
    state.routeSteps target current visited (Nat.succ fuel) =
      (if current.syntacticEq target then #[#[]]
        else (state.edgesFrom current).flatMap fun candidate =>
          if visited.any (fun vertex => vertex.syntacticEq candidate.target) then #[]
          else (state.routeSteps target candidate.target (candidate.target :: visited) fuel).map
            fun steps => #[candidate] ++ steps) := rfl

/-- Completeness of the enumeration: a walk that follows `edgesFrom`, stops at `target` and is not
pruned by the gate is enumerated within any fuel that bounds its length. -/
theorem SemanticState.routeSteps_complete (state : SemanticState) (target : CategoryExpr) :
    ∀ (fuel : ℕ) (current : CategoryExpr) (visited : List CategoryExpr)
      (chain : List StructuralEdge),
      ChainTo state current chain target → StopsAt target current chain →
        GateOpen visited chain → chain.length ≤ fuel →
          chain.toArray ∈ state.routeSteps target current visited fuel
  | 0, current, visited, [], _, hstop, _, _ => by
      have hstopTest : current.syntacticEq target = true := hstop
      rw [SemanticState.routeSteps_eq_zero, if_pos hstopTest]
      simp
  | 0, current, visited, _ :: _, _, _, _, hlen => by
      simp only [List.length_cons] at hlen
      exfalso
      omega
  | Nat.succ fuel, current, visited, [], _, hstop, _, _ => by
      have hstopTest : current.syntacticEq target = true := hstop
      rw [SemanticState.routeSteps_eq_succ, if_pos hstopTest]
      simp
  | Nat.succ fuel, current, visited, edge :: rest, hchain, hstop, hgate, hlen => by
      cases hchain with
      | cons hmem hrest =>
        obtain ⟨hne, hstopRest⟩ := hstop
        obtain ⟨hopen, hgateRest⟩ := hgate
        rw [SemanticState.routeSteps_eq_succ,
          if_neg (by rw [hne]; exact Bool.false_ne_true)]
        refine Array.mem_flatMap.mpr ⟨edge, hmem, ?_⟩
        rw [if_neg (by rw [hopen]; exact Bool.false_ne_true)]
        refine Array.mem_map.mpr ⟨rest.toArray, ?_, ?_⟩
        · exact SemanticState.routeSteps_complete state target fuel edge.target
            (edge.target :: visited) rest hrest hstopRest hgateRest (by
              simp only [List.length_cons] at hlen
              omega)
        · simp

/-- The same completeness for `SemanticState.routes`: the route the walk describes is one of the
routes the search returns, with the walk's labels. -/
theorem SemanticState.routes_complete (state : SemanticState) (source target : CategoryExpr)
    (fuel : ℕ) {chain : List StructuralEdge}
    (hchain : ChainTo state source chain target) (hstop : StopsAt target source chain)
    (hgate : GateOpen [source] chain) (hlen : chain.length ≤ fuel) :
    ∃ route ∈ state.routes source target fuel, route.steps = chain.toArray := by
  refine ⟨{ source := source, target := target, steps := chain.toArray }, ?_, rfl⟩
  exact Array.mem_map.mpr ⟨chain.toArray,
    SemanticState.routeSteps_complete state target fuel source [source] chain hchain hstop hgate
      hlen, rfl⟩

end CasCatalogue
