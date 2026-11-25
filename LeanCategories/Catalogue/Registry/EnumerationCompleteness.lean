/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.RouteDiscovery

/-!
# Completeness of a walk enumeration under the enclosure hypothesis

Issue #99's completion item 3 asks that a search "prove its termination and completeness under
stated hypotheses", and that exceeding a resource bound not be presented as a proof that no finite
enclosure exists. `RouteDiscovery` supplied the hypothesis and the bound
(`finite_sublevels`, `enclosure`, `finite_edges`; `walk_length_le_card`). This module supplies the
completeness half for the enumeration it applies to.

`boundedWalks next target fuel source` enumerates the continuations of every walk from `source` of
length at most `fuel`, following `next`. `boundedWalks_complete` proves that every walk whose steps
lie in `next` and whose length fits the fuel is among them, and
`boundedWalks_complete_of_enclosure` replaces `fuel` by the enclosure's cardinality, so that under a
checked enclosure the fuel is a consequence of the hypothesis rather than a cut-off.

Two limits are stated rather than papered over:

* the enumeration proved complete here is *depth-bounded*; `SemanticState.routes`
  (`Semantic.lean:1730`) prunes visited vertices instead and is a `partial def`, so no theorem of
  this file unfolds it. Its simplicity restriction is sound (a route never revisits a category) but
  its completeness is not claimed;
* `next` is a successor function, not the registry's `edgesFrom`: the theorem is about the shape of
  the enumeration the registry uses, not about that particular `partial` implementation.
-/

@[expose] public section

namespace CasCatalogue.RouteDiscovery

variable {V : Type*}

/-- The continuations of a walk from `current`, of length at most `fuel`, following `next`: every
list of vertices reachable from `current` in at most `fuel` steps. The lists returned are the
vertices *after* `current`. -/
def boundedWalks (next : V → List V) : ℕ → V → List (List V)
  | 0, _ => [[]]
  | fuel + 1, current =>
      [[]] ++ (next current).flatMap fun nextVertex =>
        (boundedWalks next fuel nextVertex).map (nextVertex :: ·)

/-- Completeness: every walk from `current` whose steps lie in `next`, and whose length fits the
fuel, is enumerated. The target plays no part in the enumeration; a search for a particular target
filters this list. -/
theorem boundedWalks_complete {next : V → List V} {Step : V → V → Prop}
    (hnext : ∀ ⦃u v⦄, Step u v → v ∈ next u) :
    ∀ (fuel : ℕ) {current : V} {l : List V}, l.head? = some current →
      l.length - 1 ≤ fuel → IsWalk Step l → l.tail ∈ boundedWalks next fuel current
  | 0, current, l, hhead, hlen, hwalk => by
      match l, hhead with
      | [], h => simp at h
      | [_], _ => simp [boundedWalks]
      | _ :: _ :: _, _ =>
          simp only [List.length_cons] at hlen
          exfalso
          omega
  | fuel + 1, current, l, hhead, hlen, hwalk => by
      match l, hhead with
      | [], h => simp at h
      | [_], _ => simp [boundedWalks]
      | x :: y :: rest, h =>
          have hx : current = x := by simpa using h.symm
          subst hx
          have hstep : Step current y := hwalk 0 (by simp)
          have hwalkTail : IsWalk Step (y :: rest) := by
            intro i hi
            exact hwalk (i + 1) (by simpa using hi)
          have hlenTail : (y :: rest).length - 1 ≤ fuel := by
            simp only [List.length_cons] at hlen ⊢
            omega
          have ihTail := boundedWalks_complete hnext fuel rfl hlenTail hwalkTail
          exact List.mem_append.mpr (Or.inr
            (List.mem_flatMap.mpr ⟨y, hnext hstep,
              List.mem_map.mpr ⟨rest, ihTail, rfl⟩⟩))

/-- With the enclosure hypothesis the fuel is the enclosure's cardinality: every simple walk from
`source` to `target` is enumerated by the depth-bounded search at that fuel, so the fuel is a
consequence of the finiteness hypothesis rather than a cut-off. -/
theorem boundedWalks_complete_of_enclosure {next : V → List V} {Step : V → V → Prop}
    (hnext : ∀ ⦃u v⦄, Step u v → v ∈ next u) {source target : V} {enclosure : Finset V}
    (hencloses : ∀ v, Reaches Step source v → v ∈ enclosure) {l : List V}
    (hhead : l.head? = some source) (_hlast : l.getLast? = some target)
    (hwalk : IsWalk Step l) (hnodup : l.Nodup) :
    l.tail ∈ boundedWalks next enclosure.card source := by
  refine boundedWalks_complete hnext enclosure.card hhead ?_ hwalk
  have hbound := walk_length_le_card hhead hwalk hnodup hencloses
  omega

end CasCatalogue.RouteDiscovery
