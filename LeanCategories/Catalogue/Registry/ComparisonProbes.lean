/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.RouteDiscovery
public meta import LeanCategories.Catalogue.Registry.RouteDiscovery

/-!
# Route discovery probes: what selection retains and what the search does not enumerate

Executable checks over specimen states. No cell row is registered in this repository yet (no
`validateCell`-checked row exists), so the rows here name real declarations but are not registry
rows: they exercise the selection logic, which reads only a row's two routes, its `invertible` flag
and its stable id, and the retention theorems are proved for every state. The two-cycle specimen
exercises the enumeration on a graph with a loop.

What these probes show, matching issue #99's completion items:

* competing cells are both retained, in the order selection reports them, and the outcome is
  `competing` rather than a choice (`id99.competing`, `id99.competingIds`);
* a non-invertible cell is a candidate only in its own direction (`id99.reversedNotBackward`);
* a pair that no registered cell relates is `unrelated`, which is not a claim of inequality
  (`id99.unrelated`);
* an explicitly specified composite that revisits a category is accepted by `routeEdges?`, while
  the implicit enumeration of simple routes does not produce it (`id99.explicitRevisiting`).
-/

@[expose] public section

namespace CasCatalogue.RouteDiscoveryProbes

open CasCatalogue

/-- The stable ids a selection reports, in the order it reports them. -/
def selectionIds : ComparisonSelection → List String
  | .unrelated => []
  | .unique witness => [witness.cell.id.raw]
  | .competing witnesses => witnesses.map fun witness => witness.cell.id.raw

def firstRoute : Array EdgeRef := #[.functor ⟨"fun.first"⟩]

def secondRoute : Array EdgeRef := #[.functor ⟨"fun.second"⟩]

def loneRoute : Array EdgeRef := #[.functor ⟨"fun.lone"⟩]

/-- Two parallel invertible cells on one pair of routes, the reverse-direction partner of that pair,
and a non-invertible cell on the same pair: direction, not search order, decides candidacy. -/
def comparisonSpecimen : SemanticState :=
  { cells := #[
      { id := ⟨"cmp.probe.first"⟩, source := .atom ⟨"cat.upper"⟩,
        target := .atom ⟨"cat.lower"⟩, left := #[.functor ⟨"fun.first"⟩],
        right := #[.functor ⟨"fun.second"⟩]
        declaration := ``CategoryTheory.Iso.refl, invertible := true },
      { id := ⟨"cmp.probe.second"⟩, source := .atom ⟨"cat.upper"⟩,
        target := .atom ⟨"cat.lower"⟩, left := #[.functor ⟨"fun.first"⟩],
        right := #[.functor ⟨"fun.second"⟩]
        declaration := ``CategoryTheory.Iso.refl, invertible := true },
      { id := ⟨"cmp.probe.reversed"⟩, source := .atom ⟨"cat.upper"⟩,
        target := .atom ⟨"cat.lower"⟩, left := #[.functor ⟨"fun.second"⟩]
        right := #[.functor ⟨"fun.first"⟩], declaration := ``CategoryTheory.Iso.refl
        invertible := true },
      { id := ⟨"cmp.probe.oneWay"⟩, source := .atom ⟨"cat.upper"⟩,
        target := .atom ⟨"cat.lower"⟩, left := #[.functor ⟨"fun.lone"⟩]
        right := #[.functor ⟨"fun.second"⟩], declaration := ``CategoryTheory.Iso.refl
        invertible := false }] }

/-- Two competing registered cells give the competing outcome. -/
theorem id99.competing :
    (comparisonSpecimen.selectComparison firstRoute secondRoute).isCompeting = true := by
  decide

/-- Both competing cells are retained, and the invertible reverse-direction cell with them: three
witnesses, none merged and none dropped. -/
theorem id99.competingIds :
    selectionIds (comparisonSpecimen.selectComparison firstRoute secondRoute) =
      ["cmp.probe.first", "cmp.probe.second", "cmp.probe.reversed"] := by
  decide

/-- A single registered cell gives the unique outcome. -/
theorem id99.unique :
    (comparisonSpecimen.selectComparison loneRoute secondRoute).isUnique = true := by
  decide

/-- The non-invertible row relating `second` to `lone` is not read backwards, so the reversed pair
has no candidate at all. -/
theorem id99.reversedNotBackward :
    (comparisonSpecimen.selectComparison secondRoute loneRoute).isUnrelated = true := by
  decide

/-- No registered cell relates this pair: selection says so, and claims nothing more. -/
theorem id99.unrelated :
    (comparisonSpecimen.selectComparison firstRoute loneRoute).isUnrelated = true := by
  decide

/-- The same pair read the other way keeps the non-invertible row, in its own direction. -/
theorem id99.oneWayForward :
    selectionIds (comparisonSpecimen.selectComparison loneRoute secondRoute) =
      ["cmp.probe.oneWay"] := by
  decide

/-- A structural pair in both directions: the enumeration of simple routes finds the direct route
and never revisits `cat.a`. -/
def cycleSpecimen : SemanticState :=
  { functors := #[
      { id := ⟨"fun.ab"⟩, source := .atom ⟨"cat.a"⟩, target := .atom ⟨"cat.b"⟩
        declaration := ``sameEndpoint, realization := ``sameEndpoint
        expression := .atomic ⟨"fun.ab"⟩, structural := true },
      { id := ⟨"fun.ba"⟩, source := .atom ⟨"cat.b"⟩, target := .atom ⟨"cat.a"⟩
        declaration := ``sameEndpoint, realization := ``sameEndpoint
        expression := .atomic ⟨"fun.ba"⟩, structural := true }] }

theorem id99.simpleRoutesOnly :
    (cycleSpecimen.routes (.atom ⟨"cat.a"⟩) (.atom ⟨"cat.b"⟩)).size = 1 := by
  native_decide

/-- The explicitly specified composite `a → b → a → b` is accepted step by step: the simplicity
restriction of the enumeration does not reject a route the caller states. -/
theorem id99.explicitRevisiting :
    (cycleSpecimen.routeEdges? (.atom ⟨"cat.a"⟩) (.atom ⟨"cat.b"⟩)
      #[.functor ⟨"fun.ab"⟩, .functor ⟨"fun.ba"⟩,
        .functor ⟨"fun.ab"⟩]).isSome = true := by
  native_decide

end CasCatalogue.RouteDiscoveryProbes
