/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence

@[expose] public section

/-!
# The set of maps `Y^X`

`Y^X`, the set of all maps `X → Y`: the exponential object of `Sets` (Mac Lane, *Categories for
the Working Mathematician*, IV.6; in Lean the function type `X → Y`, the internal hom of `Type`,
Mathlib `CategoryTheory.Types` with `CartesianClosed`). Every map `X → Y` is an element of `Y^X`:
its admission has no hypothesis, so there is nothing for its evidence to establish. An operation
total on every map out of `X` (a sum over a finite subset of `X`, `FiniteSums`) is a morphism out
of `Y^X`.
-/

open CategoryTheory

namespace CasCatalogue.Foundation.Maps

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- `Y^X`, the maps `X → Y`. -/
abbrev maps (X Y : Type) : SetsCat.{0} := X → Y

/-- The map `f : X → Y` as an element of `Y^X`. Every map is one: there is no hypothesis. -/
def admit (X Y : Type) (f : X → Y) : fin 1 ⟶ maps X Y := TypeCat.ofHom fun _ => f

open Lean Elab Tactic in
/-- The evidence of the admission into `Y^X`. The admission has no hypothesis, so it is never run
on a goal: every map `X → Y` is an element of `Y^X`, and no proof is owed. Run on a goal, it
establishes nothing and fails. -/
meta def mapsEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "Y^X" <| CasCatalogue.Evidence.closeByFirst
    m!"an element of Y^X needs no evidence; there is no hypothesis to establish" []

end CasCatalogue.Foundation.Maps

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.maps"⟩, category := CategoryId.sets, name := "Maps"
    declaration := `CasCatalogue.Foundation.Maps.maps
    admission := some `CasCatalogue.Foundation.Maps.admit
    evidence := some `CasCatalogue.Foundation.Maps.mapsEvidence }

end CasCatalogue
