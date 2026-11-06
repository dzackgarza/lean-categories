/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.SmashProduct

/-! # Card: `LeanCategories.Topology.BasedTop.map_point`

source: Riehl, *Category Theory in Context*, §4.4 (FC03-C04-U037): the based smash product

Published copy of a result from `LeanCategories.Topology.SmashProduct`; the definition module keeps the original declaration, this file restates it, and the platform submission replaces the delegated proof with `by sorry`.
-/

@[expose] public section

namespace LeanCategories.Cards

open LeanCategories.Topology

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open LeanCategories.Topology
universe u
open BasedTop

/-- A morphism of based spaces preserves the distinguished point. -/
theorem LeanCategories_Topology_BasedTop_map_point : ∀ {X Y : BasedTop.{u}} (f : X ⟶ Y),
    f.right X.point = Y.point :=
  LeanCategories.Topology.BasedTop.map_point

end LeanCategories.Cards
