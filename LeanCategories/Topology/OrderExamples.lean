/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.Real

@[expose] public section

namespace LeanCategories.Topology

open Set TopologicalSpace

/-- Munkres' set `K = {1/n | n ∈ ℕ_{>0}}`. -/
def munkresK : Set ℝ :=
  {x | ∃ n : ℕ+, x = 1 / (n : ℝ)}

/-- The standard basis used to define Munkres' `K`-topology on `ℝ`: ordinary
open intervals and intervals with `K` removed. -/
def kTopologyBasis : Set (Set ℝ) :=
  {s | ∃ a b : ℝ, a < b ∧ (s = Ioo a b ∨ s = Ioo a b \ munkresK)}

/-- Munkres' `K`-topology on `ℝ`, FC02-C02-U020. -/
@[instance_reducible]
def kTopology : TopologicalSpace ℝ :=
  generateFrom kTopologyBasis

/-- The closed unit interval, used in the ordered-square construction. -/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- The underlying ordered square `I × I` with dictionary (lexicographic) order. -/
abbrev OrderedUnitSquare := Lex (UnitInterval × UnitInterval)

/-- The order topology on the dictionary-ordered square, Munkres FC02-C02-U043. -/
@[instance_reducible]
def orderedUnitSquareTopology : TopologicalSpace OrderedUnitSquare :=
  Preorder.topology OrderedUnitSquare

end LeanCategories.Topology
