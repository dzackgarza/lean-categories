/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

noncomputable section

namespace SimpleGraph.Walk

universe u
variable {V : Type u} {G : SimpleGraph V} {u v w : V}

/-- A walk has no immediate occurrence of an edge followed by the oppositely oriented edge
(FC02-C14-U014). -/
def IsReduced (p : G.Walk u v) : Prop :=
  ∀ i (hi : i + 1 < p.darts.length), p.darts[i + 1] ≠ (p.darts[i]).symm

/-- Reduced-prepend for simple-graph walks. If the first edge of `p` immediately reverses `h`,
cancel the pair; otherwise prepend `h`.

Adapted from the `redCons` construction in Mathlib PR #11604 at
`0a7c341ccbe6b354f277b0f48bad76e13e6ea866` (Apache-2.0). -/
noncomputable def redCons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w := by
  cases p with
  | nil => exact .cons h .nil
  | @cons _ x _ h' p' =>
      by_cases hx : x = u
      · subst x
        exact p'
      · exact .cons h (.cons h' p')

/-- Recursive reduction by repeatedly cancelling adjacent oppositely oriented edges
(FC02-C14-U015).

Adapted from `Multigraph.reduction` in Mathlib PR #11604 at
`0a7c341ccbe6b354f277b0f48bad76e13e6ea866` (Apache-2.0). -/
noncomputable def reduction {u v : V} : G.Walk u v → G.Walk u v
  | .nil => .nil
  | .cons h p => redCons h (reduction p)

end SimpleGraph.Walk

namespace SimpleGraph

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Euler number `#V - #E` of a finite simple graph (FC02-C14-U025). -/
def eulerNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  Fintype.card V - G.edgeFinset.card

end SimpleGraph
