/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.PresentedGroup

/-!
# Cayley graph and Cayley-complex cell data

Hatcher FC07-C01-U067 starts from a presentation `G = <g_alpha | r_beta>`.
At the declaration layer, its Cayley complex has vertices indexed by `G`, one
oriented labelled edge for every pair `(g, alpha)`, and one relator 2-cell for
every pair `(g, beta)`. This file records exactly those cell indices and the
associated source/target/word data.

Topological disk attachment, the resulting CW structure, the covering map to
the presentation complex, and the universal-cover assertion are later result
content and are deliberately not constructor fields here.
-/

@[expose] public section

namespace LeanCategories.Topology

universe u

variable {Generator : Type u} (rels : Set (FreeGroup Generator))

/-- Vertices of the Cayley graph of the group presented by `rels`. -/
abbrev PresentedCayleyVertex : Type u := PresentedGroup rels

/-- An oriented labelled Cayley edge: from `source` to `source * g_alpha`. -/
structure PresentedCayleyEdge where
  /-- Initial vertex of the edge. -/
  source : PresentedGroup rels
  /-- Generator labelling the edge. -/
  generator : Generator

namespace PresentedCayleyEdge

/-- Terminal vertex of a labelled Cayley edge. -/
def target (e : PresentedCayleyEdge rels) : PresentedGroup rels :=
  e.source * PresentedGroup.of e.generator

end PresentedCayleyEdge

/-- A relator 2-cell of the Cayley complex, indexed by the translate at which
the corresponding relator loop is attached. -/
structure PresentedCayleyTwoCell where
  /-- Vertex translating the relator loop. -/
  translate : PresentedGroup rels
  /-- Relator whose translated loop is the attaching word. -/
  relator : rels

namespace PresentedCayleyTwoCell

/-- The free-group word labelling the boundary of a Cayley 2-cell. -/
def boundaryWord (c : PresentedCayleyTwoCell rels) : FreeGroup Generator :=
  c.relator.1

end PresentedCayleyTwoCell

end LeanCategories.Topology
