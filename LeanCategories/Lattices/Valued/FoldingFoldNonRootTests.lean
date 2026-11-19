/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingFoldNonRoot
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for the `(−4)` non-root case

The lemma is the identity `(α^J)² = 2α² + 2⟨α, gα⟩` read at `α² = −4`, `⟨α, gα⟩ ≥ 4`: the folded
square is `≥ 0`, so Definition 3.7's filter drops the fold. What the probe checks is that the
statement is the one the development can use — applied at the hyperbolic plane with the hypotheses
explicit.

The hypotheses are not computed on a concrete involution here. The natural instance is the negation
`g = −1` of the plane, for which `⟨α, −α⟩ = −α² = 4` at `α² = −4`; constructing it needs the
negation's isometry law `⟨−x, −y⟩ = ⟨x, y⟩`, which this pin of the repository does not have as a
lemma for a lattice pairing, and evaluating it on the packed carrier runs into the coordinate
obstruction the other probes record.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The `(−4)` case at the hyperbolic plane, with the hypotheses explicit. -/
example (g : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)
    (α : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
    (h4 : hyperbolicPlaneFiniteLattice.obj.obj.pairing α α = -4)
    (hge : 4 ≤ hyperbolicPlaneFiniteLattice.obj.obj.pairing α (g.1 α))
    (hne : g.1 α ≠ α) :
    0 ≤ hyperbolicPlaneFiniteLattice.obj.obj.pairing
      (foldedVector g α) (foldedVector g α) :=
  foldedVector_self_nonneg_of_square_neg_four (L := hyperbolicPlaneFiniteLattice) g h4 hge hne

end LeanCategories.Lattices.Valued
