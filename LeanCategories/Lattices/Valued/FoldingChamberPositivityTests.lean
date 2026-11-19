/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingChamberPositivity
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for the positivity transfer

The lemma moves positivity from the ambient walls to the folded walls, by the same `ε` mechanism as
the fold transfer. What the probe checks is that it applies where the development needs it: at the
hyperbolic plane with the ambient positivity given, the folded conclusion follows.

The hypothesis is not discharged on the concrete `uInterior`/`uRoot` pair here: after
`invariantFixedLattice_pairing` the goal's second argument is the coercion of `R i`, and rewriting
with
`uInterior_pairing_root` — which is stated on the model carrier `Fin 2 → ℤ` — does not match it.
That is the packed-carrier evaluation obstruction the other probes record, not a gap in the lemma.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- Positivity transfers at the plane: from the ambient walls to the folded walls. -/
example (g : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (hg : g * g = 1)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (w : involutionFixedSubmodule g)
    (hwamb : ∀ i : Fin 1, 0 < hyperbolicPlaneFiniteLattice.obj.obj.pairing
      (w : hyperbolicPlaneFiniteLattice.obj.obj.carrier) ((fun _ : Fin 1 => uRoot) i)) :
    ∀ i : Fin 1, 0 < (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice) g).obj.obj.pairing w
      (foldedWallFamily (L := hyperbolicPlaneFiniteLattice) g hg (fun _ : Fin 1 => uRoot) i) :=
  foldedWallFamily_pairing_pos (L := hyperbolicPlaneFiniteLattice) g hg
    (fun _ : Fin 1 => uRoot) w hwamb

end LeanCategories.Lattices.Valued
