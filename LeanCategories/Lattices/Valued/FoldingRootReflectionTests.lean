/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingRootReflection
public import LeanCategories.Lattices.Valued.FoldingDiagram

/-!
# Probe for `rootReflection`, on the smallest input that decides it

The reflection is a lattice isometry of `M^σ`; what decides that is its defining property on a root:
`(w_α v)² = v²` for the square, and the reflection of the root itself is its own negative
(`w_α α = -α`). Both are read at the worked invariant lattice of `T_dP` at the `E₈` block's
`e₀ - e₀'`, whose square is `-4`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The reflection in a root preserves the square of that root. -/
example [Module.Projective ℤ (involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry)]
    (v : (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry).obj.obj.carrier)
    (hv : IsReflectiveRoot (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry).obj v) :
    (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry).obj.obj.pairing
        ((rootReflection (L := tdpFiniteLattice) tdpIsometry v hv).1 v)
        ((rootReflection (L := tdpFiniteLattice) tdpIsometry v hv).1 v)
      = (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry).obj.obj.pairing v v :=
  (rootReflection (L := tdpFiniteLattice) tdpIsometry v hv).property v v

/-- The reflection in a reflective root is again a reflective root. -/
example [Module.Projective ℤ (involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry)]
    (v : (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry).obj.obj.carrier)
    (hv : IsReflectiveRoot (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry).obj v) :
    IsReflectiveRoot (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry).obj
      ((rootReflection (L := tdpFiniteLattice) tdpIsometry v hv).1 v) :=
  rootReflection_reflective (L := tdpFiniteLattice) tdpIsometry v hv hv

#print axioms rootReflection_reflective

end LeanCategories.Lattices.Valued
