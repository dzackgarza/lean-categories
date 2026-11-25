/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingTdpE8NotAChamber

/-!
# Probe: the eight `E₈` walls are not a chamber of `T_dP`

`chamberOf_folded_trace_tdpE8` carries `IsChamberWithWalls tdpFiniteLattice t (Set.range
tdpE8Family)`. The probes decide that this is unsatisfiable: a `U`-summand root is a negative square
root of `T_dP`, orthogonal to every folded `E₈` wall, hence not a `ℤ`-combination of them.

The second probe is the guard against the trivial escape: the `U`-root really has square `−2`, so it
is a genuine root rather than a vector chosen to make the pairing vanish.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The `U`-root is a genuine root: square `−2`. -/
example : tdpFiniteLattice.obj.obj.pairing tdpURoot tdpURoot = -2 := tdpURoot_square

/-- It is not a combination of the eight folded `E₈` walls. -/
example : ¬ ∃ c : Fin 8 → ℤ,
    tdpURoot = ∑ i, c i • foldedVector tdpIsometry (tdpE8Root i) :=
  tdpURoot_not_combination

end LeanCategories.Lattices.Valued
