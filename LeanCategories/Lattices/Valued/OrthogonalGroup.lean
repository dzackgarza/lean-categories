/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Constructions
public import LeanCategories.Modules.Bilinear.Valued.OrthogonalGroup

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

/-- The orthogonal group `O(L)`. -/
abbrev OrthogonalGroup (L : IntegralLatticeCat R) :=
  BilinModuleCat.OrthogonalGroup L.obj

/-- The orbit of a sublattice carrier under `O(L)`. -/
abbrev submoduleOrbit (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) :=
  MulAction.orbit (OrthogonalGroup L) P

/-- The subgroup of `O(L)` that preserves a sublattice carrier. -/
abbrev submoduleStabilizer (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) :=
  MulAction.stabilizer (OrthogonalGroup L) P

end LeanCategories.Lattices.Valued
