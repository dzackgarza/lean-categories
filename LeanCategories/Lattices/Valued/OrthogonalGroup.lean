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

end LeanCategories.Lattices.Valued
