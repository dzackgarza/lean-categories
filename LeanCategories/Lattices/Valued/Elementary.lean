/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Discriminant

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R] [IsDomain R]

/-- The carrier of the discriminant module `A_L = L♯/L`. -/
abbrev discriminantModule (L : IntegralLatticeCat R) : Type u :=
  (discriminantSymBilWFormObject R L).obj.carrier

/-- A lattice is `I`-elementary when the ideal `I` annihilates its discriminant module.

At a height-one prime this is `𝔭`-elementarity; over `ℤ` the ideal `(p)` gives the
classical `p`-elementary lattices. -/
def IsIElementary (L : IntegralLatticeCat R) (I : Ideal R) : Prop :=
  Module.IsTorsionBySet R (discriminantModule R L) I

/-- Elementarity is containment of the ideal in the annihilator of the discriminant
module. -/
theorem isIElementary_iff_le_annihilator (L : IntegralLatticeCat R) (I : Ideal R) :
    IsIElementary R L I ↔ I ≤ Module.annihilator R (discriminantModule R L) :=
  Module.isTorsionBySet_iff_subset_annihilator R (discriminantModule R L)

/-- A smaller ideal inherits elementarity. -/
theorem IsIElementary.mono {L : IntegralLatticeCat R} {I J : Ideal R}
    (h : IsIElementary R L J) (hIJ : I ≤ J) : IsIElementary R L I :=
  Module.isTorsionBySet_of_subset hIJ h

/-- Every lattice is elementary for the annihilator of its discriminant module. -/
theorem isIElementary_annihilator (L : IntegralLatticeCat R) :
    IsIElementary R L (Module.annihilator R (discriminantModule R L)) :=
  Module.isTorsionBySet_annihilator R (discriminantModule R L)

/-- The discriminant module of an `I`-elementary lattice is a module over the residue
ring `R ⧸ I`. -/
noncomputable abbrev IsIElementary.residueModule {L : IntegralLatticeCat R} {I : Ideal R}
    (h : IsIElementary R L I) : Module (R ⧸ I) (discriminantModule R L) :=
  h.module

/-- The residue rank of an elementary lattice, its discriminant module measured over the
residue ring. For a height-one prime this is the length `a_𝔭(L)`. -/
noncomputable def IsIElementary.residueRank {L : IntegralLatticeCat R} {I : Ideal R}
    (h : IsIElementary R L I) : ℕ :=
  letI := h.residueModule R
  Module.finrank (R ⧸ I) (discriminantModule R L)

end LeanCategories.Lattices.Valued
