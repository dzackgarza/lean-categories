/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Basic
public import LeanCategories.Modules.Framed
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R]
variable (n : ℕ)

/-- Forget an integral lattice to its carrier module. -/
def integralLatticeForget : IntegralLatticeCat R ⥤ ModuleCat R :=
  (isLattice R R).ι ⋙ LeanCategories.Modules.Bilinear.Valued.forget R R

/-- Rank-`n` coordinatized lattices form the categorical pullback of coordinates
and intrinsic lattices over their carrier modules. -/
abbrev CoordLatticeCat (n : ℕ) :=
  CategoricalPullback
    (LeanCategories.Modules.Coord.forget R (Fin n))
    (integralLatticeForget R)

/-- Forget a coordinatized lattice to its coordinatized carrier module. -/
def coordLatticeToCoord :
    CoordLatticeCat R n ⥤ LeanCategories.Modules.Coord R (Fin n) :=
  CategoricalPullback.π₁ _ _

/-- Compare a coordinatized lattice with its intrinsic lattice. -/
def coordLatticeToIntegral : CoordLatticeCat R n ⥤ IntegralLatticeCat R :=
  CategoricalPullback.π₂ _ _

namespace CoordLatticeCat

/-- Equip an intrinsic lattice with coordinates from a selected finite basis. -/
noncomputable def ofBasis (L : IntegralLatticeCat R)
    (b : Module.Basis (Fin n) R L.obj.carrier) : CoordLatticeCat R n := by
  let e : LeanCategories.Modules.StandardFreeModule R (Fin n) ≅ L.obj.carrierObj :=
    LinearEquiv.toModuleIso
      ((Finsupp.linearEquivFunOnFinite R R (Fin n)).trans b.equivFun.symm)
  exact
    { fst := LeanCategories.Modules.Coord.ofIso R (Fin n) e
      snd := L
      iso := Iso.refl _ }

@[simp]
theorem coordLatticeToIntegral_obj_ofBasis (L : IntegralLatticeCat R)
    (b : Module.Basis (Fin n) R L.obj.carrier) :
    (coordLatticeToIntegral R n).obj (ofBasis R n L b) = L :=
  rfl

end CoordLatticeCat

end LeanCategories.Lattices.Valued
