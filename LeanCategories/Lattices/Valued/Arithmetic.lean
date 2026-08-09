/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- Finite projective lattices form the finite-carrier full subcategory of `LatticeCat`. -/
def isFiniteProjectiveLattice : ObjectProperty (LatticeCat R W) :=
  fun L ↦ Module.Finite R L.obj.carrier

/-- The category of finite projective `W`-valued `R`-lattices. -/
abbrev FiniteProjectiveLatticeCat :=
  (isFiniteProjectiveLattice R W).FullSubcategory

/-- Finite free lattices form a full subcategory of the general lattice category. -/
def isFiniteFreeLattice : ObjectProperty (LatticeCat R W) :=
  fun L ↦ Module.Finite R L.obj.carrier ∧ Module.Free R L.obj.carrier

/-- The category of finite free `W`-valued `R`-lattices. -/
abbrev FiniteFreeLatticeCat :=
  (isFiniteFreeLattice R W).FullSubcategory

namespace FiniteProjectiveLatticeCat

variable {R W}

/-- A finite projective module over a principal ideal domain is free. -/
theorem carrier_free [IsDomain R] [IsPrincipalIdealRing R]
    (L : FiniteProjectiveLatticeCat R W) : Module.Free R L.obj.obj.carrier := by
  letI : Module.Projective R L.obj.obj.carrier := L.obj.property.1
  letI : Module.Finite R L.obj.obj.carrier := L.property
  infer_instance

end FiniteProjectiveLatticeCat

/-- Forget that a finite free lattice has a free carrier. -/
def finiteFreeToFiniteProjective :
    FiniteFreeLatticeCat R W ⥤ FiniteProjectiveLatticeCat R W where
  obj L := ⟨L.obj, L.property.1⟩
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Over a principal ideal domain, every finite projective lattice is finite free. -/
def finiteProjectiveToFiniteFree [IsDomain R] [IsPrincipalIdealRing R] :
    FiniteProjectiveLatticeCat R W ⥤ FiniteFreeLatticeCat R W where
  obj L := ⟨L.obj, L.property, L.carrier_free⟩
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

end LeanCategories.Lattices.Valued
