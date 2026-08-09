/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- Change the value module by postcomposition. -/
def changeValue {W' : Type u} [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') : LatticeCat R W ⥤ LatticeCat R W' where
  obj L :=
    ⟨(LeanCategories.Modules.Bilinear.Valued.changeValue R W f).obj L.obj,
      ⟨L.property.1, L.property.2.1,
        fun x y ↦ congr_arg f (L.property.2.2 x y)⟩⟩
  map g := ObjectProperty.homMk
    ((LeanCategories.Modules.Bilinear.Valued.changeValue R W f).map g.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

end LeanCategories.Lattices.Valued

