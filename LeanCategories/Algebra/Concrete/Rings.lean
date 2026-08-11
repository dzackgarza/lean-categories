/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import LeanCategories.Algebra.Concrete.Magmas

@[expose] public section

/-!
# Rings

This file owns the concrete categories of rings, commutative rings, and division rings.
-/

namespace LeanCategories.Algebra

open CategoryTheory

universe u

def Rings : ObjCat.{u + 1, u} := Cat.of RingCat.{u}
def CommutativeRings : ObjCat.{u + 1, u} := Cat.of CommRingCat.{u}

def IsDivisionRing (R : RingCat.{u}) : Prop := Nonempty (DivisionRing R)

abbrev DivisionRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := RingCat.{u}) IsDivisionRing

noncomputable def divisionOnRings : Classifier Rings where
  total := Cat.of DivisionRingCat.{u}
  forget := (ObjectProperty.ι (C := RingCat.{u}) IsDivisionRing).toCatHom

noncomputable def DivisionRings : ObjCat.{u + 1, u} := divisionOnRings.total

end LeanCategories.Algebra
