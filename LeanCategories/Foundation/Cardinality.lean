/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

/-!
# Cardinality as a functor

#53 §3: cardinality is the isomorphism invariant
`card : Core(Set) ⥤ Disc(Card)`, `X ↦ #X`. An isomorphism of sets is sent to the identity of its
(common) cardinal, by `Cardinal.mk_congr`.
-/

open CategoryTheory

namespace LeanCategories.Foundation

universe u

/-- Cardinality, the isomorphism invariant of sets, as a functor on the core of `Type u`. -/
def cardinality : Core (Type u) ⥤ Discrete Cardinal.{u} where
  obj X := ⟨Cardinal.mk X.of⟩
  map f := eqToHom (congrArg Discrete.mk (Cardinal.mk_congr f.iso.toEquiv))

/-- The cardinality of a set, read off the functor. -/
@[simp] theorem cardinality_obj (X : Core (Type u)) :
    (cardinality.obj X).as = Cardinal.mk X.of := rfl

end LeanCategories.Foundation
