/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change of commutative algebras

Mathlib's equivalence between commutative algebras and under-categories
identifies base change with tensor-product pushout.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Algebra

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Base change of commutative algebras along `R ⟶ S`. -/
abbrev commAlgBaseChange : CommAlgCat R ⥤ CommAlgCat S :=
  (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
    CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of S) ⋙
      (commAlgCatEquivUnder (CommRingCat.of S)).inverse

end LeanCategories.Algebra
