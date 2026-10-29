/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.MonoidOperations
public import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms
public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings

@[expose] public section

open CategoryTheory
open CasCatalogue.Algebra.MonoidOperations

namespace CasCatalogue.Algebra.MonoidOperationsTests

/-- On the multiplicative monoid of the integers, the unit is integer one. -/
example : one (MonCat.of ℤ) 0 = (1 : ℤ) := rfl

/-- On the additive group expressed multiplicatively, the unit is integer zero.
The common carrier cannot identify these two selected structures. -/
example : one (MonCat.of (Multiplicative ℤ)) 0 = Multiplicative.ofAdd (0 : ℤ) := rfl

example : mul (MonCat.of ℤ) ((2 : ℤ), 3) = 6 := rfl

example : mul (MonCat.of (Multiplicative ℤ))
    (Multiplicative.ofAdd (2 : ℤ), Multiplicative.ofAdd (3 : ℤ)) =
      Multiplicative.ofAdd (5 : ℤ) := rfl

/-- The declared ring multiplication agrees with the whole operation inherited
along its multiplicative port, for every selected ring. -/
example (R : RingCat.{0}) :
    mul (Ports.ringsMultiplicative.toFunctor.obj R) = NamedRings.mul R := rfl

/-- The additive port instead gives the ring's addition, with the same carrier
but a different complete binary operation. -/
example (R : RingCat.{0}) :
    mul (Ports.groupsMonoid.toFunctor.obj
      (Ports.additiveGroupsToGroups.toFunctor.obj (Ports.ringsAdditive.toFunctor.obj R))) =
        NamedRings.add R := rfl

/-- The inherited identity is the complete identity automorphism. -/
example (G : GrpCat.{0}) :
    one ((forget₂ GrpCat MonCat).obj
      ((Automorphisms.automorphisms GrpCat).obj ⟨G⟩)) 0 = Iso.refl G := rfl

/-- The inherited multiplication keeps Mathlib's actual composition order. -/
example (G : GrpCat.{0}) (a b : Aut G) :
    (mul ((forget₂ GrpCat MonCat).obj
      ((Automorphisms.automorphisms GrpCat).obj ⟨G⟩)) (a, b)).hom =
        b.hom ≫ a.hom := rfl

end CasCatalogue.Algebra.MonoidOperationsTests
