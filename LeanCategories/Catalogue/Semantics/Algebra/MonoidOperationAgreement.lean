/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.MonoidOperations
public import LeanCategories.Catalogue.Semantics.Algebra.CommutativeMonoids

@[expose] public section

/-!
# Universal agreement of the existing multiplicative operations

`Catalogue/Registry/operation-agreement.md` specifies the generic comparison:
the complete source and every declaration/structural parameter are abstracted
before a checked equality of the whole operation families is used. Lean's
`Eq.refl` supplies the identity comparison for definitionally equal families;
there is no additional registry row or category priority.

These equations unfold only the existing Mathlib ring/monoid structures and
forgetful functors. In particular, they do not use commutativity, selected
objects, or evaluations of the operations. The commutative-ring equation also
retains the existing structured route comparison
`CommMonoids.commutativeRingsMonoidsCell`. Its components are identities at
the selected multiplicative monoid, not arbitrary equal-carrier identifications.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.MonoidOperationAgreement

universe u v

/-- The entire ring-indexed family, before selecting any ring or operands. -/
theorem ring_mul :
    (fun R : RingCat.{0} =>
      MonoidOperations.mul (Ports.ringsMultiplicative.toFunctor.obj R)) =
        NamedRings.mul := rfl

/-- The two incomparable bindings from commutative rings agree as complete
operation families along their actual multiplicative routes. -/
theorem commutative_ring_mul :
    (fun R : CommRingCat.{0} =>
      NamedRings.mul (Algebras.commutativeRingsRings.toFunctor.obj R)) =
    (fun R : CommRingCat.{0} =>
      MonoidOperations.mul ((CommMonoids.commutativeRingsMultiplicative ≫
        CommMonoids.commutativeMonoidsMonoid).toFunctor.obj R)) := rfl

/-- Precomposition retains any selected structural functor in the whole family.
`C`, its category structure, and `F` remain universally quantified parameters. -/
theorem commutative_ring_mul_precomp {C : Type u} [Category.{v} C]
    (F : C ⥤ CommRingCat.{0}) :
    (fun X : C =>
      NamedRings.mul (Algebras.commutativeRingsRings.toFunctor.obj (F.obj X))) =
    (fun X : C =>
      MonoidOperations.mul ((CommMonoids.commutativeRingsMultiplicative ≫
        CommMonoids.commutativeMonoidsMonoid).toFunctor.obj (F.obj X))) := rfl

/-- The additive port gives the whole addition family, never multiplication. -/
theorem additive_port :
    (fun R : RingCat.{0} =>
      MonoidOperations.mul (Ports.groupsMonoid.toFunctor.obj
        (Ports.additiveGroupsToGroups.toFunctor.obj
          (Ports.ringsAdditive.toFunctor.obj R)))) =
        NamedRings.add := rfl

end CasCatalogue.Algebra.MonoidOperationAgreement
