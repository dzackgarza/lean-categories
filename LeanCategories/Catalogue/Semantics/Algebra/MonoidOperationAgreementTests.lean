/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.MonoidOperationAgreement
public import LeanCategories.Catalogue.Semantics.Algebra.Fields

@[expose] public section

open CategoryTheory

namespace CasCatalogue.Algebra.MonoidOperationAgreementTests

/-- Both whole multiplicative families agree at a universally quantified field;
the classifier's exact forgetful functor remains in the equation. -/
example :
    (fun K : LeanCategories.Algebra.FieldCat.{0} =>
      NamedRings.mul (Algebras.commutativeRingsRings.toFunctor.obj
        (Fields.fieldClassifier.forget.toFunctor.obj K))) =
    (fun K : LeanCategories.Algebra.FieldCat.{0} =>
      MonoidOperations.mul ((CommMonoids.commutativeRingsMultiplicative ≫
        CommMonoids.commutativeMonoidsMonoid).toFunctor.obj
          (Fields.fieldClassifier.forget.toFunctor.obj K))) :=
  MonoidOperationAgreement.commutative_ring_mul_precomp
    Fields.fieldClassifier.forget.toFunctor

/-- The scalar ring of a parameterized source category is universally abstracted
too. No fixed coefficient ring is substituted before comparison. -/
example :
    (fun (K : CommRingCat.{0}) (A : Under K) =>
      NamedRings.mul (Algebras.commutativeRingsRings.toFunctor.obj
        ((Algebras.algebrasForget K).obj A))) =
    (fun (K : CommRingCat.{0}) (A : Under K) =>
      MonoidOperations.mul ((CommMonoids.commutativeRingsMultiplicative ≫
        CommMonoids.commutativeMonoidsMonoid).toFunctor.obj
          ((Algebras.algebrasForget K).obj A))) := rfl

/-- The preexisting structured comparison retains both actual identity maps. -/
example (R : CommRingCat.{0}) :
    (CommMonoids.commutativeRingsMonoidsCell.app R).hom = 𝟙 _ ∧
      (CommMonoids.commutativeRingsMonoidsCell.app R).inv = 𝟙 _ := ⟨rfl, rfl⟩

/-- A coincident selected answer cannot compare the two whole operations. -/
example : NamedRings.mul (RingCat.of ℤ) ((2 : ℤ), 2) =
    NamedRings.add (RingCat.of ℤ) ((2 : ℤ), 2) := rfl

theorem integer_mul_ne_add :
    NamedRings.mul (RingCat.of ℤ) ≠ NamedRings.add (RingCat.of ℤ) := by
  intro h
  have impossible := congrArg (fun f => f ((2 : ℤ), 3)) h
  change (6 : ℤ) = 5 at impossible
  exact (by decide : (6 : ℤ) ≠ 5) impossible

/-- The whole universal families are distinct, regardless of their coincidence
at some selected arguments. -/
example : (fun R : RingCat.{0} => NamedRings.mul R) ≠ NamedRings.add := by
  intro h
  exact integer_mul_ne_add (congrFun h (RingCat.of ℤ))

/-- Even equality of whole maps on one selected source object is insufficient:
the one-element ring makes both operations equal, unlike the universal family. -/
example : NamedRings.mul (RingCat.of (ZMod 1)) =
    NamedRings.add (RingCat.of (ZMod 1)) := by
  apply ConcreteCategory.hom_ext
  intro p
  exact Subsingleton.elim _ _

/-- Two independently selected monoids are not identified by sharing a carrier.
The multiplicative and additively reinterpreted integer structures separate them. -/
example : ¬ (∀ (M N : MonCat.{0}),
    HEq (MonoidOperations.mul M) (MonoidOperations.mul N)) := by
  intro h
  have same : MonoidOperations.mul (MonCat.of ℤ) =
      MonoidOperations.mul (MonCat.of (Multiplicative ℤ)) :=
    eq_of_heq (h (MonCat.of ℤ) (MonCat.of (Multiplicative ℤ)))
  have impossible := congrArg (fun f => f ((2 : ℤ), 3)) same
  change (6 : ℤ) = 5 at impossible
  exact (by decide : (6 : ℤ) ≠ 5) impossible

/-- Independent declaration parameters cannot be unified or specialized away. -/
example : ¬ (∀ (R : RingCat.{0}) (n m : ℕ),
    NamedRings.pow R n = NamedRings.pow R m) := by
  intro h
  have impossible := congrArg (fun f => f (2 : ℤ)) (h (RingCat.of ℤ) 1 2)
  change (2 : ℤ) = 4 at impossible
  exact (by decide : (2 : ℤ) ≠ 4) impossible

/-- Specializing the two exponents to the same numeral would hide that failure. -/
example (R : RingCat.{0}) : NamedRings.pow R 2 = NamedRings.pow R 2 := rfl

end CasCatalogue.Algebra.MonoidOperationAgreementTests
