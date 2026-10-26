/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.MonoidOperationAgreement
public import LeanCategories.Catalogue.Semantics.Algebra.Semirings
public meta import LeanCategories.Catalogue.Registry.Computation
public meta import LeanCategories.Catalogue.Semantics.Algebra.CatalogueRegistration
public meta import LeanCategories.Catalogue.Semantics.Algebra.Semirings

@[expose] public section

/-!
# Computational derivations along the existing multiplicative forgetful functors

Mathlib's `RingCat.hasForgetToSemiRingCat` and
`SemiRingCat.hasForgetToMonCat` are precisely the two factors already used by
`Ports.ringsMultiplicative`. Their object maps retain the selected multiplication.
This module publishes those factors and the whole-family equations that result.

There are two plans for ring multiplication. One uses its published monoid port;
the other uses semiring multiplication, itself derived from monoid multiplication.
The monoid port also has its factored plan. These are alternatives with ordinary
function application and categorical composition, not ordered semantic choices.

Sources are the existing `Ports`, `MonoidOperations`, `NamedRings`, `Semirings`
and `MonoidOperationAgreement.ring_mul`, and Mathlib
`Algebra/Category/Ring/Basic.lean` at
`db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0).
No multiplication, selected structure, or expected computational answer is added.
-/

open CategoryTheory

namespace CasCatalogue

namespace FunctorId

def ringsSemiring : FunctorId := ⟨"fun.rings.semiring"⟩
def semiringsMonoid : FunctorId := ⟨"fun.semirings.monoid"⟩

end FunctorId

namespace Algebra.ComputationDerivations

universe u

/-- The first factor already used by `Ports.ringsMultiplicative`. -/
def ringsSemiring : LeanCategories.Algebra.Rings.{u} ⟶ Semirings.Semirings.{u} :=
  (forget₂ RingCat SemiRingCat).toCatHom

/-- The second factor already used by `Ports.ringsMultiplicative`. -/
def semiringsMonoid : Semirings.Semirings.{u} ⟶ LeanCategories.Algebra.Monoids.{u} :=
  (forget₂ SemiRingCat MonCat).toCatHom

def RingsSemiringExpr :
    FunctorExpr Catalogue.Rings.Rings Semirings.SemiringsExpr :=
  .atomic FunctorId.ringsSemiring

def SemiringsMonoidExpr :
    FunctorExpr Semirings.SemiringsExpr Catalogue.Magmas.Monoids :=
  .atomic FunctorId.semiringsMonoid

noncomputable def ringsSemiringRealization :
    FunctorRealization RingsSemiringExpr LeanCategories.Algebra.Rings.{u}
      Semirings.Semirings.{u} ringsSemiring.toFunctor :=
  { sourceRealization := CatalogueRegistration.ringsRealization
    targetRealization := Semirings.semiringsRealization }

noncomputable def semiringsMonoidRealization :
    FunctorRealization SemiringsMonoidExpr Semirings.Semirings.{u}
      LeanCategories.Algebra.Monoids.{u} semiringsMonoid.toFunctor :=
  { sourceRealization := Semirings.semiringsRealization
    targetRealization := CatalogueRegistration.monoidsRealization }

/-- The ordinary composition of the two published factors, at every universe. -/
def ringMultiplicativePlan
    (F : LeanCategories.Algebra.Rings.{u} ⟶ Semirings.Semirings.{u})
    (G : Semirings.Semirings.{u} ⟶ LeanCategories.Algebra.Monoids.{u}) :
    LeanCategories.Algebra.Rings.{u} ⟶ LeanCategories.Algebra.Monoids.{u} :=
  F ≫ G

theorem ringMultiplicativePlan_correct :
    ringMultiplicativePlan ringsSemiring.{u} semiringsMonoid =
      Ports.ringsMultiplicative := rfl

/-- The newly exposed factor path has the existing selected monoid port. -/
def ringMultiplicativeComparison :
    Ports.ringsMultiplicative.toFunctor ≅
      (ringsSemiring.{u} ≫ semiringsMonoid).toFunctor := Iso.refl _

/-- Both semiring carrier paths retain its actual underlying set and maps. -/
def semiringCarrierComparison :
    Semirings.semiringsForget.toFunctor ≅
      semiringsMonoid.{u}.toFunctor ⋙ forget MonCat := Iso.refl _

/-- A monoid multiplication family applied to the object map of the ring port.
The intermediate carrier depends on the supplied functor; it is not erased. -/
def ringMulMonoidPlan
    (F : LeanCategories.Algebra.Rings.{0} ⟶ LeanCategories.Algebra.Monoids.{0})
    (mul : (M : MonCat.{0}) → (M × M : Type) ⟶ (M : Type))
    (R : RingCat.{0}) :=
  mul (F.toFunctor.obj R)

theorem ringMulMonoidPlan_correct :
    ringMulMonoidPlan Ports.ringsMultiplicative MonoidOperations.mul = NamedRings.mul :=
  MonoidOperationAgreement.ring_mul

/-- Semiring multiplication is the selected monoid's multiplication. -/
def semiringMulMonoidPlan
    (F : Semirings.Semirings.{0} ⟶ LeanCategories.Algebra.Monoids.{0})
    (mul : (M : MonCat.{0}) → (M × M : Type) ⟶ (M : Type))
    (R : SemiRingCat.{0}) :=
  mul (F.toFunctor.obj R)

theorem semiringMulMonoidPlan_correct :
    semiringMulMonoidPlan semiringsMonoid MonoidOperations.mul = Semirings.mul := rfl

/-- The alternative ring plan calls the complete semiring multiplication family. -/
def ringMulSemiringPlan
    (F : LeanCategories.Algebra.Rings.{0} ⟶ Semirings.Semirings.{0})
    (mul : (R : SemiRingCat.{0}) → (R × R : Type) ⟶ (R : Type))
    (R : RingCat.{0}) :=
  mul (F.toFunctor.obj R)

theorem ringMulSemiringPlan_correct :
    ringMulSemiringPlan ringsSemiring Semirings.mul = NamedRings.mul := rfl

end Algebra.ComputationDerivations

open Algebra.ComputationDerivations

normalized_registry .functor
  { id := FunctorId.ringsSemiring
    source := Algebra.Catalogue.Rings.Rings
    target := Algebra.Semirings.SemiringsExpr
    declaration := `CasCatalogue.Algebra.ComputationDerivations.ringsSemiring
    realization := `CasCatalogue.Algebra.ComputationDerivations.ringsSemiringRealization
    expression := RingsSemiringExpr
    structural := true }

normalized_registry .functor
  { id := FunctorId.semiringsMonoid
    source := Algebra.Semirings.SemiringsExpr
    target := Algebra.Catalogue.Magmas.Monoids
    declaration := `CasCatalogue.Algebra.ComputationDerivations.semiringsMonoid
    realization := `CasCatalogue.Algebra.ComputationDerivations.semiringsMonoidRealization
    expression := SemiringsMonoidExpr
    structural := true }

normalized_registry .cell
  { id := ⟨"cell.rings.multiplicative_monoid.semiring"⟩
    source := Algebra.Catalogue.Rings.Rings
    target := Algebra.Catalogue.Magmas.Monoids
    left := #[.functor FunctorId.ringsMultiplicative]
    right := #[.functor FunctorId.ringsSemiring, .functor FunctorId.semiringsMonoid]
    declaration := `CasCatalogue.Algebra.ComputationDerivations.ringMultiplicativeComparison
    invertible := true }

normalized_registry .cell
  { id := ⟨"cell.semirings.carrier"⟩
    source := Algebra.Semirings.SemiringsExpr
    target := Foundation.Sets
    left := #[.functor FunctorId.semiringsForget]
    right := #[.functor FunctorId.semiringsMonoid, .functor FunctorId.monoidsSemigroup,
      .classifierForget ClassifierId.magmasAssociative,
      .classifierForget ClassifierId.setsBinaryOperation]
    declaration := `CasCatalogue.Algebra.ComputationDerivations.semiringCarrierComparison
    invertible := true }

normalized_computation_derivation
  { id := ⟨"derive.rings.multiplicative_monoid.semiring"⟩
    target := .functor FunctorId.ringsMultiplicative
    prerequisites := #[.functor FunctorId.ringsSemiring, .functor FunctorId.semiringsMonoid]
    plan := `CasCatalogue.Algebra.ComputationDerivations.ringMultiplicativePlan
    correctness := `CasCatalogue.Algebra.ComputationDerivations.ringMultiplicativePlan_correct }

normalized_computation_derivation
  { id := ⟨"derive.rings.mul.monoid"⟩
    target := .operation ⟨"op.rings.mul"⟩
    prerequisites := #[.functor FunctorId.ringsMultiplicative,
      .operation ⟨"op.monoids.mul"⟩]
    plan := `CasCatalogue.Algebra.ComputationDerivations.ringMulMonoidPlan
    correctness := `CasCatalogue.Algebra.ComputationDerivations.ringMulMonoidPlan_correct }

normalized_computation_derivation
  { id := ⟨"derive.semirings.mul.monoid"⟩
    target := .operation ⟨"op.semirings.mul"⟩
    prerequisites := #[.functor FunctorId.semiringsMonoid,
      .operation ⟨"op.monoids.mul"⟩]
    plan := `CasCatalogue.Algebra.ComputationDerivations.semiringMulMonoidPlan
    correctness := `CasCatalogue.Algebra.ComputationDerivations.semiringMulMonoidPlan_correct }

normalized_computation_derivation
  { id := ⟨"derive.rings.mul.semiring"⟩
    target := .operation ⟨"op.rings.mul"⟩
    prerequisites := #[.functor FunctorId.ringsSemiring,
      .operation ⟨"op.semirings.mul"⟩]
    plan := `CasCatalogue.Algebra.ComputationDerivations.ringMulSemiringPlan
    correctness := `CasCatalogue.Algebra.ComputationDerivations.ringMulSemiringPlan_correct }

end CasCatalogue
