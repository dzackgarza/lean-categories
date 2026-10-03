/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Algebras
public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Algebras
public meta import LeanCategories.Catalogue.Semantics.Algebra.Ports
public meta import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Magmas
public meta import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Rings

@[expose] public section

/-!
# Commutative monoids (LC-13: the structure of `∑` and `∏` belongs to their category)

A sum `∑_{a ∈ A} f(a)` over a finite set `A` is the fold of a commutative monoid over `A`: the
value does not depend on an order of `A` because the operation is associative and commutative and
the empty sum is its unit (Bourbaki, *Algebra I*, I.1.5 and I.2.1; Mathlib `Finset.sum`,
`Finset.prod`). Its codomain is therefore an object of the category of commutative monoids,
written additively (`∑`, Mathlib `AddCommMonCat`) or multiplicatively (`∏`, Mathlib
`CommMonCat`), and the operation and unit are that object's.

* `CommMon → Mon` and `AddCommMon → AddMon` forget commutativity (Mathlib `forget₂`).
* A commutative ring is a commutative monoid under multiplication,
  `CommRing → CommMon` (Mathlib `forget₂ CommRingCat CommSemiRingCat ⋙ forget₂ CommSemiRingCat
  CommMonCat`). Its multiplicative monoid is then reached along two routes,
  `CommRing → Ring → Mon` and `CommRing → CommMon → Mon`, which are the same functor: the
  identity comparison is registered as an invertible cell (`commutativeRingsMonoidsCell`).
* A ring is a commutative monoid under addition, `Ring → AddCommMon` (Mathlib
  `forget₂ RingCat AddCommGrpCat ⋙ forget₂ AddCommGrpCat AddCommMonCat`). The registered additive
  port `Ring → AddGrp` forgets commutativity, and `AddGrp` has no registered route to `AddMon`, so
  the additive monoid of a ring is reached along this route alone.
-/

open CategoryTheory
open LeanCategories LeanCategories.Algebra

namespace CasCatalogue

namespace CategoryId
def commutativeMonoids : CategoryId := ⟨"cat.commutative_monoids"⟩
def additiveCommutativeMonoids : CategoryId := ⟨"cat.additive_commutative_monoids"⟩
end CategoryId

namespace FunctorId
def commutativeMonoidsMonoid : FunctorId := ⟨"fun.commutative_monoids.monoid"⟩
def additiveCommutativeMonoidsAdditiveMonoid : FunctorId :=
  ⟨"fun.additive_commutative_monoids.additive_monoid"⟩
def commutativeRingsMultiplicative : FunctorId :=
  ⟨"fun.commutative_rings.multiplicative_commutative_monoid"⟩
def ringsAdditiveCommutative : FunctorId := ⟨"fun.rings.additive_commutative_monoid"⟩
end FunctorId

namespace Algebra.CommMonoids

universe u

open CasCatalogue.Algebra.Catalogue.Magmas CasCatalogue.Algebra.Catalogue.Rings
open CasCatalogue.Algebra.CatalogueRegistration

def CommutativeMonoidsExpr : CategoryExpr := .atom CategoryId.commutativeMonoids
def AdditiveCommutativeMonoidsExpr : CategoryExpr := .atom CategoryId.additiveCommutativeMonoids

/-- Commutative monoids, written multiplicatively (Mathlib `CommMonCat`). -/
def CommutativeMonoids : ObjCat.{u + 1, u} := Cat.of CommMonCat.{u}

/-- Commutative monoids, written additively (Mathlib `AddCommMonCat`). -/
def AdditiveCommutativeMonoids : ObjCat.{u + 1, u} := Cat.of AddCommMonCat.{u}

noncomputable def commutativeMonoidsRealization :
    CategoryRealization CommutativeMonoidsExpr CommutativeMonoids.{u} := {}
noncomputable def additiveCommutativeMonoidsRealization :
    CategoryRealization AdditiveCommutativeMonoidsExpr AdditiveCommutativeMonoids.{u} := {}

/-- A commutative monoid as a `CommMonCat`, and its underlying set. -/
abbrev asCommMonoid (M : CommutativeMonoids.{0}) : CommMonCat.{0} := M
abbrev commMonoidCarrier (M : CommutativeMonoids.{0}) : Type := asCommMonoid M

/-- An additive commutative monoid as an `AddCommMonCat`, and its underlying set. -/
abbrev asAddCommMonoid (M : AdditiveCommutativeMonoids.{0}) : AddCommMonCat.{0} := M
abbrev addCommMonoidCarrier (M : AdditiveCommutativeMonoids.{0}) : Type := asAddCommMonoid M

def CommutativeMonoidsMonoidExpr : FunctorExpr CommutativeMonoidsExpr Monoids :=
  .atomic FunctorId.commutativeMonoidsMonoid
def AdditiveCommutativeMonoidsAdditiveMonoidExpr :
    FunctorExpr AdditiveCommutativeMonoidsExpr AdditiveMonoids :=
  .atomic FunctorId.additiveCommutativeMonoidsAdditiveMonoid
def CommutativeRingsMultiplicativeExpr : FunctorExpr CommutativeRings CommutativeMonoidsExpr :=
  .atomic FunctorId.commutativeRingsMultiplicative
def RingsAdditiveCommutativeExpr : FunctorExpr Rings AdditiveCommutativeMonoidsExpr :=
  .atomic FunctorId.ringsAdditiveCommutative

/-- The underlying monoid of a commutative monoid. -/
def commutativeMonoidsMonoid : CommutativeMonoids.{u} ⟶ Algebra.Monoids.{u} :=
  (forget₂ CommMonCat MonCat).toCatHom

/-- The underlying additive monoid of an additive commutative monoid. -/
def additiveCommutativeMonoidsAdditiveMonoid :
    AdditiveCommutativeMonoids.{u} ⟶ Algebra.AdditiveMonoids.{u} :=
  (forget₂ AddCommMonCat AddMonCat).toCatHom

/-- The multiplicative commutative monoid of a commutative ring. -/
def commutativeRingsMultiplicative : Algebra.CommutativeRings.{u} ⟶ CommutativeMonoids.{u} :=
  (forget₂ CommRingCat CommSemiRingCat ⋙ forget₂ CommSemiRingCat CommMonCat).toCatHom

/-- The additive commutative monoid of a ring. -/
def ringsAdditiveCommutative : Algebra.Rings.{u} ⟶ AdditiveCommutativeMonoids.{u} :=
  (forget₂ RingCat AddCommGrpCat ⋙ forget₂ AddCommGrpCat AddCommMonCat).toCatHom

noncomputable def commutativeMonoidsMonoidRealization :
    FunctorRealization CommutativeMonoidsMonoidExpr CommutativeMonoids.{u} Algebra.Monoids.{u}
      commutativeMonoidsMonoid.toFunctor :=
  { sourceRealization := commutativeMonoidsRealization, targetRealization := monoidsRealization }
noncomputable def additiveCommutativeMonoidsAdditiveMonoidRealization :
    FunctorRealization AdditiveCommutativeMonoidsAdditiveMonoidExpr
      AdditiveCommutativeMonoids.{u} Algebra.AdditiveMonoids.{u}
      additiveCommutativeMonoidsAdditiveMonoid.toFunctor :=
  { sourceRealization := additiveCommutativeMonoidsRealization
    targetRealization := additiveMonoidsRealization }
noncomputable def commutativeRingsMultiplicativeRealization :
    FunctorRealization CommutativeRingsMultiplicativeExpr Algebra.CommutativeRings.{u}
      CommutativeMonoids.{u} commutativeRingsMultiplicative.toFunctor :=
  { sourceRealization := commutativeRingsRealization
    targetRealization := commutativeMonoidsRealization }
noncomputable def ringsAdditiveCommutativeRealization :
    FunctorRealization RingsAdditiveCommutativeExpr Algebra.Rings.{u}
      AdditiveCommutativeMonoids.{u} ringsAdditiveCommutative.toFunctor :=
  { sourceRealization := ringsRealization
    targetRealization := additiveCommutativeMonoidsRealization }

/-- The two routes from commutative rings to monoids, through rings and through commutative
monoids, are the same functor: each sends `R` to its multiplicative monoid and a ring map to
itself. -/
def commutativeRingsMonoidsCell :
    (Algebras.commutativeRingsRings.{u} ≫ Ports.ringsMultiplicative.{u}).toFunctor ≅
      (commutativeRingsMultiplicative.{u} ≫ commutativeMonoidsMonoid.{u}).toFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Forgetting a ring through its additive monoid retains the same carrier and
functions as the existing multiplicative route. Only the set-valued composites
are compared; their additive and multiplicative operations stay distinct. -/
def ringsAdditiveMonoidCarrierCell :
    ringsAdditiveCommutative.{u}.toFunctor ⋙
      additiveCommutativeMonoidsAdditiveMonoid.{u}.toFunctor ⋙
      CatalogueRegistration.additiveMonoidsUnderlying.{u} ≅
        LeanCategories.Algebra.ringCarrierMultiplicative.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

end Algebra.CommMonoids

open Algebra.CommMonoids
open CasCatalogue.Algebra.Catalogue.Magmas CasCatalogue.Algebra.Catalogue.Rings

normalized_registry .category
  { id := CategoryId.commutativeMonoids, name := "CommutativeMonoids"
    declaration := `CasCatalogue.Algebra.CommMonoids.CommutativeMonoids
    expression := CommutativeMonoidsExpr
    realization := `CasCatalogue.Algebra.CommMonoids.commutativeMonoidsRealization }

normalized_registry .category
  { id := CategoryId.additiveCommutativeMonoids, name := "AdditiveCommutativeMonoids"
    declaration := `CasCatalogue.Algebra.CommMonoids.AdditiveCommutativeMonoids
    expression := AdditiveCommutativeMonoidsExpr
    realization :=
      `CasCatalogue.Algebra.CommMonoids.additiveCommutativeMonoidsRealization }

normalized_registry .functor
  { id := FunctorId.commutativeMonoidsMonoid, source := CommutativeMonoidsExpr, target := Monoids
    declaration := `CasCatalogue.Algebra.CommMonoids.commutativeMonoidsMonoid
    realization := `CasCatalogue.Algebra.CommMonoids.commutativeMonoidsMonoidRealization
    expression := CommutativeMonoidsMonoidExpr
    structural := true }

normalized_registry .functor
  { id := FunctorId.additiveCommutativeMonoidsAdditiveMonoid
    source := AdditiveCommutativeMonoidsExpr, target := AdditiveMonoids
    declaration :=
      `CasCatalogue.Algebra.CommMonoids.additiveCommutativeMonoidsAdditiveMonoid
    realization :=
      `CasCatalogue.Algebra.CommMonoids.additiveCommutativeMonoidsAdditiveMonoidRealization
    expression := AdditiveCommutativeMonoidsAdditiveMonoidExpr
    structural := true }

normalized_registry .functor
  { id := FunctorId.commutativeRingsMultiplicative, source := CommutativeRings
    target := CommutativeMonoidsExpr
    declaration := `CasCatalogue.Algebra.CommMonoids.commutativeRingsMultiplicative
    realization :=
      `CasCatalogue.Algebra.CommMonoids.commutativeRingsMultiplicativeRealization
    expression := CommutativeRingsMultiplicativeExpr
    structural := true }

normalized_registry .functor
  { id := FunctorId.ringsAdditiveCommutative, source := Rings
    target := AdditiveCommutativeMonoidsExpr
    declaration := `CasCatalogue.Algebra.CommMonoids.ringsAdditiveCommutative
    realization := `CasCatalogue.Algebra.CommMonoids.ringsAdditiveCommutativeRealization
    expression := RingsAdditiveCommutativeExpr
    structural := true }

normalized_registry .cell
  { id := ⟨"cell.commutative_rings.multiplicative_monoid"⟩, source := CommutativeRings
    target := Monoids
    left := #[.functor FunctorId.commutativeRingsRings, .functor FunctorId.ringsMultiplicative]
    right := #[.functor FunctorId.commutativeRingsMultiplicative,
      .functor FunctorId.commutativeMonoidsMonoid]
    declaration := `CasCatalogue.Algebra.CommMonoids.commutativeRingsMonoidsCell
    invertible := true }

normalized_registry .cell
  { id := ⟨"cell.rings.additive_monoid_carrier"⟩, source := Rings, target := Foundation.Sets
    left := #[.functor FunctorId.ringsAdditiveCommutative,
      .functor FunctorId.additiveCommutativeMonoidsAdditiveMonoid,
      .functor FunctorId.additiveMonoidsUnderlying]
    right := ringsToSets
    declaration := `CasCatalogue.Algebra.CommMonoids.ringsAdditiveMonoidCarrierCell
    invertible := true }

end CasCatalogue
