/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Ports
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Ports

@[expose] public section

/-!
# Addition of the selected additive monoid

Mathlib's `AddMonCat` retains the chosen additive monoid, and `AddGrpCat` has
its existing forgetful functor to it. These declarations expose that complete
binary addition and structural functor, with their ordinary preservation law.
No scalar ring or alternative structure on the same carrier is chosen.

The new additive-group route to sets is compared with the existing route
through `AddGrpCat.toGrp` by the identity natural isomorphism. That comparison
is only at sets: it does not identify addition with any multiplicative structure.

Sources: Mathlib `Algebra/Category/MonCat/Basic.lean` (`AddMonCat`, `map_add`),
`Algebra/Category/Grp/Basic.lean` (`forget₂ AddGrpCat AddMonCat`), and
`Algebra/Category/Grp/EquivalenceGroupAddGroup.lean` at
`db584cd6d46c92f209a44c0f1c829460d327499d`, Apache-2.0. The public source audit
found only ring and semiring `+` rows, and no additive-group to additive-monoid
structural row. This exposes the existing additive owner, not a new module
operation or a new addition law.

The 2026-10-24 public formalization-corpus query `"AddGrpCat" "AddMonCat"`
was followed by inspection of these pinned Mathlib declarations.
-/

open CategoryTheory

namespace CasCatalogue

namespace FunctorId
def additiveGroupsMonoid : FunctorId := ⟨"fun.additive_groups.additive_monoid"⟩
end FunctorId

namespace Algebra.AdditiveOperations

universe u

/-- The full binary addition of the selected additive monoid. -/
def add (M : AddMonCat.{u}) : (M × M : Type u) ⟶ (M : Type u) :=
  TypeCat.ofHom fun p => p.1 + p.2

/-- An additive homomorphism preserves this same selected operation. -/
theorem add_natural {M N : AddMonCat.{u}} (f : M ⟶ N) (a b : M) :
    f (add M (a, b)) = add N (f a, f b) := map_add f.hom a b

/-- Forgetting additive inverses retains the actual additive operation. -/
def additiveGroupsMonoid :
    LeanCategories.Algebra.AdditiveGroups.{u} ⥤
      LeanCategories.Algebra.AdditiveMonoids.{u} :=
  forget₂ AddGrpCat AddMonCat

def AdditiveGroupsMonoidExpr :
    FunctorExpr Catalogue.Magmas.AdditiveGroups Catalogue.Magmas.AdditiveMonoids :=
  .atomic FunctorId.additiveGroupsMonoid

noncomputable def additiveGroupsMonoidRealization :
    FunctorRealization AdditiveGroupsMonoidExpr
      LeanCategories.Algebra.AdditiveGroups.{u}
      LeanCategories.Algebra.AdditiveMonoids.{u} additiveGroupsMonoid :=
  { sourceRealization := CatalogueRegistration.additiveGroupsRealization
    targetRealization := CatalogueRegistration.additiveMonoidsRealization }

/-- The old and new additive-group carrier routes have the same functions.
The source of the comparison retains the preexisting route through groups. -/
def additiveGroupCarrierComparison :
    (Ports.additiveGroupsToGroups.toFunctor ⋙ forget GrpCat.{u}) ≅
    (additiveGroupsMonoid ⋙ CatalogueRegistration.additiveMonoidsUnderlying) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

end Algebra.AdditiveOperations

normalized_registry .functor
  { id := FunctorId.additiveGroupsMonoid
    source := Algebra.Catalogue.Magmas.AdditiveGroups
    target := Algebra.Catalogue.Magmas.AdditiveMonoids
    declaration := `CasCatalogue.Algebra.AdditiveOperations.additiveGroupsMonoid
    realization := `CasCatalogue.Algebra.AdditiveOperations.additiveGroupsMonoidRealization
    expression := Algebra.AdditiveOperations.AdditiveGroupsMonoidExpr
    structural := true }

normalized_registry .operation
  { id := ⟨"op.additive_monoids.add"⟩, category := CategoryId.additiveMonoids
    name := "+", arity := 2
    declaration := `CasCatalogue.Algebra.AdditiveOperations.add }

normalized_registry .cell
  { id := ⟨"cell.additive_groups.carrier"⟩
    source := Algebra.Catalogue.Magmas.AdditiveGroups, target := Foundation.Sets
    left := #[.functor FunctorId.additiveGroupsToGroups, .functor FunctorId.groupsMonoid,
      .functor FunctorId.monoidsSemigroup, .classifierForget ClassifierId.magmasAssociative,
      .classifierForget ClassifierId.setsBinaryOperation]
    right := #[.functor FunctorId.additiveGroupsMonoid,
      .functor FunctorId.additiveMonoidsUnderlying]
    declaration := `CasCatalogue.Algebra.AdditiveOperations.additiveGroupCarrierComparison
    invertible := true }

end CasCatalogue
