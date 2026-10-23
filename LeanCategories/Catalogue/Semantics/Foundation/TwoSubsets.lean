/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsets
public import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public import Mathlib.Data.Set.PowersetCard
public import Mathlib.Tactic.NormNum
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue

@[expose] public section

/-!
# Two-element subsets

The owner is Mathlib `Set.powersetCard X 2`, finite subsets with exactly two
members, rather than ordered pairs or multisets. Mathlib's
`Set.powersetCard.map` acts on embeddings. Restricting that action to
bijections gives the registered functor on `Core(Sets)`; arbitrary set maps
are deliberately outside its domain. The cardinality theorem is Mathlib
`Set.powersetCard.card`, specialized to two.
-/

open CategoryTheory

namespace CasCatalogue.Foundation.TwoSubsets

open CasCatalogue.Foundation.PowerSets
open CasCatalogue.Catalogue.ConstructorRegistration

universe u

/-- The set of unordered subsets with exactly two distinct members. -/
abbrev twoSubsets (X : Type u) : Type u := Set.powersetCard X 2

/-- Direct image along an injection preserves the two-element condition. -/
def map {X Y : Type u} (f : X ↪ Y) : twoSubsets X → twoSubsets Y :=
  Set.powersetCard.map 2 f

/-- Inclusion into the previously registered finite-subset object. -/
def inclusion (X : Type) : twoSubsets X ⟶ FiniteSubsets.finiteSubsets X :=
  TypeCat.ofHom Subtype.val

instance inclusion_mono (X : Type) : Mono (inclusion X) :=
  (CategoryTheory.mono_iff_injective _).mpr Subtype.val_injective

/-- The original input set is retained; only bijections act on it here. -/
def onCore : Core (Type u) ⥤ Type u where
  obj X := twoSubsets X.of
  map f := TypeCat.ofHom (map f.iso.toEquiv.toEmbedding)
  map_id X := by
    ext s : 3
    apply Subtype.ext
    change Finset.map _ s.1 = s.1
    simp
  map_comp f g := by
    ext s : 3
    apply Subtype.ext
    change Finset.map _ s.1 = Finset.map _ (Finset.map _ s.1)
    rw [Finset.map_map]
    rfl

theorem map_extent {X Y : Type u} (f : X ↪ Y) (s : twoSubsets X) :
    ((map f s : twoSubsets Y) : Set Y) = f '' (s : Set X) :=
  Set.powersetCard.coe_map 2 f s

theorem card [Finite X] : Nat.card (twoSubsets X) = (Nat.card X).choose 2 :=
  Set.powersetCard.card X 2

theorem fin_five_card : Nat.card (twoSubsets (Fin 5)) = 10 := by
  rw [card]
  norm_num [Nat.choose]

theorem fin_five_cardinal : Cardinal.mk (twoSubsets (Fin 5)) = 10 := by
  rw [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card, fin_five_card]
  norm_num

/-- No singleton, including a repeated pair, belongs to this object. -/
theorem singleton_not_member (X : Type u) (x : X) :
    ({x} : Finset X) ∉ Set.powersetCard X 2 := by
  simp

def functorId : FunctorId := ⟨"fun.core_sets.two_subsets"⟩
def expression : FunctorExpr Constructed.CoreSets Foundation.Sets := .atomic functorId

noncomputable def realization :
    FunctorRealization expression coreSetsCategory.{u}
      LeanCategories.Foundation.Mathlib.Sets.{u} onCore :=
  { sourceRealization := coreSetsRealization
    targetRealization := Foundation.CatalogueRegistration.setsRealization }

def argument (X : Type) : coreSetsCategory.{0} := ⟨X⟩
def identification (X : Type) : onCore.obj (argument X) ≅ twoSubsets X := Iso.refl _

end CasCatalogue.Foundation.TwoSubsets

namespace CasCatalogue

normalized_registry .functor
  { id := Foundation.TwoSubsets.functorId, source := Constructed.CoreSets
    target := Foundation.Sets, declaration := `CasCatalogue.Foundation.TwoSubsets.onCore
    realization := `CasCatalogue.Foundation.TwoSubsets.realization
    expression := Foundation.TwoSubsets.expression }

normalized_registry .object
  { id := ⟨"obj.sets.two_subsets"⟩, category := CategoryId.sets, name := "TwoSubsets"
    declaration := `CasCatalogue.Foundation.TwoSubsets.twoSubsets
    inclusion := some `CasCatalogue.Foundation.TwoSubsets.inclusion
    functorPresentation := some
      { functor := Foundation.TwoSubsets.functorId
        argument := `CasCatalogue.Foundation.TwoSubsets.argument
        identification := `CasCatalogue.Foundation.TwoSubsets.identification } }

normalized_registry .method
  { id := ⟨"meth.two_subsets"⟩, name := "two_subsets", owner := Foundation.Sets
    functor := Foundation.TwoSubsets.functorId, shape := .isoInvariant }

end CasCatalogue
