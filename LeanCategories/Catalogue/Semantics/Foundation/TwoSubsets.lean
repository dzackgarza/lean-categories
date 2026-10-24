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

/-- For any set carrier `X : Type u`, the set of unordered finite subsets
`s : Finset X` satisfying `s.card = 2`, as Mathlib `Set.powersetCard X 2`.
Its elements have exactly two distinct members; ordering and repetitions add
no data. There is no finiteness hypothesis on `X`. `inclusion` forgets only
the cardinality condition, `singleton_not_member` excludes singletons, and
`card` gives `Nat.card X` choose two when `X` is finite. -/
abbrev twoSubsets (X : Type u) : Type u := Set.powersetCard X 2

/-- For an embedding `f : X ↪ Y`, the function from `twoSubsets X` to
`twoSubsets Y` taking a two-element subset to its direct image under `f`.
Injectivity preserves its cardinality, and `map_extent` states the exact
underlying-set equation `(map f s : Set Y) = f '' (s : Set X)`. -/
def map {X Y : Type u} (f : X ↪ Y) : twoSubsets X → twoSubsets Y :=
  Set.powersetCard.map 2 f

/-- For `X : Type`, the inclusion `twoSubsets X → Finset X` sending
`⟨s, hs : s.card = 2⟩` to the same finite subset `s`. Its target is the
existing `FiniteSubsets.finiteSubsets X`; `inclusion_mono` proves monicity. -/
def inclusion (X : Type) : twoSubsets X ⟶ FiniteSubsets.finiteSubsets X :=
  TypeCat.ofHom Subtype.val

instance inclusion_mono (X : Type) : Mono (inclusion X) :=
  (CategoryTheory.mono_iff_injective _).mpr Subtype.val_injective

/-- The functor `Core (Type u) ⥤ Type u` sending a selected set `X` to its
unordered two-element subsets. An arrow of the source is a specified
bijection `f : X ≅ Y`; its action sends each subset `s` to the direct image
`f '' s`, using `map` and the bijection's underlying embedding.
`map_extent` gives the action on the complete subset. This is also the
object assignment of the public `two_subsets` method; its morphism action
is defined on bijections, as required by the source category `Core(Sets)`. -/
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

/-- Realization of the two-subset functor from `Core(Sets)` to `Sets`, with
the complete object and bijection actions given by `onCore`. -/
noncomputable def realization :
    FunctorRealization expression coreSetsCategory.{u}
      LeanCategories.Foundation.Mathlib.Sets.{u} onCore :=
  { sourceRealization := coreSetsRealization
    targetRealization := Foundation.CatalogueRegistration.setsRealization }

/-- The selected set `X` viewed as an object of `Core(Sets)`, keeping its
carrier unchanged so that only bijections are available as arrows. -/
def argument (X : Type) : coreSetsCategory.{0} := ⟨X⟩
/-- The identity comparison between `onCore` applied to the selected set `X`
and `twoSubsets X`; each two-element subset is preserved in both directions. -/
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
