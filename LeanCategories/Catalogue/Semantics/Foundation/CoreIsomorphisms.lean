/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
public import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public import Mathlib.Data.Fin.Rev
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue

@[expose] public section

/-!
# Specified set isomorphisms as arrows of the core

The core of `Sets` keeps complete specified bijections. Mathlib `CoreHom.mk`
places an isomorphism in that category, retaining both arrows and their inverse
laws. `setsIso` publishes this construction for every pair of sets.

The existing finite-ordinal reversal is Mathlib `Fin.rev`. Its already proved
involution `Fin.revPerm` supplies a complete isomorphism for every `Fin n`,
including the empty set. The public comparison and core arrow below use this
same isomorphism. They do not replace `Fin n` or the original set map `rev(n)`.

Sources: Mathlib `CategoryTheory.CoreHom`, `Equiv.toIso`, `Fin.revPerm`, and
`Fin.rev_involutive`; the existing `Foundation.Morphisms.finRev`.
-/

open CategoryTheory

namespace CasCatalogue.Foundation.CoreIsomorphisms

open Objects

universe u

/-- For arbitrary selected sets `X`, `Y` and a specified isomorphism `e : X ≅ Y`,
the arrow `Core.mk X ⟶ Core.mk Y` carrying exactly `e`. Its forward function,
inverse function, and inverse equations are all retained by `CoreHom.mk`. -/
def setsIso (X Y : Type u) (e : X ≅ Y) : Core.mk X ⟶ Core.mk Y :=
  CoreHom.mk e

/-- The complete reversal isomorphism of the original `Fin n`.
Both directions are the existing map `Morphisms.finRev n`, sending
`k` to `n - 1 - k`; the two inverse laws are `Fin.rev_involutive`.
This declaration is valid for every natural `n`, including zero. -/
def finRevIso (n : ℕ) : fin n ≅ fin n := Fin.revPerm.toIso

/-- The specified reversal of `Fin n`, now as an arrow of `Core(Sets)`.
It is `setsIso (Fin n) (Fin n) (finRevIso n)`, so both directions of the
accepted isomorphism are present. Any functor on `Core(Sets)` may act on it. -/
def finRevCore (n : ℕ) : Core.mk (fin n) ⟶ Core.mk (fin n) :=
  setsIso (fin n) (fin n) (finRevIso n)

theorem finRevIso_hom (n : ℕ) : (finRevIso n).hom = Morphisms.finRev n := rfl

theorem finRevIso_inv (n : ℕ) : (finRevIso n).inv = Morphisms.finRev n := rfl

theorem finRevCore_hom (n : ℕ) : (finRevCore n).iso.hom = Morphisms.finRev n := rfl

theorem finRevCore_inv (n : ℕ) : (finRevCore n).iso.inv = Morphisms.finRev n := rfl

/-- The two retained directions make reversal an involution in the core itself. -/
theorem finRevCore_comp (n : ℕ) : finRevCore n ≫ finRevCore n = 𝟙 (Core.mk (fin n)) := by
  apply Core.hom_ext
  exact (finRevIso n).hom_inv_id

end CasCatalogue.Foundation.CoreIsomorphisms

namespace CasCatalogue

normalized_registry .morphism
  { id := ⟨"mor.core_sets.specified_iso"⟩, category := CategoryId.coreSets
    name := "core_iso"
    declaration := `CasCatalogue.Foundation.CoreIsomorphisms.setsIso }

normalized_registry .presentation
  { id := ⟨"cmp.sets.fin_reversal"⟩, name := "fin_reversal"
    source := ⟨"obj.sets.fin"⟩, target := ⟨"obj.sets.fin"⟩
    declaration := `CasCatalogue.Foundation.CoreIsomorphisms.finRevIso }

normalized_registry .morphism
  { id := ⟨"mor.core_sets.fin_rev"⟩, category := CategoryId.coreSets
    name := "core_rev"
    declaration := `CasCatalogue.Foundation.CoreIsomorphisms.finRevCore }

end CasCatalogue
