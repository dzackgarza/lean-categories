/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Units (LC-14: inverses exist on units, not on a monoid)

A monoid `M` has no inverses in general; its units `Mˣ` (Mathlib `Units`, the units functor
`Mon → Grp`) form a group, and `⁻¹` is part of that group's structure: an operation on `Mˣ`, never
on `M`. The endomorphisms `Matₙ(K) = End(Kⁿ)` form a monoid; their units are the automorphisms
`GLₙ(K) = Aut(Kⁿ) = Matₙ(K)ˣ`; the units of a field `K` are `K^× = K ∖ {0}`.

* `Mˣ ↪ M` (`Units.val`) is a monomorphism: a unit is an element of `M`.
* An element `x ∈ M` is a unit only with the evidence `IsUnit x` (the admission); without it, it
  is not an element of `Mˣ`, and `x⁻¹` is not a term.
* `⁻¹ : Mˣ → Mˣ`, and division `M × Mˣ → M`, `(a, u) ↦ a u⁻¹`.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.Units

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- `Mˣ`. -/
abbrev units (M : Type) [Monoid M] : SetsCat.{0} := Mˣ

/-- `Mˣ ↪ M`. -/
def inclusion (M : Type) [Monoid M] : units M ⟶ (M : SetsCat.{0}) := TypeCat.ofHom Units.val

/-- The unit `x`, with the evidence that `x` is a unit. -/
noncomputable def admit (M : Type) [Monoid M] (x : M) (h : IsUnit x) : fin 1 ⟶ units M :=
  TypeCat.ofHom fun _ => h.unit

/-- `u ↦ u⁻¹`, the inverse of the group `Mˣ`. -/
def inverse (M : Type) [Monoid M] : units M ⟶ units M := TypeCat.ofHom fun u => u⁻¹

/-- `(a, u) ↦ a u⁻¹`. -/
def divide (M : Type) [Monoid M] : (M × units M : SetsCat.{0}) ⟶ (M : SetsCat.{0}) :=
  TypeCat.ofHom fun p => p.1 * ↑(p.2⁻¹)

end CasCatalogue.Algebra.Units

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.units"⟩, category := CategoryId.sets, name := "Units"
    declaration := `CasCatalogue.Algebra.Units.units
    inclusion := some `CasCatalogue.Algebra.Units.inclusion
    admission := some `CasCatalogue.Algebra.Units.admit }

normalized_registry .morphism
  { id := ⟨"mor.sets.units_inverse"⟩, category := CategoryId.sets, name := "⁻¹"
    declaration := `CasCatalogue.Algebra.Units.inverse }

normalized_registry .morphism
  { id := ⟨"mor.sets.divide"⟩, category := CategoryId.sets, name := "/"
    declaration := `CasCatalogue.Algebra.Units.divide }

end CasCatalogue
