/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Division (SPEC.md, "Exact number systems": fractions)

Division is not total: `a / b` is defined for `b ≠ 0`. For a division ring `K` of characteristic
zero (`ℚ`, `ℝ`, `ℂ`):
* `K∖{0}` is the set of its nonzero elements, whose numerals are the nonzero `k ↦ k` (the numeral
  `0` names none);
* `/ : K × K∖{0} → K` is division (Mathlib `DivisionRing`), defined on its whole domain; Lean's
  total `x / 0 = 0` is not in its image of definitions.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.Fractions

open CasCatalogue.Foundation.PowerSets

/-- `K∖{0}`. -/
abbrev nonzero (K : Type) [DivisionRing K] [CharZero K] : SetsCat.{0} := {x : K // x ≠ 0}

/-- The numeral `k ∈ K∖{0}`, for `k ≠ 0`. -/
def nonzeroElement (K : Type) [DivisionRing K] [CharZero K] (k : ℕ) : Option (nonzero K) :=
  if h : k = 0 then none else some ⟨k, Nat.cast_ne_zero.mpr h⟩

/-- `a / b` for `b ≠ 0`. -/
def divide (K : Type) [DivisionRing K] [CharZero K] :
    (K × nonzero K : SetsCat.{0}) ⟶ (K : SetsCat.{0}) :=
  TypeCat.ofHom fun p => p.1 / p.2.1

end CasCatalogue.Algebra.Fractions

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.nonzero"⟩, category := CategoryId.sets, name := "nonzero"
    declaration := `CasCatalogue.Algebra.Fractions.nonzero }

normalized_registry .elementLiteral
  { id := ⟨"elt.sets.nonzero"⟩, object := ⟨"obj.sets.nonzero"⟩
    denotation := `CasCatalogue.Algebra.Fractions.nonzeroElement }

normalized_registry .morphism
  { id := ⟨"mor.sets.divide"⟩, category := CategoryId.sets, name := "/"
    declaration := `CasCatalogue.Algebra.Fractions.divide }

end CasCatalogue
