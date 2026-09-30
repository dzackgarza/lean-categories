/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.PortComparison
public import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Rat.Defs
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Ports

@[expose] public section

/-!
# The named rings and the ring operations on their elements (SPEC.md, "Exact number systems")

* `ℚ` is a named set (`obj.sets.rationals`) whose numerals are `k ↦ k`.
* `ℤ`, `ℤ/n` (`ZMod`) and `ℚ` in `Rings` refine the named sets `ℤ`, `ℤ/n` and `ℚ` along the
  multiplicative route to `Sets` (the ring diamond is identified at sets by `cmp.rings.carrier`):
  their underlying sets are those sets (`Iso.refl`).
* The element operations of `Rings`: `+` and `·` (`R × R → R`), `-` and `^k` (`R → R`), natural
  in the ring, as morphisms of `Sets`. Their laws are Mathlib's (`RingCat`).
-/

open CategoryTheory

namespace CasCatalogue.Algebra.NamedRings

open CasCatalogue.Foundation.Objects

/-- `ℚ`. -/
abbrev rationals : LeanCategories.Foundation.Mathlib.Sets.{0} := ℚ

/-- `ℤ` as a ring. -/
abbrev ringIntegers : LeanCategories.Algebra.Rings.{0} := RingCat.of ℤ

/-- `ℤ/n` as a ring. -/
abbrev ringIntegersMod (n : ℕ) : LeanCategories.Algebra.Rings.{0} := RingCat.of (ZMod n)

/-- `ℚ` as a ring. -/
abbrev ringRationals : LeanCategories.Algebra.Rings.{0} := RingCat.of ℚ

/-- The underlying set of the ring `ℤ` is `ℤ`. -/
def ringIntegersIdentification : (integers : LeanCategories.Foundation.Mathlib.Sets.{0}) ≅ integers :=
  Iso.refl _

/-- The underlying set of the ring `ℤ/n` is `ℤ/n`. -/
def ringIntegersModIdentification (n : ℕ) :
    (integersMod n : LeanCategories.Foundation.Mathlib.Sets.{0}) ≅ integersMod n :=
  Iso.refl _

/-- The underlying set of the ring `ℚ` is `ℚ`. -/
def ringRationalsIdentification : (rationals : LeanCategories.Foundation.Mathlib.Sets.{0}) ≅ rationals :=
  Iso.refl _

/-- An object of `Rings` as a `RingCat`. -/
abbrev asRing (R : LeanCategories.Algebra.Rings.{0}) : RingCat.{0} := R

/-- The set underlying a ring. -/
abbrev underlying (R : LeanCategories.Algebra.Rings.{0}) : Type := asRing R

/-- Addition, `R × R → R`. -/
def add (R : LeanCategories.Algebra.Rings.{0}) :
    (underlying R × underlying R : LeanCategories.Foundation.Mathlib.Sets.{0}) ⟶
      (underlying R : LeanCategories.Foundation.Mathlib.Sets.{0}) :=
  TypeCat.ofHom fun p => p.1 + p.2

/-- Multiplication, `R × R → R`. -/
def mul (R : LeanCategories.Algebra.Rings.{0}) :
    (underlying R × underlying R : LeanCategories.Foundation.Mathlib.Sets.{0}) ⟶
      (underlying R : LeanCategories.Foundation.Mathlib.Sets.{0}) :=
  TypeCat.ofHom fun p => p.1 * p.2

/-- Negation, `R → R`. -/
def neg (R : LeanCategories.Algebra.Rings.{0}) :
    (underlying R : LeanCategories.Foundation.Mathlib.Sets.{0}) ⟶
      (underlying R : LeanCategories.Foundation.Mathlib.Sets.{0}) :=
  TypeCat.ofHom fun x => -x

/-- The numeral `k` of a ring `R`: the image of `k ∈ ℕ ⊆ ℤ` under the unique ring map `ℤ → R` out
of the initial ring (Mathlib `Int.castRingHom`), LC-15. -/
def ringNumeral (R : LeanCategories.Algebra.Rings.{0}) (k : ℕ) :
    fin 1 ⟶ (underlying R : LeanCategories.Foundation.Mathlib.Sets.{0}) :=
  TypeCat.ofHom fun _ => Int.castRingHom (asRing R) (k : ℤ)

/-- The power `x ↦ x^k`, `R → R`. -/
def pow (R : LeanCategories.Algebra.Rings.{0}) (k : ℕ) :
    (underlying R : LeanCategories.Foundation.Mathlib.Sets.{0}) ⟶
      (underlying R : LeanCategories.Foundation.Mathlib.Sets.{0}) :=
  TypeCat.ofHom fun x => x ^ k

end CasCatalogue.Algebra.NamedRings

namespace CasCatalogue

open CasCatalogue.Algebra.Catalogue.Rings

normalized_registry .object
  { id := ⟨"obj.sets.rationals"⟩, category := CategoryId.sets, name := "ℚ"
    declaration := `CasCatalogue.Algebra.NamedRings.rationals }

normalized_registry .numeral
  { id := ⟨"num.rings"⟩, over := some CategoryId.rings
    declaration := `CasCatalogue.Algebra.NamedRings.ringNumeral }

/-- The multiplicative route from rings to sets, which `cmp.rings.carrier` designates. -/
meta def ringsToSets : Array EdgeRef :=
  #[.functor FunctorId.ringsMultiplicative, .functor FunctorId.monoidsSemigroup,
    .classifierForget ClassifierId.magmasAssociative,
    .classifierForget ClassifierId.setsBinaryOperation]

normalized_registry .object
  { id := ⟨"obj.rings.integers"⟩, category := CategoryId.rings, name := "ℤ"
    declaration := `CasCatalogue.Algebra.NamedRings.ringIntegers
    refines := some
      { base := ⟨"obj.sets.integers"⟩, route := ringsToSets
        identification := `CasCatalogue.Algebra.NamedRings.ringIntegersIdentification } }

normalized_registry .object
  { id := ⟨"obj.rings.integers_mod"⟩, category := CategoryId.rings, name := "ZMod"
    declaration := `CasCatalogue.Algebra.NamedRings.ringIntegersMod
    refines := some
      { base := ⟨"obj.sets.integers_mod"⟩, route := ringsToSets
        identification := `CasCatalogue.Algebra.NamedRings.ringIntegersModIdentification } }

normalized_registry .object
  { id := ⟨"obj.rings.rationals"⟩, category := CategoryId.rings, name := "ℚ"
    declaration := `CasCatalogue.Algebra.NamedRings.ringRationals
    refines := some
      { base := ⟨"obj.sets.rationals"⟩, route := ringsToSets
        identification := `CasCatalogue.Algebra.NamedRings.ringRationalsIdentification } }

normalized_registry .operation
  { id := ⟨"op.rings.add"⟩, category := CategoryId.rings, name := "+", arity := 2
    declaration := `CasCatalogue.Algebra.NamedRings.add }

normalized_registry .operation
  { id := ⟨"op.rings.mul"⟩, category := CategoryId.rings, name := "·", arity := 2
    declaration := `CasCatalogue.Algebra.NamedRings.mul }

normalized_registry .operation
  { id := ⟨"op.rings.pow"⟩, category := CategoryId.rings, name := "^", arity := 1, numerals := 1
    declaration := `CasCatalogue.Algebra.NamedRings.pow }

normalized_registry .operation
  { id := ⟨"op.rings.neg"⟩, category := CategoryId.rings, name := "-", arity := 1
    declaration := `CasCatalogue.Algebra.NamedRings.neg }

end CasCatalogue
