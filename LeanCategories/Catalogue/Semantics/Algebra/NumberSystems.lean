/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public import Mathlib.Data.Complex.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.EpiMono
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings

@[expose] public section

/-!
# The number systems `ℕ ⊆ ℤ ⊆ ℚ ⊆ ℝ ⊆ ℂ` (SPEC.md, "Exact number systems")

`ℝ` and `ℂ` are named sets whose numerals are `k ↦ k`, refined by the rings `ℝ` and `ℂ`. The
inclusions `ℕ ⊆ ℤ ⊆ ℚ ⊆ ℝ ⊆ ℂ` are the casts, monomorphisms of `Sets` because they are injective
(Mathlib `Nat.cast_injective`, `Int.cast_injective`, `Rat.cast_injective`,
`Complex.ofReal_injective`; `mono_iff_injective`).
-/

open CategoryTheory

namespace CasCatalogue.Algebra.NumberSystems

open CasCatalogue.Foundation.Objects CasCatalogue.Algebra.NamedRings

/-- `ℝ`. -/
abbrev reals : LeanCategories.Foundation.Mathlib.Sets.{0} := ℝ

/-- `ℂ`. -/
abbrev complexes : LeanCategories.Foundation.Mathlib.Sets.{0} := ℂ

/-- `k ∈ ℝ`. -/
noncomputable def realsElement (k : ℕ) : Option reals := some (k : ℝ)

/-- `k ∈ ℂ`. -/
noncomputable def complexesElement (k : ℕ) : Option complexes := some (k : ℂ)

/-- `ℝ` as a ring. -/
noncomputable abbrev ringReals : LeanCategories.Algebra.Rings.{0} := RingCat.of ℝ

/-- `ℂ` as a ring. -/
noncomputable abbrev ringComplexes : LeanCategories.Algebra.Rings.{0} := RingCat.of ℂ

def ringRealsIdentification : (reals : LeanCategories.Foundation.Mathlib.Sets.{0}) ≅ reals :=
  Iso.refl _

def ringComplexesIdentification :
    (complexes : LeanCategories.Foundation.Mathlib.Sets.{0}) ≅ complexes :=
  Iso.refl _

/-- A map of sets given by an injective function is a monomorphism. -/
theorem mono_of_injective {X Y : Type} (f : X → Y) (h : Function.Injective f) :
    Mono (TypeCat.ofHom f : (X : LeanCategories.Foundation.Mathlib.Sets.{0}) ⟶
      (Y : LeanCategories.Foundation.Mathlib.Sets.{0})) :=
  (mono_iff_injective (TypeCat.ofHom f : X ⟶ Y)).2 h

/-- `ℕ ⊆ ℤ`. -/
def naturalsIntegers : naturals ⟶ integers := TypeCat.ofHom (Nat.cast : ℕ → ℤ)
/-- `ℤ ⊆ ℚ`. -/
def integersRationals : integers ⟶ rationals := TypeCat.ofHom (Int.cast : ℤ → ℚ)
/-- `ℚ ⊆ ℝ`. -/
noncomputable def rationalsReals : rationals ⟶ reals := TypeCat.ofHom (Rat.cast : ℚ → ℝ)
/-- `ℝ ⊆ ℂ`. -/
noncomputable def realsComplexes : reals ⟶ complexes := TypeCat.ofHom (Complex.ofReal : ℝ → ℂ)

theorem naturalsIntegers_mono : Mono naturalsIntegers :=
  mono_of_injective _ Nat.cast_injective
theorem integersRationals_mono : Mono integersRationals :=
  mono_of_injective _ Int.cast_injective
theorem rationalsReals_mono : Mono rationalsReals :=
  mono_of_injective _ Rat.cast_injective
theorem realsComplexes_mono : Mono realsComplexes :=
  mono_of_injective _ Complex.ofReal_injective

end CasCatalogue.Algebra.NumberSystems

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.reals"⟩, category := CategoryId.sets, name := "ℝ"
    declaration := `CasCatalogue.Algebra.NumberSystems.reals }

normalized_registry .object
  { id := ⟨"obj.sets.complexes"⟩, category := CategoryId.sets, name := "ℂ"
    declaration := `CasCatalogue.Algebra.NumberSystems.complexes }

normalized_registry .elementLiteral
  { id := ⟨"elt.sets.reals"⟩, object := ⟨"obj.sets.reals"⟩
    denotation := `CasCatalogue.Algebra.NumberSystems.realsElement }

normalized_registry .elementLiteral
  { id := ⟨"elt.sets.complexes"⟩, object := ⟨"obj.sets.complexes"⟩
    denotation := `CasCatalogue.Algebra.NumberSystems.complexesElement }

normalized_registry .object
  { id := ⟨"obj.rings.reals"⟩, category := CategoryId.rings, name := "ℝ"
    declaration := `CasCatalogue.Algebra.NumberSystems.ringReals
    refines := some
      { base := ⟨"obj.sets.reals"⟩, route := ringsToSets
        identification := `CasCatalogue.Algebra.NumberSystems.ringRealsIdentification } }

normalized_registry .object
  { id := ⟨"obj.rings.complexes"⟩, category := CategoryId.rings, name := "ℂ"
    declaration := `CasCatalogue.Algebra.NumberSystems.ringComplexes
    refines := some
      { base := ⟨"obj.sets.complexes"⟩, route := ringsToSets
        identification := `CasCatalogue.Algebra.NumberSystems.ringComplexesIdentification } }

normalized_registry .inclusion
  { id := ⟨"incl.sets.naturals_integers"⟩, category := CategoryId.sets
    sub := ⟨"obj.sets.naturals"⟩, super := ⟨"obj.sets.integers"⟩
    declaration := `CasCatalogue.Algebra.NumberSystems.naturalsIntegers
    mono := `CasCatalogue.Algebra.NumberSystems.naturalsIntegers_mono }

normalized_registry .inclusion
  { id := ⟨"incl.sets.integers_rationals"⟩, category := CategoryId.sets
    sub := ⟨"obj.sets.integers"⟩, super := ⟨"obj.sets.rationals"⟩
    declaration := `CasCatalogue.Algebra.NumberSystems.integersRationals
    mono := `CasCatalogue.Algebra.NumberSystems.integersRationals_mono }

normalized_registry .inclusion
  { id := ⟨"incl.sets.rationals_reals"⟩, category := CategoryId.sets
    sub := ⟨"obj.sets.rationals"⟩, super := ⟨"obj.sets.reals"⟩
    declaration := `CasCatalogue.Algebra.NumberSystems.rationalsReals
    mono := `CasCatalogue.Algebra.NumberSystems.rationalsReals_mono }

normalized_registry .inclusion
  { id := ⟨"incl.sets.reals_complexes"⟩, category := CategoryId.sets
    sub := ⟨"obj.sets.reals"⟩, super := ⟨"obj.sets.complexes"⟩
    declaration := `CasCatalogue.Algebra.NumberSystems.realsComplexes
    mono := `CasCatalogue.Algebra.NumberSystems.realsComplexes_mono }

end CasCatalogue
