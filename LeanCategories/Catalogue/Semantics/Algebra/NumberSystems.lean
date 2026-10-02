/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.GCDMonoid.Nat
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

The positions `Fin n` and the residues `ℤ/n` are two objects, not one: `Fin n ↪ ℤ/n` sends the
position `k` to the numeral `k` of the ring `ℤ/n` (`finPoint_finIntegersMod`), and a position is an
element of `ℤ/n` only through this map, never because `ZMod n` is defined as `Fin n` for `n ≠ 0`.

Functions of elements, as named morphisms of `Sets`: `gcd : ℤ × ℤ → ℤ` (Mathlib `GCDMonoid.gcd`,
nonnegative), `re, im : ℂ → ℝ`, `bar : ℂ → ℂ` (conjugation), `abs : ℂ → ℝ` (`‖z‖`),
`sqrt : ℝ → ℝ` (`Real.sqrt`), and the element `i : 1 → ℂ`.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.NumberSystems

open CasCatalogue.Foundation.Objects CasCatalogue.Algebra.NamedRings

/-- `ℝ`. -/
abbrev reals : LeanCategories.Foundation.Mathlib.Sets.{0} := ℝ

/-- `ℂ`. -/
abbrev complexes : LeanCategories.Foundation.Mathlib.Sets.{0} := ℂ

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

/-- `Fin n ↪ ℤ/n`, the position `k < n` to the residue class of `k`: the image of `k` under the
initial ring map `ℤ → ℤ/n`. `Fin n`, the `n`-element set of positions, and `ℤ/n`, the set
underlying the ring `ℤ/n`, are different objects, related by this map and not identified: for
`n ≠ 0` it is a bijection (`ZMod.val` inverts it), and for `n = 0` it is `∅ ↪ ℤ`. -/
def finIntegersMod (n : ℕ) : fin n ⟶ integersMod n :=
  TypeCat.ofHom fun k => ((k : ℕ) : ZMod n)

/-- Distinct positions `j, k < n` are distinct residues: `j ≡ k mod n` forces `j = k`
(Mathlib `ZMod.natCast_eq_natCast_iff'`). -/
theorem finIntegersMod_mono (n : ℕ) : Mono (finIntegersMod n) :=
  mono_of_injective _ fun j k h => Fin.ext <| by
    have := (ZMod.natCast_eq_natCast_iff' j k n).mp h
    rwa [Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt k.2] at this

/-- The transport of the position `k` of `Fin n` into `ℤ/n` is the numeral `k` of the ring `ℤ/n`
(LC-15): `1 → Fin n ↪ ℤ/n` is `1 → ℤ/n`, `k ↦ k`. -/
theorem finPoint_finIntegersMod (n k : ℕ) (h : k < n) :
    Foundation.Morphisms.finPoint n k h ≫ finIntegersMod n = ringNumeral (ringIntegersMod n) k := by
  ext p
  simp [Foundation.Morphisms.finPoint, finIntegersMod, ringNumeral]

/-- `gcd : ℤ × ℤ → ℤ`. -/
def gcd : (integers × integers : LeanCategories.Foundation.Mathlib.Sets.{0}) ⟶ integers :=
  TypeCat.ofHom fun p => GCDMonoid.gcd p.1 p.2

/-- The real part `ℂ → ℝ`. -/
noncomputable def re : complexes ⟶ reals := TypeCat.ofHom Complex.re

/-- The imaginary part `ℂ → ℝ`. -/
noncomputable def im : complexes ⟶ reals := TypeCat.ofHom Complex.im

/-- Conjugation `ℂ → ℂ`. -/
noncomputable def bar : complexes ⟶ complexes := TypeCat.ofHom (starRingEnd ℂ)

/-- The absolute value `ℂ → ℝ`. -/
noncomputable def abs : complexes ⟶ reals := TypeCat.ofHom fun z => ‖z‖

/-- The square root `ℝ → ℝ` (`0` below `0`, Mathlib `Real.sqrt`). -/
noncomputable def sqrt : reals ⟶ reals := TypeCat.ofHom Real.sqrt

/-- The element `i ∈ ℂ`, `1 → ℂ`. -/
noncomputable def imaginaryUnit : fin 1 ⟶ complexes := TypeCat.ofHom fun _ => Complex.I

end CasCatalogue.Algebra.NumberSystems

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.reals"⟩, category := CategoryId.sets, name := "ℝ"
    declaration := `CasCatalogue.Algebra.NumberSystems.reals }

normalized_registry .object
  { id := ⟨"obj.sets.complexes"⟩, category := CategoryId.sets, name := "ℂ"
    declaration := `CasCatalogue.Algebra.NumberSystems.complexes }

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
  { id := ⟨"incl.sets.fin_integers_mod"⟩, category := CategoryId.sets
    sub := ⟨"obj.sets.fin"⟩, super := ⟨"obj.sets.integers_mod"⟩
    declaration := `CasCatalogue.Algebra.NumberSystems.finIntegersMod
    mono := `CasCatalogue.Algebra.NumberSystems.finIntegersMod_mono }

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

normalized_registry .morphism
  { id := ⟨"mor.sets.gcd"⟩, category := CategoryId.sets, name := "gcd"
    declaration := `CasCatalogue.Algebra.NumberSystems.gcd }

normalized_registry .morphism
  { id := ⟨"mor.sets.complex_re"⟩, category := CategoryId.sets, name := "re"
    declaration := `CasCatalogue.Algebra.NumberSystems.re }

normalized_registry .morphism
  { id := ⟨"mor.sets.complex_im"⟩, category := CategoryId.sets, name := "im"
    declaration := `CasCatalogue.Algebra.NumberSystems.im }

normalized_registry .morphism
  { id := ⟨"mor.sets.complex_bar"⟩, category := CategoryId.sets, name := "bar"
    declaration := `CasCatalogue.Algebra.NumberSystems.bar }

normalized_registry .morphism
  { id := ⟨"mor.sets.complex_abs"⟩, category := CategoryId.sets, name := "abs"
    declaration := `CasCatalogue.Algebra.NumberSystems.abs }

normalized_registry .morphism
  { id := ⟨"mor.sets.real_sqrt"⟩, category := CategoryId.sets, name := "sqrt"
    declaration := `CasCatalogue.Algebra.NumberSystems.sqrt }

normalized_registry .morphism
  { id := ⟨"mor.sets.complex_i"⟩, category := CategoryId.sets, name := "i"
    declaration := `CasCatalogue.Algebra.NumberSystems.imaginaryUnit }

end CasCatalogue
