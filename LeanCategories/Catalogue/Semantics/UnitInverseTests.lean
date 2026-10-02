/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Units
public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public import LeanCategories.Catalogue.Semantics.Limits.Registration
public import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
public meta import LeanCategories.Catalogue.Semantics.Algebra.Units

@[expose] public section

/-!
# Decided equations between inverses of admitted units

A unit is admitted into `Mˣ` with the evidence `Invertible x` that the registered evidence of
`obj.sets.units` (`Units.invertibleEvidence`) establishes, run here as a consumer runs it
(`run_tac`). The admitted unit keeps its inverse as data, so an equation between elements formed
from it, through the registered `⁻¹ : Mˣ → Mˣ`, `Mˣ ↪ M` and `/ : M × Mˣ → M`, is decided by
`decide +kernel`: the kernel reduces both sides to values of `M` and compares them.

The pair `(a, u) : 1 → M × Mˣ` is the mediator of the registered product cone `lim.sets.product`,
and the numeral `1` of `ℚ` is `ringNumeral` (the image of `1` under the ring map out of `ℤ`).
-/

namespace CasCatalogue.UnitInverseTests

open CategoryTheory Limits
open CasCatalogue.Algebra.Units CasCatalogue.Algebra.NamedRings
open CasCatalogue.Limits.Registration CasCatalogue.Foundation.Objects
open CasCatalogue.Foundation.Morphisms CasCatalogue.Algebra.NumberSystems

/-- The element `u⁻¹ ∈ M` of a unit `u : 1 → Mˣ`: `1 → Mˣ → Mˣ ↪ M`. -/
abbrev inverseElement (M : Type) [Monoid M] (u : fin 1 ⟶ units (MonCat.of M)) :
    fin 1 ⟶ (M : LeanCategories.Foundation.Mathlib.Sets.{0}) :=
  u ≫ inverse (MonCat.of M) ≫ inclusion (MonCat.of M)

/-- The element `a / u ∈ M`: the pair `(a, u)`, the mediator of the registered product cone,
followed by `/ : M × Mˣ → M`. -/
abbrev divideElement (M : Type) [Monoid M]
    (a : fin 1 ⟶ (M : LeanCategories.Foundation.Mathlib.Sets.{0})) (u : fin 1 ⟶ units (MonCat.of M)) :
    fin 1 ⟶ (M : LeanCategories.Foundation.Mathlib.Sets.{0}) :=
  (setsProduct _ _).isLimit.lift (BinaryFan.mk a u) ≫ divide (MonCat.of M)

/-- The element `c ∈ M` of a value `c`. -/
abbrev element {M : Type} (c : M) : fin 1 ⟶ (M : LeanCategories.Foundation.Mathlib.Sets.{0}) :=
  TypeCat.ofHom fun _ => c

/-- `3⁻¹ = 1/3` in `ℚ`, the inverse of the unit `3 ∈ ℚˣ`. -/
example : inverseElement ℚ (admit (MonCat.of ℚ) 3 (by run_tac invertibleEvidence)) = element (1 / 3 : ℚ) := by
  decide +kernel

/-- `1 / 3 = 1/3` in `ℚ`: the numeral `1` divided by the unit `3 ∈ ℚˣ`. -/
example : divideElement ℚ (ringNumeral ringRationals 1)
    (admit (MonCat.of ℚ) 3 (by run_tac invertibleEvidence)) = element (1 / 3 : ℚ) := by
  decide +kernel

/-- `3⁻¹ ≠ 1/2` in `ℚ`. -/
example :
    inverseElement ℚ (admit (MonCat.of ℚ) 3 (by run_tac invertibleEvidence)) ≠ element (1 / 2 : ℚ) := by
  decide +kernel

/-- `1 / 3 ≠ 3` in `ℚ`. -/
example : divideElement ℚ (ringNumeral ringRationals 1)
    (admit (MonCat.of ℚ) 3 (by run_tac invertibleEvidence)) ≠ element (3 : ℚ) := by
  decide +kernel

/-- `(-3/4)⁻¹ = -4/3` in `ℚ`. -/
example :
    inverseElement ℚ (admit (MonCat.of ℚ) (-3 / 4) (by run_tac invertibleEvidence)) = element (-4 / 3 : ℚ) := by
  decide +kernel

/-- `2⁻¹ = 3` in `ℤ/5`. -/
example : inverseElement (ZMod 5) (admit (MonCat.of (ZMod 5)) 2 (by run_tac invertibleEvidence)) =
    element (3 : ZMod 5) := by
  decide +kernel

/-- `2⁻¹ ≠ 2` in `ℤ/5`. -/
example : inverseElement (ZMod 5) (admit (MonCat.of (ZMod 5)) 2 (by run_tac invertibleEvidence)) ≠
    element (2 : ZMod 5) := by
  decide +kernel

/-- `7⁻¹ = 7` in `ℤ/12` (`7 · 7 = 49 = 4 · 12 + 1`). -/
example : inverseElement (ZMod 12) (admit (MonCat.of (ZMod 12)) 7 (by run_tac invertibleEvidence)) =
    element (7 : ZMod 12) := by
  decide +kernel

/-- `(-1)⁻¹ = -1` in `ℤ`, whose units are `±1`. -/
example : inverseElement ℤ (admit (MonCat.of ℤ) (-1) (by run_tac invertibleEvidence)) = element (-1 : ℤ) := by
  decide +kernel

/-- `1⁻¹ = 1` in `ℤ`. -/
example : inverseElement ℤ (admit (MonCat.of ℤ) 1 (by run_tac invertibleEvidence)) = element (1 : ℤ) := by
  decide +kernel

/-- `(2 · 4)⁻¹ = 4⁻¹ · 2⁻¹ = 2 · 5 = 1` in `ℤ/7`, through the inverse of a product. -/
example : inverseElement (ZMod 7) (admit (MonCat.of (ZMod 7)) (2 * 4) (by run_tac invertibleEvidence)) =
    element (1 : ZMod 7) := by
  decide +kernel

/-! ## The numerals of `ℤ/n`

The numeral `k ∈ ℤ/n` is `ringNumeral (ringIntegersMod n) k`, the image of `k` under the initial
ring map `ℤ → ℤ/n` (LC-15). A position `k` of `Fin n` names an element of `ℤ/n` only through
`Fin n ↪ ℤ/n` (`finIntegersMod`), which carries it to the numeral `k`
(`finPoint_finIntegersMod`). -/

/-- The numeral `k` of `ℤ/n`, an element `1 → ℤ/n`. -/
abbrev zmodNumeral (n k : ℕ) : fin 1 ⟶ integersMod n := ringNumeral (ringIntegersMod n) k

/-- The value in `ℤ/n` of the numeral `k`, at the point of `1`. -/
abbrev zmodNumeralValue (n k : ℕ) : integersMod n :=
  ConcreteCategory.hom (C := Type) (zmodNumeral n k) ⟨0, Nat.one_pos⟩

/-- `2⁻¹ = 3` in `ℤ/5` (`2 · 3 = 6 = 5 + 1`), at the numerals of `ℤ/5`. -/
example : inverseElement (ZMod 5)
    (admit (MonCat.of (ZMod 5)) (zmodNumeralValue 5 2) (by run_tac invertibleEvidence)) =
      zmodNumeral 5 3 := by
  decide +kernel

/-- `2⁻¹ ≠ 2` in `ℤ/5`, at the numerals. -/
example : inverseElement (ZMod 5)
    (admit (MonCat.of (ZMod 5)) (zmodNumeralValue 5 2) (by run_tac invertibleEvidence)) ≠
      zmodNumeral 5 2 := by
  decide +kernel

/-- `7⁻¹ = 7` in `ℤ/12` (`7 · 7 = 49 = 4 · 12 + 1`), at the numerals. -/
example : inverseElement (ZMod 12)
    (admit (MonCat.of (ZMod 12)) (zmodNumeralValue 12 7) (by run_tac invertibleEvidence)) =
      zmodNumeral 12 7 := by
  decide +kernel

/-- `1 / 7 = 7` in `ℤ/12`: the numeral `1` divided by the unit `7`. -/
example : divideElement (ZMod 12) (zmodNumeral 12 1)
    (admit (MonCat.of (ZMod 12)) (zmodNumeralValue 12 7) (by run_tac invertibleEvidence)) =
      zmodNumeral 12 7 := by
  decide +kernel

/-- `12⁻¹ = 3` in `ℤ/7`: the numeral `12` is `5`, and `5 · 3 = 15 = 2 · 7 + 1`. -/
example : inverseElement (ZMod 7)
    (admit (MonCat.of (ZMod 7)) (zmodNumeralValue 7 12) (by run_tac invertibleEvidence)) =
      zmodNumeral 7 3 := by
  decide +kernel

/-- The position `2` of `Fin 5`, carried into `ℤ/5` by `Fin 5 ↪ ℤ/5`, has inverse the numeral
`3`: the transport makes it the numeral `2`. -/
example : inverseElement (ZMod 5)
    (admit (MonCat.of (ZMod 5))
      (ConcreteCategory.hom (C := Type) (finPoint 5 2 (by decide) ≫ finIntegersMod 5)
        ⟨0, Nat.one_pos⟩) (by run_tac invertibleEvidence)) =
      zmodNumeral 5 3 := by
  decide +kernel

/-- The transport of the position `k` is the numeral `k`, so admitting either gives the same
unit of `ℤ/5`. -/
example : finPoint 5 2 (by decide) ≫ finIntegersMod 5 = zmodNumeral 5 2 :=
  finPoint_finIntegersMod 5 2 _

end CasCatalogue.UnitInverseTests
