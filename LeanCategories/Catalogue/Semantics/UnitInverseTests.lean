/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Units
public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
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
open CasCatalogue.Foundation.Morphisms

/-- The element `u⁻¹ ∈ M` of a unit `u : 1 → Mˣ`: `1 → Mˣ → Mˣ ↪ M`. -/
abbrev inverseElement (M : Type) [Monoid M] (u : fin 1 ⟶ units M) :
    fin 1 ⟶ (M : LeanCategories.Foundation.Mathlib.Sets.{0}) :=
  u ≫ inverse M ≫ inclusion M

/-- The element `a / u ∈ M`: the pair `(a, u)`, the mediator of the registered product cone,
followed by `/ : M × Mˣ → M`. -/
abbrev divideElement (M : Type) [Monoid M]
    (a : fin 1 ⟶ (M : LeanCategories.Foundation.Mathlib.Sets.{0})) (u : fin 1 ⟶ units M) :
    fin 1 ⟶ (M : LeanCategories.Foundation.Mathlib.Sets.{0}) :=
  (setsProduct _ _).isLimit.lift (BinaryFan.mk a u) ≫ divide M

/-- The element `c ∈ M` of a value `c`. -/
abbrev element {M : Type} (c : M) : fin 1 ⟶ (M : LeanCategories.Foundation.Mathlib.Sets.{0}) :=
  TypeCat.ofHom fun _ => c

/-- `3⁻¹ = 1/3` in `ℚ`, the inverse of the unit `3 ∈ ℚˣ`. -/
example : inverseElement ℚ (admit ℚ 3 (by run_tac invertibleEvidence)) = element (1 / 3 : ℚ) := by
  decide +kernel

/-- `1 / 3 = 1/3` in `ℚ`: the numeral `1` divided by the unit `3 ∈ ℚˣ`. -/
example : divideElement ℚ (ringNumeral ringRationals 1)
    (admit ℚ 3 (by run_tac invertibleEvidence)) = element (1 / 3 : ℚ) := by
  decide +kernel

/-- `3⁻¹ ≠ 1/2` in `ℚ`. -/
example :
    inverseElement ℚ (admit ℚ 3 (by run_tac invertibleEvidence)) ≠ element (1 / 2 : ℚ) := by
  decide +kernel

/-- `1 / 3 ≠ 3` in `ℚ`. -/
example : divideElement ℚ (ringNumeral ringRationals 1)
    (admit ℚ 3 (by run_tac invertibleEvidence)) ≠ element (3 : ℚ) := by
  decide +kernel

/-- `(-3/4)⁻¹ = -4/3` in `ℚ`. -/
example :
    inverseElement ℚ (admit ℚ (-3 / 4) (by run_tac invertibleEvidence)) = element (-4 / 3 : ℚ) := by
  decide +kernel

/-- `2⁻¹ = 3` in `ℤ/5`. -/
example : inverseElement (ZMod 5) (admit (ZMod 5) 2 (by run_tac invertibleEvidence)) =
    element (3 : ZMod 5) := by
  decide +kernel

/-- `2⁻¹ ≠ 2` in `ℤ/5`. -/
example : inverseElement (ZMod 5) (admit (ZMod 5) 2 (by run_tac invertibleEvidence)) ≠
    element (2 : ZMod 5) := by
  decide +kernel

/-- `7⁻¹ = 7` in `ℤ/12` (`7 · 7 = 49 = 4 · 12 + 1`). -/
example : inverseElement (ZMod 12) (admit (ZMod 12) 7 (by run_tac invertibleEvidence)) =
    element (7 : ZMod 12) := by
  decide +kernel

/-- `(-1)⁻¹ = -1` in `ℤ`, whose units are `±1`. -/
example : inverseElement ℤ (admit ℤ (-1) (by run_tac invertibleEvidence)) = element (-1 : ℤ) := by
  decide +kernel

/-- `1⁻¹ = 1` in `ℤ`. -/
example : inverseElement ℤ (admit ℤ 1 (by run_tac invertibleEvidence)) = element (1 : ℤ) := by
  decide +kernel

/-- `(2 · 4)⁻¹ = 4⁻¹ · 2⁻¹ = 2 · 5 = 1` in `ℤ/7`, through the inverse of a product. -/
example : inverseElement (ZMod 7) (admit (ZMod 7) (2 * 4) (by run_tac invertibleEvidence)) =
    element (1 : ZMod 7) := by
  decide +kernel

/-! ## The registered numerals of `ℤ/n`

A consumer forms the numeral `k ∈ ℤ/n` (`obj.sets.integers_mod`, `n ≠ 0`) with the registered
numeral `num.sets.fin`: `ℤ/n` is `Fin n` by definition (Mathlib `ZMod`), so `finPoint _ k _` at
`1 ⟶ ℤ/n` takes `n = m + 1` and names the point `⟨k, _⟩ : Fin (m + 1)`. That element, not the
`OfNat` literal `(k : ZMod n)`, is the one admitted here. -/

/-- The registered numeral `u = finPoint _ k _` of `ℤ/n`, stated as an element `1 → ℤ/n` (its
elaborated type is `1 → Fin (m + 1)`, the definition of `ℤ/n`). -/
abbrev zmodNumeral (n : ℕ) (u : fin 1 ⟶ integersMod n) : fin 1 ⟶ integersMod n := u

/-- The value in `ℤ/n` of the registered numeral `u`, at the point of `1`: `⟨k, _⟩`. -/
abbrev zmodNumeralValue (n : ℕ) (u : fin 1 ⟶ integersMod n) : integersMod n :=
  ConcreteCategory.hom (C := Type) u ⟨0, Nat.one_pos⟩

/-- `2⁻¹ = 3` in `ℤ/5`, both the registered numerals of `ℤ/5` (`2 · 3 = 6 = 5 + 1`). -/
example : inverseElement (ZMod 5)
    (admit (ZMod 5) (zmodNumeralValue 5 (finPoint _ 2 (by decide)))
      (by run_tac invertibleEvidence)) = zmodNumeral 5 (finPoint _ 3 (by decide)) := by
  decide +kernel

/-- `2⁻¹ ≠ 2` in `ℤ/5`, at the registered numerals. -/
example : inverseElement (ZMod 5)
    (admit (ZMod 5) (zmodNumeralValue 5 (finPoint _ 2 (by decide)))
      (by run_tac invertibleEvidence)) ≠ zmodNumeral 5 (finPoint _ 2 (by decide)) := by
  decide +kernel

/-- `7⁻¹ = 7` in `ℤ/12` (`7 · 7 = 49 = 4 · 12 + 1`), at the registered numerals. -/
example : inverseElement (ZMod 12)
    (admit (ZMod 12) (zmodNumeralValue 12 (finPoint _ 7 (by decide)))
      (by run_tac invertibleEvidence)) = zmodNumeral 12 (finPoint _ 7 (by decide)) := by
  decide +kernel

/-- `1 / 7 = 7` in `ℤ/12`: the numeral `1` divided by the unit `7`, both registered numerals. -/
example : divideElement (ZMod 12) (zmodNumeral 12 (finPoint _ 1 (by decide)))
    (admit (ZMod 12) (zmodNumeralValue 12 (finPoint _ 7 (by decide)))
      (by run_tac invertibleEvidence)) = zmodNumeral 12 (finPoint _ 7 (by decide)) := by
  decide +kernel

end CasCatalogue.UnitInverseTests
