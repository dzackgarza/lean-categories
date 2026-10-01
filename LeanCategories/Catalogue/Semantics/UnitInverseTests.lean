/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Units
public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public import LeanCategories.Catalogue.Semantics.Limits.Registration
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

end CasCatalogue.UnitInverseTests
