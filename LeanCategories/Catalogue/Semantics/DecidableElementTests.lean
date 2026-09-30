/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public import LeanCategories.Catalogue.Semantics.Limits.Registration

@[expose] public section

/-!
# Decidable equality of elements of named sets

An element `x` of a set `X` is a global element `1 ⟶ X` of `Sets`, so an equation between
elements is an equation between morphisms. Such an equation is decided by `decide`, with a
kernel-checked proof, through `CategoryTheory.ConcreteCategory.decidableEqHom` and Mathlib's
decidable equality of functions out of the finite set `1 = Fin 1`.

The elements are formed as the catalogue forms them: numerals are `ringNumeral` (the image of
`k` under the ring map out of `ℤ`), and a binary operation is applied to a pair of elements
through the mediator of the registered product cone `lim.sets.product`.
-/

namespace CasCatalogue.DecidableElementTests

open CategoryTheory Limits
open CasCatalogue.Algebra.NamedRings CasCatalogue.Limits.Registration

/-- The element `op(x, y)` of `R`: the pair `(x, y) : 1 ⟶ R × R` is the mediator of the
registered product cone, followed by the operation `R × R → R`. -/
def applyBinary (R : LeanCategories.Algebra.Rings.{0})
    (op : (underlying R × underlying R : LeanCategories.Foundation.Mathlib.Sets.{0}) ⟶
      (underlying R : LeanCategories.Foundation.Mathlib.Sets.{0}))
    (x y : CasCatalogue.Foundation.Objects.fin 1 ⟶
      (underlying R : LeanCategories.Foundation.Mathlib.Sets.{0})) :
    CasCatalogue.Foundation.Objects.fin 1 ⟶
      (underlying R : LeanCategories.Foundation.Mathlib.Sets.{0}) :=
  (setsProduct _ _).isLimit.lift (BinaryFan.mk x y) ≫ op

/-- `2 + 3 = 5` in `ℤ`. -/
example : applyBinary ringIntegers (add ringIntegers) (ringNumeral ringIntegers 2)
    (ringNumeral ringIntegers 3) = ringNumeral ringIntegers 5 := by
  decide

/-- `2 + 3 ≠ 6` in `ℤ`. -/
example : applyBinary ringIntegers (add ringIntegers) (ringNumeral ringIntegers 2)
    (ringNumeral ringIntegers 3) ≠ ringNumeral ringIntegers 6 := by
  decide

/-- `2 · 3 = 1` in `ℤ/5`. -/
example : applyBinary (ringIntegersMod 5) (mul (ringIntegersMod 5))
    (ringNumeral (ringIntegersMod 5) 2) (ringNumeral (ringIntegersMod 5) 3) =
      ringNumeral (ringIntegersMod 5) 1 := by
  decide

/-- `2 · 3 ≠ 5` in `ℤ`. -/
example : applyBinary ringIntegers (mul ringIntegers) (ringNumeral ringIntegers 2)
    (ringNumeral ringIntegers 3) ≠ ringNumeral ringIntegers 5 := by
  decide

/-- The point `2` of `Fin 3` is not the point `1`. -/
example : CasCatalogue.Foundation.Morphisms.finPoint 3 2 (by decide) ≠
    CasCatalogue.Foundation.Morphisms.finPoint 3 1 (by decide) := by
  decide

end CasCatalogue.DecidableElementTests
