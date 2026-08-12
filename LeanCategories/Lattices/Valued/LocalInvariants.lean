/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

namespace LeanCategories.Lattices.Valued

universe u

/-- An abelian group modulo its subgroup of squares. -/
abbrev ModSquares (G : Type u) [CommGroup G] :=
  G ⧸ Subgroup.square G

/-- The square-class group of a field. -/
abbrev FieldSquareClass (K : Type u) [Field K] :=
  ModSquares Kˣ

/-- The square-class group of the units of a commutative ring. -/
abbrev UnitSquareClass (R : Type u) [CommRing R] :=
  ModSquares Rˣ

/-- The square class of a nonzero field element. -/
def fieldSquareClass {K : Type u} [Field K] (x : Kˣ) :
    FieldSquareClass K :=
  QuotientGroup.mk' (Subgroup.square Kˣ) x

/-- The square class of a ring unit. -/
def unitSquareClass {R : Type u} [CommRing R] (x : Rˣ) :
    UnitSquareClass R :=
  QuotientGroup.mk' (Subgroup.square Rˣ) x

/-- Every class modulo squares has exponent two. -/
theorem modSquares_sq {G : Type u} [CommGroup G]
    (x : ModSquares G) : x ^ 2 = 1 := by
  refine Quotient.inductionOn' x ?_
  intro g
  rw [← QuotientGroup.mk_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.mem_square.mpr ⟨g, pow_two g⟩

/-- The square class of a product is the product of the square classes. -/
theorem fieldSquareClass_mul {K : Type u} [Field K] (u v : Kˣ) :
    fieldSquareClass (u * v) = fieldSquareClass u * fieldSquareClass v :=
  map_mul _ _ _

/-- Multiplying by a square does not change the square class. -/
theorem fieldSquareClass_mul_sq {K : Type u} [Field K] (u q : Kˣ) :
    fieldSquareClass (u * (q * q)) = fieldSquareClass u := by
  rw [fieldSquareClass, fieldSquareClass, QuotientGroup.mk'_eq_mk']
  exact ⟨q⁻¹ * q⁻¹, Subgroup.mem_square.mpr ⟨q⁻¹, rfl⟩, by group⟩

/-- Square classes of the `p`-adic field. -/
abbrev PadicSquareClass (p : ℕ) [Fact p.Prime] :=
  FieldSquareClass ℚ_[p]

/-- Square classes of units in the `p`-adic integers. -/
abbrev PadicUnitSquareClass (p : ℕ) [Fact p.Prime] :=
  UnitSquareClass ℤ_[p]

end LeanCategories.Lattices.Valued
