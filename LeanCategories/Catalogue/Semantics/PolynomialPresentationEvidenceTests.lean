/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
public meta import LeanCategories.Catalogue.Semantics.Algebra.PolynomialEvidence

@[expose] public section

/-!
# Nonzero polynomial evidence at its selected coefficient structures

The existing public domain requires exactly `p ≠ 0`. These controls keep the
complete polynomial, selected coefficient structures, and actual coefficient
map. They use the existing degree, normalization, and injective-map cases.
The paired zero statements are independently proved equal to zero and refused.
-/

open CategoryTheory
open CasCatalogue.Algebra

namespace CasCatalogue.PolynomialPresentationEvidenceTests

/-- A literal polynomial function of the public generator, in the selected ring. -/
example :
    let K := NamedCommutativeRings.rationals
    let R : RingCat.{0} := Polynomials.ringPolynomials K
    let x : R := ConcreteCategory.hom (C := Type) (Polynomials.generator K)
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)
    (fun y : R => y ^ 3 + 2 * y + 1) x ≠ 0 := by
  run_tac Polynomials.nonzeroPolynomialEvidence

/-- Cancelling leading terms leaves the constant one, at the same selected ring. -/
example :
    let K := NamedCommutativeRings.rationals
    let R : RingCat.{0} := Polynomials.ringPolynomials K
    let x : R := ConcreteCategory.hom (C := Type) (Polynomials.generator K)
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)
    (fun y : R => (y + 1) ^ 2 - y ^ 2 - 2 * y) x ≠ 0 := by
  run_tac Polynomials.nonzeroPolynomialEvidence

/-- The coefficient ring may be its public forgotten-ring presentation, and
the coefficient itself its declared numeral map. -/
example :
    let S := (forget₂ CommRingCat RingCat).obj NamedCommutativeRings.rationals
    let c : S := ConcreteCategory.hom (C := Type) (NamedRings.ringNumeral S 3)
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)
    (Polynomial.X ^ 2 + Polynomial.C c : Polynomial S) ≠ 0 := by
  run_tac Polynomials.nonzeroPolynomialEvidence

/-- Reduction in the selected characteristic removes the leading term but
leaves a nonzero constant: `(X+3)(X+4)-X² = 5` over the ring of residues modulo seven. -/
example :
    let K := NamedCommutativeRings.integersMod 7
    let R : RingCat.{0} := Polynomials.ringPolynomials K
    let x : R := ConcreteCategory.hom (C := Type) (Polynomials.generator K)
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)
    (fun y : R => (y + 3) * (y + 4) - y ^ 2) x ≠ 0 := by
  run_tac Polynomials.nonzeroPolynomialEvidence

/-- The actual public integer coefficient map preserves this entire nonzero
polynomial. Its source is not replaced by a carrier with an inferred map. -/
example :
    let R := NamedCommutativeRings.integers
    let S := NamedCommutativeRings.rationals
    let q := NamedCommutativeRings.integerCoefficients S
    ConcreteCategory.hom (C := Type) (Polynomials.map R S q)
      (Polynomial.X ^ 2 + 1 : Polynomial R) ≠ 0 := by
  run_tac Polynomials.nonzeroPolynomialEvidence

/-- The neighboring cancelling expression is exactly zero. -/
theorem cancelled_polynomial_eq_zero :
    let K := NamedCommutativeRings.rationals
    let R : RingCat.{0} := Polynomials.ringPolynomials K
    let x : R := ConcreteCategory.hom (C := Type) (Polynomials.generator K)
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)
    (fun y : R => (y + 1) ^ 2 - y ^ 2 - 2 * y - 1) x = 0 := by
  change (Polynomial.X + 1) ^ 2 - Polynomial.X ^ 2 -
    2 * Polynomial.X - 1 = (0 : Polynomial ℚ)
  ring

/-- A coefficient that vanishes in the selected characteristic gives zero. -/
theorem vanished_coefficient_eq_zero :
    let K := NamedCommutativeRings.integersMod 7
    let R : RingCat.{0} := Polynomials.ringPolynomials K
    let x : R := ConcreteCategory.hom (C := Type) (Polynomials.generator K)
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)
    (fun y : R => 7 * y) x = 0 := by
  change Polynomial.C (7 : ZMod 7) * Polynomial.X = (0 : Polynomial (ZMod 7))
  rw [show (7 : ZMod 7) = 0 by decide]
  simp only [Polynomial.C_0, zero_mul]

/-- The selected coefficient map sends the zero polynomial to zero. -/
theorem mapped_zero_eq_zero :
    let R := NamedCommutativeRings.integers
    let S := NamedCommutativeRings.rationals
    let q := NamedCommutativeRings.integerCoefficients S
    ConcreteCategory.hom (C := Type) (Polynomials.map R S q)
      (Polynomial.X - Polynomial.X : Polynomial R) = 0 := by
  simp [Polynomials.map]

/-- The public nonzero evidence refuses each complete zero expression. -/
example : True := by
  fail_if_success
    have :
        let K := NamedCommutativeRings.rationals
        let R : RingCat.{0} := Polynomials.ringPolynomials K
        let x : R := ConcreteCategory.hom (C := Type) (Polynomials.generator K)
          (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)
        (fun y : R => (y + 1) ^ 2 - y ^ 2 - 2 * y - 1) x ≠ 0 := by
      run_tac Polynomials.nonzeroPolynomialEvidence
  fail_if_success
    have :
        let K := NamedCommutativeRings.integersMod 7
        let R : RingCat.{0} := Polynomials.ringPolynomials K
        let x : R := ConcreteCategory.hom (C := Type) (Polynomials.generator K)
          (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)
        (fun y : R => 7 * y) x ≠ 0 := by
      run_tac Polynomials.nonzeroPolynomialEvidence
  fail_if_success
    have :
        let R := NamedCommutativeRings.integers
        let S := NamedCommutativeRings.rationals
        let q := NamedCommutativeRings.integerCoefficients S
        ConcreteCategory.hom (C := Type) (Polynomials.map R S q)
          (Polynomial.X - Polynomial.X : Polynomial R) ≠ 0 := by
      run_tac Polynomials.nonzeroPolynomialEvidence
  trivial

end CasCatalogue.PolynomialPresentationEvidenceTests
