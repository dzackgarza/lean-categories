/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
import Mathlib.Algebra.Ring.TransferInstance
meta import LeanCategories.Catalogue.Semantics.Algebra.PolynomialEvidence

/-!
# Independent controls for the closed polynomial evidence contract

These examples exercise the documented expression, normalization, catalogue-presentation,
and injective-coefficient-map cases of `Polynomials.nonzeroPolynomialEvidence`. They state
whole polynomial obligations. The zero equations are proved separately from the evidence,
and the refused attempts do not have those equations in their local contexts.

The mathematical owners are `Polynomial.ne_zero_of_coe_le_degree`,
`Polynomial.map_ne_zero_iff`, `RingHom.injective`, `RingHom.injective_int`, and
`FaithfulSMul.algebraMap_injective`. No computational implementation is an input.
-/

open CategoryTheory Polynomial
open CasCatalogue.Algebra

namespace CasCatalogue.Algebra.Polynomials.ContractTests

/-! ## Expressions and cancellation over each advertised coefficient ring -/

example : (-(X + C 2) ^ 3 + X ^ 3 : Polynomial ℤ) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

example : ((X - C (3 / 2)) * (X + C (3 / 2)) - X ^ 2 : Polynomial ℚ) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

example : (C (3 / 2) * X ^ 4 - X + 1 : Polynomial ℝ) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

example : (C Complex.I * X ^ 2 + 1 : Polynomial ℂ) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

-- Expansion creates the new multiple eight of the selected characteristic.
example : ((X + 3) * (X + 5) - X ^ 2 : Polynomial (ZMod 8)) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

-- Nilpotent leading coefficients disappear, but the constant coefficient survives.
example : ((C 2 * X) ^ 3 + 3 : Polynomial (ZMod 8)) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

example : ((X + 1) ^ 2 - X ^ 2 - 2 * X : Polynomial (ZMod 0)) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

/-! ## Independently justified injectivity cases -/

-- A map from a simple ring into a nontrivial ring.
example : (X ^ 3 + C (2 / 3) : Polynomial ℚ).map (algebraMap ℚ ℝ) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

example : (X ^ 2 - C (5 / 2) : Polynomial ℝ).map Complex.ofRealHom ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

-- The coefficient map is a nonidentity endomorphism of the same carrier.
example : (X ^ 2 + C Complex.I : Polynomial ℂ).map (starRingEnd ℂ) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

-- Characteristic zero supplies the injectivity of the integer coefficient map.
example : (X ^ 4 - 2 * X + 3 : Polynomial ℤ).map (Int.castRingHom ℂ) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

-- The source coefficient ring is neither simple nor the integers.
example : (X ^ 2 + 1 : Polynomial (Polynomial (ZMod 8))).map
    (algebraMap (Polynomial (ZMod 8)) (Polynomial (Polynomial (ZMod 8)))) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

example : (X ^ 3 + C 2 : Polynomial (ZMod 8)).map (RingHom.id (ZMod 8)) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

example : (X ^ 2 + 1 : Polynomial (ZMod 8)).map
    ((algebraMap (Polynomial (ZMod 8)) (Polynomial (Polynomial (ZMod 8)))).comp
      (algebraMap (ZMod 8) (Polynomial (ZMod 8)))) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

/-! ## Closed catalogue presentations retain their selected structures and maps -/

example :
    let R := NamedCommutativeRings.rationals
    let P := ringPolynomials R
    NamedRings.add P
      (NamedRings.pow P 3 (generator R 0),
        coefficients R
          (NamedRings.ringNumeral ((forget₂ CommRingCat RingCat).obj R) 2 0)) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

example :
    let R := NamedCommutativeRings.integersMod 8
    let P := ringPolynomials R
    let x := generator R 0
    NamedRings.add P
      (NamedRings.mul P
        (NamedRings.add P (x, NamedRings.ringNumeral P 3 0),
          NamedRings.add P (x, NamedRings.ringNumeral P 5 0)),
        NamedRings.neg P (NamedRings.pow P 2 x)) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

example : map NamedCommutativeRings.integers NamedCommutativeRings.complexes
    (NamedCommutativeRings.integerCoefficients NamedCommutativeRings.reals ≫
      NamedCommutativeRings.realComplexCoefficients)
    (generator NamedCommutativeRings.integers 0 ^ 4 + 3) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

/-! ## Independently proved zero polynomials and corresponding refusals -/

theorem rationalCancellation_zero :
    ((X - 2) * (X + 2) - X ^ 2 + 4 : Polynomial ℚ) = 0 := by
  ring

example : True := by
  fail_if_success
    have : ((X - 2) * (X + 2) - X ^ 2 + 4 : Polynomial ℚ) ≠ 0 := by
      run_tac nonzeroPolynomialEvidence
  trivial

theorem residueCancellation_zero :
    ((X + 3) * (X + 5) - X ^ 2 - 7 : Polynomial (ZMod 8)) = 0 := by
  ring_nf
  reduce_mod_char

example : True := by
  fail_if_success
    have : ((X + 3) * (X + 5) - X ^ 2 - 7 : Polynomial (ZMod 8)) ≠ 0 := by
      run_tac nonzeroPolynomialEvidence
  trivial

theorem zeroRing_variable_zero : (X : Polynomial (ZMod 1)) = 0 :=
  Subsingleton.elim _ _

example : True := by
  fail_if_success
    have : (X : Polynomial (ZMod 1)) ≠ 0 := by
      run_tac nonzeroPolynomialEvidence
  trivial

theorem mappedZero_zero : (X - X : Polynomial ℚ).map (algebraMap ℚ ℝ) = 0 := by
  simp

example : True := by
  fail_if_success
    have : (X - X : Polynomial ℚ).map (algebraMap ℚ ℝ) ≠ 0 := by
      run_tac nonzeroPolynomialEvidence
  trivial

theorem noninjectiveConstant_zero :
    (C 8 : Polynomial ℤ).map (Int.castRingHom (ZMod 8)) = 0 := by
  norm_num
  reduce_mod_char

example : True := by
  fail_if_success
    have : (C 8 : Polynomial ℤ).map (Int.castRingHom (ZMod 8)) ≠ 0 := by
      run_tac nonzeroPolynomialEvidence
  trivial

/-! ## One coefficient carrier with incompatible selected ring structures -/

/-- Transport the residue-ring structure along the permutation interchanging its zero and
one. Its selected zero is the ordinary residue class one. This is Mathlib's existing
`Equiv.commRing` construction, not a second definition of a ring. -/
noncomputable def zeroSwappedResidues : CommRingCat :=
  @CommRingCat.of (ZMod 8) (Equiv.swap (0 : ZMod 8) 1).commRing

theorem zeroSwappedResidues_zero : (0 : zeroSwappedResidues) = (1 : ZMod 8) := by
  change (Equiv.swap (0 : ZMod 8) 1).symm 0 = 1
  simp

example : (C 1 : Polynomial (ZMod 8)) ≠ 0 := by
  run_tac nonzeroPolynomialEvidence

theorem incompatibleConstant_zero : coefficients zeroSwappedResidues (1 : ZMod 8) = 0 := by
  rw [← zeroSwappedResidues_zero]
  simp only [coefficients, TypeCat.ofHom_apply, map_zero]

example : True := by
  fail_if_success
    have : coefficients zeroSwappedResidues (1 : ZMod 8) ≠ 0 := by
      run_tac nonzeroPolynomialEvidence
  trivial

end CasCatalogue.Algebra.Polynomials.ContractTests
