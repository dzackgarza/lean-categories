/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Units
public import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
public import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
public import Mathlib.Algebra.Group.Pi.Units
public meta import LeanCategories.Catalogue.Semantics.Algebra.Units

@[expose] public section

/-!
# Units at the exact selected categorical presentation

These controls use the already declared matrix determinant criterion and
constant-polynomial criterion. They check both the full unit proposition and
the constructive inverse with both multiplication laws. Literal functions and
categorical wrappers retain their original multiplication and coefficient
instances. No new family of units is introduced.

Sources: Mathlib `Matrix.isUnit_iff_isUnit_det`,
`Matrix.invertibleOfDetInvertible`, `Polynomial.isUnit_C`, and `Pi.isUnit_iff`.
-/

open CategoryTheory
open CasCatalogue.Algebra
open CasCatalogue.Algebra.Units

namespace CasCatalogue.UnitsPresentationTests

/-- The scalar numeral lies in the monoid of the exact forgotten rational ring. -/
example :
    let R := (forget₂ CommRingCat RingCat).obj NamedCommutativeRings.rationals
    let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj R
    let a : M := ConcreteCategory.hom (C := Type) (NamedRings.ringNumeral R 5)
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)
    Nonempty (Invertible a) ∧ IsUnit a := by
  constructor
  · exact ⟨by run_tac invertibleEvidence⟩
  · run_tac isUnitEvidence

/-- This integer matrix has determinant one, in its registered matrix ring. -/
example :
    let R := LinearAlgebra.matrixRing 2 NamedCommutativeRings.integers
    let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj R
    let A : M := !![2, 3; 3, 5]
    Nonempty (Invertible A) ∧ IsUnit A := by
  constructor
  · exact ⟨by run_tac invertibleEvidence⟩
  · run_tac isUnitEvidence

/-- The same matrix as a literal function keeps exactly the same dictionaries. -/
example :
    let R := LinearAlgebra.matrixRing 2 NamedCommutativeRings.integers
    let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj R
    let A : M := fun i j =>
      if i = 0 then (if j = 0 then 2 else 3) else (if j = 0 then 3 else 5)
    Nonempty (Invertible A) ∧ IsUnit A := by
  constructor
  · exact ⟨by run_tac invertibleEvidence⟩
  · run_tac isUnitEvidence

/-- Matrix entries may themselves be the public numerals of the selected
coefficient ring. The determinant is minus two, a unit of that rational ring. -/
example :
    let K := NamedCommutativeRings.rationals
    let S := (forget₂ CommRingCat RingCat).obj K
    let R := LinearAlgebra.matrixRing 2 K
    let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj R
    let A : M := fun i j =>
      ConcreteCategory.hom (C := Type)
        (NamedRings.ringNumeral S
          (if i = 0 then (if j = 0 then 1 else 2) else (if j = 0 then 3 else 4)))
        (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)
    Nonempty (Invertible A) ∧ IsUnit A := by
  constructor
  · exact ⟨by run_tac invertibleEvidence⟩
  · run_tac isUnitEvidence

/-- The public coefficient morphism presents a constant polynomial unit. -/
example :
    let K := NamedCommutativeRings.rationals
    let R : RingCat.{0} := Polynomials.ringPolynomials K
    let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj R
    let p : M := ConcreteCategory.hom (C := Type) (Polynomials.coefficients K) (5 : K)
    Nonempty (Invertible p) ∧ IsUnit p := by
  constructor
  · exact ⟨by run_tac invertibleEvidence⟩
  · run_tac isUnitEvidence

/-- A literal function of the published generator presents the constant one
after polynomial normalization; it uses the chosen polynomial ring throughout. -/
example :
    let K := NamedCommutativeRings.rationals
    let R : RingCat.{0} := Polynomials.ringPolynomials K
    let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj R
    let x : R := ConcreteCategory.hom (C := Type) (Polynomials.generator K)
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)
    let p : M := (fun y : R => (y + 1) ^ 2 - y ^ 2 - 2 * y) x
    Nonempty (Invertible p) ∧ IsUnit p := by
  constructor
  · exact ⟨by run_tac invertibleEvidence⟩
  · run_tac isUnitEvidence

/-- A matrix with integer determinant two is not a unit of its selected ring. -/
theorem integer_matrix_not_unit :
    let R := LinearAlgebra.matrixRing 2 NamedCommutativeRings.integers
    let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj R
    ¬ IsUnit (show M from fun i j => if i = j then (if i = 0 then 2 else 1) else 0) := by
  change ¬ @IsUnit (Matrix (Fin 2) (Fin 2) ℤ) inferInstance
    (fun i j => if i = j then (if i = 0 then 2 else 1) else 0)
  intro h
  have determinantUnit := (Matrix.isUnit_iff_isUnit_det (n := Fin 2) (α := ℤ)
    (fun i j => if i = j then (if i = 0 then 2 else 1) else 0)).mp h
  have determinantValue :
      Matrix.det (fun i j : Fin 2 => if i = j then (if i = 0 then (2 : ℤ) else 1) else 0) = 2 := by
    simpa using Matrix.det_fin_two (R := ℤ)
      (fun i j => if i = j then (if i = 0 then 2 else 1) else 0)
  rw [determinantValue] at determinantUnit
  norm_num [Int.isUnit_iff] at determinantUnit

/-- The selected rational matrix is singular, so it cannot have an inverse. -/
theorem rational_matrix_not_unit :
    let R := LinearAlgebra.matrixRing 2 NamedCommutativeRings.rationals
    let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj R
    ¬ IsUnit (show M from fun (_i _j : Fin 2) => 1) := by
  change ¬ @IsUnit (Matrix (Fin 2) (Fin 2) ℚ) inferInstance (fun _i _j => 1)
  intro h
  have determinantUnit := (Matrix.isUnit_iff_isUnit_det (n := Fin 2) (α := ℚ)
    (fun _i _j => 1)).mp h
  have determinantValue : Matrix.det (fun _i _j : Fin 2 => (1 : ℚ)) = 0 := by
    simpa using Matrix.det_fin_two (R := ℚ) (fun _i _j => 1)
  rw [determinantValue] at determinantUnit
  exact not_isUnit_zero determinantUnit

/-- A nonconstant polynomial is still noninvertible in the selected polynomial ring. -/
theorem polynomial_generator_not_unit :
    let K := NamedCommutativeRings.rationals
    let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj (Polynomials.ringPolynomials K)
    ¬ IsUnit (show M from ConcreteCategory.hom (C := Type) (Polynomials.generator K)
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)) := by
  exact Polynomial.not_isUnit_X

/-- Matrix identity is a unit for matrix multiplication. -/
example :
    let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj
      (LinearAlgebra.matrixRing 2 NamedCommutativeRings.rationals)
    Nonempty (Invertible (show M from fun i j => if i = j then 1 else 0)) := by
  exact ⟨by run_tac invertibleEvidence⟩

/-- On the same function carrier, pointwise multiplication has different
units: the zero off-diagonal entry prevents this function being a unit. -/
theorem pointwise_identity_not_unit :
    ¬ IsUnit (fun i j : Fin 2 => if i = j then (1 : ℚ) else 0) := by
  intro h
  have impossible := (h.apply 0).apply 1
  norm_num at impossible

/-- Both procedures refuse the nonunits at their unchanged selected structures. -/
example : True := by
  fail_if_success
    have :
        let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj
          (LinearAlgebra.matrixRing 2 NamedCommutativeRings.integers)
        IsUnit (show M from fun i j => if i = j then (if i = 0 then 2 else 1) else 0) := by
      run_tac isUnitEvidence
  fail_if_success
    have :
        let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj
          (LinearAlgebra.matrixRing 2 NamedCommutativeRings.integers)
        Invertible (show M from fun i j => if i = j then (if i = 0 then 2 else 1) else 0) := by
      run_tac invertibleEvidence
  fail_if_success
    have :
        let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj
          (LinearAlgebra.matrixRing 2 NamedCommutativeRings.rationals)
        IsUnit (show M from fun (_i _j : Fin 2) => 1) := by
      run_tac isUnitEvidence
  fail_if_success
    have :
        let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj
          (LinearAlgebra.matrixRing 2 NamedCommutativeRings.rationals)
        Invertible (show M from fun (_i _j : Fin 2) => 1) := by
      run_tac invertibleEvidence
  fail_if_success
    have :
        let K := NamedCommutativeRings.rationals
        let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj (Polynomials.ringPolynomials K)
        IsUnit (show M from ConcreteCategory.hom (C := Type) (Polynomials.generator K)
          (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)) := by
      run_tac isUnitEvidence
  fail_if_success
    have :
        let K := NamedCommutativeRings.rationals
        let M : MonCat.{0} := Ports.ringsMultiplicative.toFunctor.obj (Polynomials.ringPolynomials K)
        Invertible (show M from ConcreteCategory.hom (C := Type) (Polynomials.generator K)
          (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)) := by
      run_tac invertibleEvidence
  fail_if_success
    have : IsUnit (fun i j : Fin 2 => if i = j then (1 : ℚ) else 0) := by
      run_tac isUnitEvidence
  fail_if_success
    have : Invertible (fun i j : Fin 2 => if i = j then (1 : ℚ) else 0) := by
      run_tac invertibleEvidence
  trivial

end CasCatalogue.UnitsPresentationTests
