/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.SerreConstruction
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis

/-!
# Humphreys' tensor-algebra model for the pre-Serre generators

Definition-level realization of Humphreys FC14-C05-U025.

For an ordered Cartan matrix, Humphreys lets the free Lie generators
`H_i,E_i,F_i` act on the tensor algebra on a vector space with basis
`v_i`.  Relative to the word basis, `H_i` acts by the negative Cartan
weight, `F_i` prefixes the letter `i`, and `E_i` is defined recursively
on the word length.

This file records exactly those endomorphisms and extends the generator
assignment to the free Lie algebra.  Showing that the four S1--S3 relator
families act by zero, and hence that the representation factors through
Humphreys' intermediate algebra `L₀`, is FC14-C05-U026 and is deliberately
not proved here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v

variable (F : Type u) (ι : Type v)
variable [Field F] [CharZero F] [DecidableEq ι]

/-- The vector space on Humphreys' letters `v_i`. -/
abbrev PreSerreGeneratorSpace := ι →₀ F

/-- The tensor algebra used for Humphreys' model representation. -/
abbrev PreSerreTensorSpace := TensorAlgebra F (PreSerreGeneratorSpace F ι)

/-- The chosen basis `(v_i)` of the generating vector space. -/
def preSerreGeneratorBasis : Module.Basis ι F (PreSerreGeneratorSpace F ι) :=
  Finsupp.basisSingleOne

/-- The induced word basis of the tensor algebra. -/
def preSerreTensorWordBasis :
    Module.Basis (FreeMonoid ι) F (PreSerreTensorSpace F ι) :=
  (preSerreGeneratorBasis F ι).tensorAlgebra

/-- The tensor corresponding to a word in the letters `v_i`. -/
def preSerreTensorWord (w : FreeMonoid ι) : PreSerreTensorSpace F ι :=
  preSerreTensorWordBasis F ι w

/-- The Cartan weight `Σ_r c_{i_r,j}` of a word
`v_{i₁}⋯v_{i_t}`. -/
def preSerreWordCartanWeight
    (A : Matrix ι ι ℤ) (j : ι) (w : FreeMonoid ι) : F :=
  (w.toList.map fun i => (A i j : F)).sum

/-- Humphreys' recursively defined action of `E_j` on a basis word.

For `i :: w` this is
`v_i (E_j · w) - δ_{ji} (Σ_{k∈w} c_{k j}) w`.
-/
def preSerreEWord
    (A : Matrix ι ι ℤ) (j : ι) :
    List ι → PreSerreTensorSpace F ι
  | [] => 0
  | i :: tail =>
      TensorAlgebra.ι F (Finsupp.single i 1) * preSerreEWord A j tail -
        if i = j then
          (tail.map fun k => (A k j : F)).sum •
            preSerreTensorWord F ι (FreeMonoid.ofList tail)
        else 0

/-- Humphreys' diagonal action of `H_j` on the tensor word basis. -/
def preSerreHEndomorphism
    (A : Matrix ι ι ℤ) (j : ι) : Module.End F (PreSerreTensorSpace F ι) :=
  (preSerreTensorWordBasis F ι).constr F fun w =>
    (-preSerreWordCartanWeight F ι A j w) • preSerreTensorWord F ι w

/-- Humphreys' action of `F_j`: left multiplication by `v_j`. -/
def preSerreFEndomorphism
    (j : ι) : Module.End F (PreSerreTensorSpace F ι) :=
  (preSerreTensorWordBasis F ι).constr F fun w =>
    preSerreTensorWord F ι (FreeMonoid.of j * w)

/-- Humphreys' recursively defined action of `E_j`. -/
def preSerreEEndomorphism
    (A : Matrix ι ι ℤ) (j : ι) : Module.End F (PreSerreTensorSpace F ι) :=
  (preSerreTensorWordBasis F ι).constr F fun w =>
    preSerreEWord F ι A j w.toList

/-- The explicit endomorphism assigned to each free pre-Serre generator. -/
def preSerreTensorGeneratorAction
    (A : Matrix ι ι ℤ) :
    CartanMatrix.Generators ι → Module.End F (PreSerreTensorSpace F ι)
  | .H i => preSerreHEndomorphism F ι A i
  | .E i => preSerreEEndomorphism F ι A i
  | .F i => preSerreFEndomorphism F ι i

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The representation of the free Lie algebra obtained by extending
Humphreys' explicit generator endomorphisms. -/
def preSerreTensorFreeLieRepresentation
    (A : Matrix ι ι ℤ) :
    FreeLieAlgebra F (CartanMatrix.Generators ι) →ₗ⁅F⁆
      Module.End F (PreSerreTensorSpace F ι) :=
  FreeLieAlgebra.lift F (preSerreTensorGeneratorAction F ι A)

end LeanCategories.Algebra
