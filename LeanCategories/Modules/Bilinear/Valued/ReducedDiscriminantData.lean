/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.LocalInvariants
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Reduced-discriminant presentation data

Definition-level data for Peters--Sterk FC11-C09-U005.

For an invariant-factor presentation with elementary divisors
`d₁ ∣ ⋯ ∣ dᵣ` and a fraction-field Gram lift `B`, the source first forms

`(d₁ ⋯ dᵣ) det(B)`.

The preceding source corollary proves that this lies in the base ring and,
for a nonsingular form, is prime to `d₁`. Those are result-layer facts.
Sweep III therefore records the displayed normalized determinant, its
possible integral representative, the reduction modulo the first elementary
divisor, and the target unit-square-class group. It does not manufacture
integrality or unit proofs and does not claim presentation-independence.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable (R : Type u) [CommRing R] [IsDomain R]
variable {n : ℕ}

/-- The denominator-normalized Gram determinant
`(∏ᵢ dᵢ) det(B)` before applying the integrality result. -/
def normalizedTorsionGramDeterminantData
    (d : Fin (n + 1) → R)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (FractionRing R)) :
    FractionRing R :=
  algebraMap R (FractionRing R) (∏ i, d i) * Matrix.det B

/-- A base-ring element represents the normalized Gram determinant when its
image in the fraction field is the displayed source expression.

Existence of such a representative is Corollary 9.1.4(1), not definition
work. -/
def IsNormalizedTorsionGramDeterminantRepresentative
    (d : Fin (n + 1) → R)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (FractionRing R))
    (a : R) : Prop :=
  algebraMap R (FractionRing R) a =
    normalizedTorsionGramDeterminantData R d B

/-- The residue ring used by the reduced discriminant, with modulus the first
elementary divisor. -/
abbrev reducedDiscriminantResidueRingData
    (d : Fin (n + 1) → R) :=
  R ⧸ Ideal.span {d 0}

/-- The target `D(R / d₁R)`: units of the first-elementary-divisor residue
ring modulo squares of units. -/
abbrev ReducedDiscriminantSquareClassData
    (d : Fin (n + 1) → R) :=
  LeanCategories.Lattices.Valued.UnitSquareClass
    (reducedDiscriminantResidueRingData R d)

/-- Reduce an integral normalized-determinant representative modulo the first
elementary divisor. -/
def reducedDiscriminantResidueData
    (d : Fin (n + 1) → R) (a : R) :
    reducedDiscriminantResidueRingData R d :=
  Ideal.Quotient.mk (Ideal.span {d 0}) a

/-- Pass a supplied unit of the residue ring to its square class.

For the normalized determinant, the fact that the residue is a unit is
Corollary 9.1.4(2) and remains outside Sweep III. -/
def reducedDiscriminantSquareClassOfUnitData
    (d : Fin (n + 1) → R)
    (u : (reducedDiscriminantResidueRingData R d)ˣ) :
    ReducedDiscriminantSquareClassData R d :=
  LeanCategories.Lattices.Valued.unitSquareClass u

end LeanCategories.Modules.Bilinear.Valued
