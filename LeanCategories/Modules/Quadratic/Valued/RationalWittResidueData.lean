/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.WittRingData
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Rational Witt residue data

Definition-level realization of Peters--Sterk FC11-C07-U025.

The source specifies the two maps appearing in the rational Witt exact
sequence by their generators: the inclusion sends `1` to the class of the
rank-one form `⟨1⟩`, while the boundary sends a rank-one class `⟨a⟩` to its
primewise residue classes.

Sweep III records these prescriptions as relations on the raw Witt quotient.
No additive-group structure on the quotient, homomorphism law, finite-support
theorem, quotient descent, or exactness assertion is proved here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Modules.Quadratic.Valued

/-- A prime number used as an index for the rational Witt residue family. -/
abbrev RationalWittPrimeData := {p : ℕ // p.Prime}

/-- The rank-one quadratic form `x ↦ a x²` as a finite free quadratic
module. -/
def rankOneFiniteFreeQuadraticSpaceData
    {R : Type*} [CommRing R] (a : R) :
    FiniteFreeQuadModuleCat R R := by
  refine ⟨QuadModuleCat.ofQuadraticMap
    (a • QuadraticMap.sq (R := R)), ?_⟩
  change Module.Free R R ∧ Module.Finite R R
  constructor <;> infer_instance

/-- A raw Witt class is represented by the rank-one form `⟨a⟩`. -/
def IsQuadraticWittRankOneData
    {R : Type*} [CommRing R]
    (x : QuadraticWittClass R) (a : R) : Prop :=
  IsQuadraticWittRepresentativeData R x
    (rankOneFiniteFreeQuadraticSpaceData a)

/-- Peters--Sterk's defining generator clause for
`i : ℤ → W(ℚ)`: the image of `1` is `⟨1⟩`. -/
def IsRationalWittInclusionGeneratorData
    (x : QuadraticWittClass ℚ) : Prop :=
  IsQuadraticWittRankOneData x 1

/-- Candidate prime-indexed residue family before imposing finite support. -/
abbrev RationalWittResidueFamilyCandidateData :=
  (p : RationalWittPrimeData) → QuadraticWittClass (ZMod p.1)

/-- Source-level finite-support condition for a prime-indexed family of raw
Witt classes.

Zero is expressed through U021's exact zero graph, so no arbitrary zero
element of the raw quotient is selected. -/
def IsRationalWittResidueFamilyData
    (f : RationalWittResidueFamilyCandidateData) : Prop :=
  ∃ S : Finset RationalWittPrimeData,
    ∀ p, p ∉ S → IsQuadraticWittZeroData (ZMod p.1) (f p)

/-- The `p`-adic unit part of a nonzero rational coefficient. -/
def rationalPadicUnitPartData
    (p : RationalWittPrimeData) (a : ℚˣ) : ℚ :=
  (a : ℚ) * (p.1 : ℚ) ^ (-padicValRat p.1 (a : ℚ))

/-- Residue coefficient of the normalized `p`-adic unit part.

`PadicInt.modPart` is Mathlib's explicit rational representative modulo `p`.
The theorem that the normalized coefficient is a `p`-adic unit, and hence that
this is its residue-field image, belongs to the result layer. -/
def rationalWittResidueCoefficientData
    (p : RationalWittPrimeData) (a : ℚˣ) : ZMod p.1 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  exact (PadicInt.modPart p.1 (rationalPadicUnitPartData p a) : ZMod p.1)

/-- Primewise second-residue prescription for a rank-one rational form.

An even `p`-adic valuation contributes the zero Witt class; an odd valuation
contributes the rank-one class of the normalized unit residue. -/
def IsRationalWittBoundaryRankOneData
    (a : ℚˣ) (f : RationalWittResidueFamilyCandidateData) : Prop :=
  IsRationalWittResidueFamilyData f ∧
    ∀ p,
      if Even (padicValRat p.1 (a : ℚ)) then
        IsQuadraticWittZeroData (ZMod p.1) (f p)
      else
        IsQuadraticWittRankOneData (f p)
          (rationalWittResidueCoefficientData p a)

/-- Exact graph of the source boundary prescription on a rank-one Witt
class.

Extending this graph additively to all of `W(ℚ)`, proving independence of a
diagonal representative, and packaging the direct-sum homomorphism are
Sweep-IV results. -/
def IsRationalWittBoundaryData
    (x : QuadraticWittClass ℚ)
    (f : RationalWittResidueFamilyCandidateData) : Prop :=
  ∃ a : ℚˣ,
    IsQuadraticWittRankOneData x (a : ℚ) ∧
      IsRationalWittBoundaryRankOneData a f

end LeanCategories.Modules.Quadratic.Valued
