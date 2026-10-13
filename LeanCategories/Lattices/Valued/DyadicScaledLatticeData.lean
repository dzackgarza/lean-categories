/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantQuadratic
public import LeanCategories.Lattices.Valued.Dyadic
public import LeanCategories.Lattices.Valued.Jordan

/-!
# Dyadic scaled-lattice data

Definition-level data for Peters--Sterk FC11-C12-U036.

The source fixes a Jordan splitting of the dyadic lattice, separates its
exponent-zero summands from the positive-exponent tail, and then scales the
form by two.  Sweep III records those selected pieces and their scaled
versions.  Existence of a dyadic Jordan splitting, comparison of the two
orthogonal-sum presentations, and the `1/2` relation between the resulting
discriminant forms are result-layer statements and are not proved here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Lattices.Valued

universe u

variable {R W : Type u} [CommRing R] [AddCommGroup W] [Module R W]

/-- Scale a finite-projective lattice without changing its carrier module.

This is the finite-projective owner of the already existing `scaleLattice`
construction; finiteness is inherited because scaling changes only the form. -/
def scaleFiniteProjectiveLatticeData
    (L : FiniteProjectiveLatticeCat R W) (a : R) :
    FiniteProjectiveLatticeCat R W :=
  ⟨scaleLattice L.obj a, L.property⟩

private instance primeTwoFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- A chosen Jordan splitting at the dyadic uniformizer `2`.  The existence
of such a splitting is not part of this definition. -/
abbrev DyadicJordanData
    (L₂ : FiniteProjectiveLatticeCat ℤ_[2] ℤ_[2]) (n : ℕ) :=
  JordanDecomposition L₂ (2 : ℤ_[2]) n

namespace DyadicJordanData

variable {L₂ : FiniteProjectiveLatticeCat ℤ_[2] ℤ_[2]} {n : ℕ}

/-- The exponent-zero part `L₂^(0)` of the chosen dyadic Jordan splitting. -/
def exponentZeroPart (J : DyadicJordanData L₂ n) :
    FiniteProjectiveLatticeCat ℤ_[2] ℤ_[2] :=
  finiteProjectiveIndexedOrthogonalSum
    (fun i : {i : Fin n // J.exponent i = 0} ↦ J.component i.1)

/-- The positive-exponent tail `L₂^(≥1)` of the chosen dyadic Jordan
splitting. -/
def positivePart (J : DyadicJordanData L₂ n) :
    FiniteProjectiveLatticeCat ℤ_[2] ℤ_[2] :=
  finiteProjectiveIndexedOrthogonalSum
    (fun i : {i : Fin n // 1 ≤ J.exponent i} ↦ J.component i.1)

/-- The displayed split presentation `L₂^(0) ⊕ L₂^(≥1)`.

The comparison of this presentation with `L₂` follows from the supplied
Jordan decomposition; it is not built into this Sweep-III datum. -/
def split (J : DyadicJordanData L₂ n) :
    FiniteProjectiveLatticeCat ℤ_[2] ℤ_[2] :=
  finiteProjectiveOrthogonalSum J.exponentZeroPart J.positivePart

/-- The scaled dyadic lattice `𝐋₂ = L₂(2)`. -/
def scaledLattice (_J : DyadicJordanData L₂ n) :
    FiniteProjectiveLatticeCat ℤ_[2] ℤ_[2] :=
  scaleFiniteProjectiveLatticeData L₂ (2 : ℤ_[2])

/-- The exponent-one piece `𝐋₂^(1) = L₂^(0)(2)`. -/
def exponentOnePart (J : DyadicJordanData L₂ n) :
    FiniteProjectiveLatticeCat ℤ_[2] ℤ_[2] :=
  scaleFiniteProjectiveLatticeData J.exponentZeroPart (2 : ℤ_[2])

/-- The scaled positive tail `𝐋₂^(≥2) = L₂^(≥1)(2)`. -/
def atLeastTwoPart (J : DyadicJordanData L₂ n) :
    FiniteProjectiveLatticeCat ℤ_[2] ℤ_[2] :=
  scaleFiniteProjectiveLatticeData J.positivePart (2 : ℤ_[2])

/-- The displayed scaled split `𝐋₂^(1) ⊕ 𝐋₂^(≥2)` as raw lattice data.

Its comparison with `scaledLattice J` is a result about the chosen Jordan
decomposition, so Sweep III deliberately does not package an isomorphism. -/
def scaledSplit (J : DyadicJordanData L₂ n) :
    FiniteProjectiveLatticeCat ℤ_[2] ℤ_[2] :=
  finiteProjectiveOrthogonalSum J.exponentOnePart J.atLeastTwoPart

end DyadicJordanData

end LeanCategories.Lattices.Valued
