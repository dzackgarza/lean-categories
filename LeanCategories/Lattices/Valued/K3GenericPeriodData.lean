/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.K3PeriodDomainData
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Generic K3 period-point data

Peters--Sterk FC11-C20-U015 (Definition 20.1.8), on the corrected
projective-line K3 period carrier.

For a lattice `S ⊂ Λ`, put `T = S⊥`.  The field `K_ρ` is generated over
`ℚ` by the primitive roots of unity whose orders `m` satisfy
`φ(m) ≤ 22 - ρ`.  A period point in `D(S⊥)` is `K_ρ`-generic when its
period line is contained in no proper integral sublattice of `T` after
complexification and the line is not defined over `K_ρ`.

Only these two defining conditions are recorded here.  The Picard-rank and
automorphism-group consequences following Definition 20.1.8 are result
content and are deliberately absent.
-/

@[expose] public noncomputable section

namespace LeanCategories.Lattices.Valued

/-- The source field
`K_ρ = ℚ({ζ_m | φ(m) ≤ 22 - ρ}) ⊂ ℂ`.

Using all primitive roots of an admissible order expresses the source prose
"adjoining ... all primitive `m`-th roots of unity" without choosing a
particular primitive root. -/
def k3AutomorphismGenericFieldData (ρ : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ
    {ζ : ℂ | ∃ m : ℕ, Nat.totient m ≤ 22 - ρ ∧ IsPrimitiveRoot ζ m}

/-- The transcendental lattice `T = S⊥` attached to the fixed integral
sublattice `S ⊂ Λ`. -/
def k3TranscendentalLatticeData
    (S : Submodule ℤ k3Lattice.obj.carrier) :
    Submodule ℤ k3Lattice.obj.carrier :=
  orthogonalSubmodule k3Lattice S

/-- Period points of the source domain `D(S⊥)`, packaged as a subtype of the
corrected K3 projective-line period carrier. -/
abbrev K3SMarkedPeriodPointData
    (S : Submodule ℤ k3Lattice.obj.carrier) :=
  {p : K3PeriodPointData // p ∈ k3LatticeMarkedPeriodDomainData S}

/-- The integral rank `ρ = rank(S)` used in Definition 20.1.8. -/
def k3PeriodLatticeRankData
    (S : Submodule ℤ k3Lattice.obj.carrier) : ℕ :=
  Module.finrank ℤ S

/-- The first condition in Definition 20.1.8: the period line is contained in
the complexification of no proper integral sublattice of `T = S⊥`. -/
def k3PeriodLineAvoidsProperTranscendentalSublatticeData
    (S : Submodule ℤ k3Lattice.obj.carrier)
    (p : K3PeriodPointData) : Prop :=
  ¬ ∃ T' : Submodule ℤ k3Lattice.obj.carrier,
    T' < k3TranscendentalLatticeData S ∧
      p.val.submodule ≤ T'.baseChange ℂ

/-- A projective K3 period line is defined over an intermediate field
`K ⊂ ℂ` when it has a nonzero generator whose coordinates in the fixed
integral K3 basis all lie in `K`.

Because the basis is defined over `ℤ ⊂ ℚ ⊂ K`, this is the direct
coordinate form of descent for a one-dimensional subspace; no choice of a
projective representative is built into the period carrier itself. -/
def k3PeriodLineDefinedOverData
    (K : IntermediateField ℚ ℂ) (p : K3PeriodPointData) : Prop :=
  ∃ v ∈ p.val.submodule, v ≠ 0 ∧
    ∀ i : K3Index, (k3Basis.baseChange ℂ).repr v i ∈ K

/-- Definition 20.1.8.  A point of `D(S⊥)` is `K_ρ`-generic, with
`ρ = rank(S)`, when it satisfies the two source conditions. -/
def IsK3GenericPeriodData
    (S : Submodule ℤ k3Lattice.obj.carrier)
    (p : K3SMarkedPeriodPointData S) : Prop :=
  k3PeriodLineAvoidsProperTranscendentalSublatticeData S p.1 ∧
    ¬ k3PeriodLineDefinedOverData
      (k3AutomorphismGenericFieldData (k3PeriodLatticeRankData S)) p.1

end LeanCategories.Lattices.Valued
