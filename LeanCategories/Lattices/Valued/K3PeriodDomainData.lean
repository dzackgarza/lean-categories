/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.PeriodDomainData
public import LeanCategories.Lattices.Valued.Standard
public import LeanCategories.Lattices.Valued.Sublattice

/-!
# Fixed-lattice K3 period-domain data

Peters--Sterk FC11-C19-U021/U025/U033, at the existing actual K3 lattice
`3U ⊥ 2E₈(-1)`. The ambient points are the positive isotropic projective
lines of its complexified intersection form, not Hodge structures polarized
by that form on the entire lattice.

A fixed positive class cuts out its orthogonal period locus. A fixed
integral sublattice cuts out `D(S⊥)`. The integral vectors orthogonal to a
period line form `NS(u)`. All three constructions reuse the same native
complexification, projective-line and linear-kernel data. No arbitrary
period set, pairing, class map, or Néron--Severi module is supplied.

These are set/lattice definitions, not the root-hyperplane complement for
ample polarizations, an analytic period space, an arithmetic quotient, or
an identification with geometric moduli. Their geometric interpretations,
dimensions and genericity assertions remain result clauses. The U021
fixed-positive-class locus was checked against Peters--Sterk, Version JUNE
2024, printed pp. 346--347, and elaborates at the repository's pinned target.
U025/U033 retain their own source-conformance acceptance gates.
-/

@[expose] public noncomputable section

namespace LeanCategories.Lattices.Valued

/-- Period points of the repository's fixed K3 intersection lattice. -/
abbrev K3PeriodPointData := LatticePeriodPointData k3Lattice.obj.bilinMap

/-- The positive-class period locus underlying U021. The chosen class remains
of type `(1,1)` through the defining orthogonality condition. The exact
primitive degree-`2k` source specialization is `K3DegreePolarizationClassData`
and `k3DegreePolarizedPeriodDomainData` below. -/
def k3PolarizedPeriodDomainData (ℓ : k3Lattice.obj.carrier)
    (_hℓ : 0 < k3Lattice.obj.pairing ℓ ℓ) : Set K3PeriodPointData :=
  {p | ℓ ∈ latticePeriodNeronSeveriData k3Lattice.obj.bilinMap p}

/-- Peters--Sterk's lattice datum for a degree-`2k` polarization
(`FC11-C19-U021`): a primitive integral K3-lattice vector of positive
square `2k`.

This records only the period-side lattice input. Whether such a vector is
the marked class of an ample divisor is geometric result data and is not
part of this Sweep-III construction. -/
structure K3DegreePolarizationClassData (k : ℕ) where
  /-- The fixed integral class `ℓ ∈ Λ`. -/
  vector : k3Lattice.obj.carrier
  /-- The source assumes that `ℓ` is primitive. -/
  primitive : IsPrimitiveSubmodule (Submodule.span ℤ {vector})
  /-- The fixed class has positive square. -/
  positive : 0 < k3Lattice.obj.pairing vector vector
  /-- The polarization degree is the source normalization `ℓ · ℓ = 2k`. -/
  square : k3Lattice.obj.pairing vector vector = 2 * (k : ℤ)

/-- The degree-`2k` period domain
`D(ℓ⊥) = {[u] ∈ D(Λ) | u · ℓ = 0}` from `FC11-C19-U021`.

The definition is the orthogonality locus of the actual primitive
degree-`2k` class. The one-orbit statement for such classes and the
geometric polarization interpretation remain result clauses. -/
def k3DegreePolarizedPeriodDomainData (k : ℕ)
    (ℓ : K3DegreePolarizationClassData k) : Set K3PeriodPointData :=
  {p | ℓ.vector ∈ latticePeriodNeronSeveriData k3Lattice.obj.bilinMap p}

/-- The U025 period locus orthogonal to the specified sublattice of the
actual K3 lattice. The source's primitive-embedding and signature conditions
specialize this construction; they are not replaced by classification data. -/
def k3LatticeMarkedPeriodDomainData
    (S : Submodule ℤ k3Lattice.obj.carrier) : Set K3PeriodPointData :=
  latticePeriodOrthogonalDomainData k3Lattice.obj.bilinMap S

/-- The U033 integral orthogonality lattice at a K3 period point. -/
def k3NeronSeveriLatticeData (p : K3PeriodPointData) :
    Submodule ℤ k3Lattice.obj.carrier :=
  latticePeriodNeronSeveriData k3Lattice.obj.bilinMap p

end LeanCategories.Lattices.Valued
