/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.PeriodDomainData
public import LeanCategories.Lattices.Valued.Standard

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
dimensions and genericity assertions remain result clauses. Original-text
acceptance and target-pin validation remain open.
-/

@[expose] public noncomputable section

namespace LeanCategories.Lattices.Valued

/-- Period points of the repository's fixed K3 intersection lattice. -/
abbrev K3PeriodPointData := LatticePeriodPointData k3Lattice.obj.bilinMap

/-- The positive-class period locus from U021. The chosen class remains
of type `(1,1)` through the defining orthogonality condition. -/
def k3PolarizedPeriodDomainData (ℓ : k3Lattice.obj.carrier)
    (_hℓ : 0 < k3Lattice.obj.pairing ℓ ℓ) : Set K3PeriodPointData :=
  {p | ℓ ∈ latticePeriodNeronSeveriData k3Lattice.obj.bilinMap p}

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
