/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.K3ArithmeticPeriodQuotientData
public import LeanCategories.Lattices.Valued.K3StrongMarkingCoverData
public import Mathlib.Topology.Sets.Closeds

/-!
# Rational SBB boundary data for degree-two K3 periods

Definition-level realization of Peters--Sterk FC11-C19-U035.

Fix a primitive degree-two polarization class. Its orthogonal lattice is the
source lattice Lambda_2. Peters--Sterk describe the rational SBB boundary
components as those indexed by nonzero primitive isotropic sublattices
I <= Lambda_2, with projective closure

P(I_C) intersect closure(D(Lambda_2)).

This file records exactly that set-level data.

* The complexification of Lambda_2 receives the topology induced by its
  canonical scalar-extension inclusion into the already-topologized K3
  complexification.
* Its projectivization receives the ordinary quotient topology on nonzero
  vectors.
* A rational boundary-component datum is a nonzero primitive isotropic
  sublattice I.
* k3DegreeTwoRationalBoundaryClosureData is literally the source projective
  closure formula.
* The set-level compactified carrier is the ordinary type-IV period domain
  together with all of these rational boundary closures.

The signature argument implying that such I have rank one or two, the
point/half-plane descriptions, the incidence statement for nested isotropic
sublattices, the Satake--Baily--Borel topology, compactness and analytic or
algebraic structure of the arithmetic quotient are result-layer content and
are not proved or bundled in Sweep III.
-/

@[expose] public noncomputable section

namespace LeanCategories.Lattices.Valued

/-- Peters--Sterk's degree-two orthogonal lattice Lambda_2, relative to the
supplied primitive degree-two polarization class. -/
noncomputable abbrev K3DegreeTwoOrthogonalFormData
    (ell : K3DegreePolarizationClassData 1) :=
  K3DegreePolarizationOrthogonalFormData 1 ell

/-- The canonical inclusion of the complexified degree-two orthogonal lattice
into the complexified K3 lattice. -/
noncomputable def k3DegreeTwoOrthogonalComplexificationInclusionData
    (ell : K3DegreePolarizationClassData 1) :
    LatticeComplexificationData (K3DegreeTwoOrthogonalFormData ell).carrier →ₗ[ℂ]
      LatticeComplexificationData k3Lattice.obj.carrier :=
  (orthogonalSubmodule k3Lattice
    (Submodule.span ℤ {ell.vector})).subtype.baseChange ℂ

/-- The finite-dimensional topology on Lambda_2 tensor C, induced from its
canonical inclusion into the fixed K3 complexification. -/
noncomputable instance k3DegreeTwoOrthogonalComplexificationTopologicalSpace
    (ell : K3DegreePolarizationClassData 1) :
    TopologicalSpace
      (LatticeComplexificationData (K3DegreeTwoOrthogonalFormData ell).carrier) :=
  TopologicalSpace.induced
    (k3DegreeTwoOrthogonalComplexificationInclusionData ell) inferInstance

/-- Quotient topology on the projectivization of Lambda_2 tensor C. -/
noncomputable instance k3DegreeTwoProjectiveAmbientTopologicalSpace
    (ell : K3DegreePolarizationClassData 1) :
    TopologicalSpace
      (Projectivization ℂ
        (LatticeComplexificationData (K3DegreeTwoOrthogonalFormData ell).carrier)) :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient
        (projectivizationSetoid ℂ
          (LatticeComplexificationData
            (K3DegreeTwoOrthogonalFormData ell).carrier))))

/-- A rational SBB boundary-component label: a nonzero primitive isotropic
integral sublattice of Lambda_2.

The source later proves that only ranks one and two occur. That theorem is
not a field of this definition. -/
structure K3DegreeTwoRationalBoundaryComponentData
    (ell : K3DegreePolarizationClassData 1) where
  sublattice : Submodule ℤ (K3DegreeTwoOrthogonalFormData ell).carrier
  primitive : IsPrimitiveSubmodule sublattice
  nonzero : sublattice ≠ ⊥
  isotropic :
    ∀ x ∈ sublattice, ∀ y ∈ sublattice,
      (K3DegreeTwoOrthogonalFormData ell).pairing x y = 0

/-- The integral rank of the isotropic sublattice indexing a rational boundary
component. The assertion that this rank is one or two is result content. -/
def k3DegreeTwoRationalBoundaryRankData
    {ell : K3DegreePolarizationClassData 1}
    (B : K3DegreeTwoRationalBoundaryComponentData ell) : ℕ :=
  Module.finrank ℤ B.sublattice

/-- The projectivization P(I_C) of the complexified isotropic sublattice,
viewed as a subset of the ambient projectivization of Lambda_2 tensor C. -/
def k3DegreeTwoBoundaryProjectiveSubspaceData
    (ell : K3DegreePolarizationClassData 1)
    (B : K3DegreeTwoRationalBoundaryComponentData ell) :
    Set (Projectivization ℂ
      (LatticeComplexificationData (K3DegreeTwoOrthogonalFormData ell).carrier)) :=
  {p | p.submodule ≤ B.sublattice.baseChange ℂ}

/-- The ordinary type-IV period-domain carrier D(Lambda_2) inside its
ambient projectivization. -/
def k3DegreeTwoPeriodDomainAmbientData
    (ell : K3DegreePolarizationClassData 1) :
    Set (Projectivization ℂ
      (LatticeComplexificationData (K3DegreeTwoOrthogonalFormData ell).carrier)) :=
  latticePeriodDomainData (K3DegreeTwoOrthogonalFormData ell).bilinMap

/-- Peters--Sterk's source closure formula:
closure(F_I) = P(I_C) intersect closure(D(Lambda_2)). -/
def k3DegreeTwoRationalBoundaryClosureData
    (ell : K3DegreePolarizationClassData 1)
    (B : K3DegreeTwoRationalBoundaryComponentData ell) :
    Set (Projectivization ℂ
      (LatticeComplexificationData (K3DegreeTwoOrthogonalFormData ell).carrier)) :=
  k3DegreeTwoBoundaryProjectiveSubspaceData ell B ∩
    closure (k3DegreeTwoPeriodDomainAmbientData ell)

/-- The set-level union of all rational SBB boundary closures. -/
def k3DegreeTwoSBBBoundaryCarrierData
    (ell : K3DegreePolarizationClassData 1) :
    Set (Projectivization ℂ
      (LatticeComplexificationData (K3DegreeTwoOrthogonalFormData ell).carrier)) :=
  ⋃ B : K3DegreeTwoRationalBoundaryComponentData ell,
    k3DegreeTwoRationalBoundaryClosureData ell B

/-- The set-level SBB compactified carrier obtained by adjoining all rational
boundary-component closures to the ordinary period domain.

No SBB topology is asserted by this definition. -/
def k3DegreeTwoSBBCompactifiedCarrierData
    (ell : K3DegreePolarizationClassData 1) :
    Set (Projectivization ℂ
      (LatticeComplexificationData (K3DegreeTwoOrthogonalFormData ell).carrier)) :=
  k3DegreeTwoPeriodDomainAmbientData ell ∪
    k3DegreeTwoSBBBoundaryCarrierData ell

end LeanCategories.Lattices.Valued
