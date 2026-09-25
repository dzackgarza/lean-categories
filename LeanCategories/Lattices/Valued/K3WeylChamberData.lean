/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.K3PeriodDomainData
public import Mathlib.Topology.Connected.Basic

/-!
# K3 period-point Weyl-chamber data

Peters--Sterk FC11-C19-U031, at the corrected projective-line K3 period
carrier.  For a period point, the real `(1,1)` space is represented in the
fixed K3 basis by real coordinate vectors orthogonal to the period line.  Its
light cone is cut by the hyperplanes of the integral square-`-2` roots in
`NS(u)`; the connected components of that complement are the supplementary
signed Weyl chambers over the period point.

The constructions below are data-level only.  They do not assert that the
light cone has exactly two components, that the displayed root halves exhaust
the roots, that chamber closures are fundamental domains, or that these
chambers are realized by strongly marked K3 surfaces.  Those are result
clauses outside Sweep III.
-/

@[expose] public noncomputable section

open scoped BigOperators TensorProduct

namespace LeanCategories.Lattices.Valued

/-- The fixed real coordinate model of the K3 lattice scalar extension. -/
abbrev K3RealPeriodAmbientData := K3Index → ℝ

/-- The real coordinate vector as an element of `ℝ ⊗[ℤ] Λ`, using the
repository's fixed K3 basis. -/
def k3RealCoordinateToRealificationData (x : K3RealPeriodAmbientData) :
    ℝ ⊗[ℤ] k3Lattice.obj.carrier :=
  ∑ i : K3Index, x i ⊗ₜ[ℤ] k3Basis i

/-- The same real coordinate vector in the complexification used by the
period-line carrier. -/
def k3RealCoordinateToComplexificationData (x : K3RealPeriodAmbientData) :
    LatticeComplexificationData k3Lattice.obj.carrier :=
  ∑ i : K3Index, (x i : ℂ) ⊗ₜ[ℤ] k3Basis i

/-- Integral K3-lattice coordinates viewed as real coordinates. -/
def k3IntegralRealCoordinatesData (x : k3Lattice.obj.carrier) :
    K3RealPeriodAmbientData :=
  fun i ↦ (k3Basis.repr x i : ℝ)

/-- The K3 intersection form on the fixed real coordinate model. -/
def k3RealPeriodPairingData :
    K3RealPeriodAmbientData → K3RealPeriodAmbientData → ℝ :=
  fun x y ↦
    (LinearMap.BilinForm.baseChange ℝ k3Lattice.obj.bilinMap)
      (k3RealCoordinateToRealificationData x)
      (k3RealCoordinateToRealificationData y)

/-- The real `(1,1)` locus `Λ_{u,ℝ}^{1,1}`: real vectors orthogonal to
the actual projective period line. -/
def k3PeriodRealH11Data (p : K3PeriodPointData) :
    Set K3RealPeriodAmbientData :=
  {x | ∀ v ∈ p.val.submodule,
    (LinearMap.BilinForm.baseChange ℂ k3Lattice.obj.bilinMap)
      (k3RealCoordinateToComplexificationData x) v = 0}

/-- The light cone in the real `(1,1)` locus at a period point. -/
def k3PeriodLightConeData (p : K3PeriodPointData) :
    Set K3RealPeriodAmbientData :=
  {x | x ∈ k3PeriodRealH11Data p ∧ 0 < k3RealPeriodPairingData x x}

/-- The connected components of the light cone.  Peters--Sterk denotes the
two components by `±C_u`; the assertion that there are exactly two is not
needed to construct their collection. -/
def k3PeriodLightConeComponentsData (p : K3PeriodPointData) :
    Set (Set K3RealPeriodAmbientData) :=
  Set.range fun x : k3PeriodLightConeData p ↦
    connectedComponentIn (k3PeriodLightConeData p) x.1

/-- The square-`-2` roots in the integral orthogonality lattice `NS(u)`. -/
def k3PeriodRootSetData (p : K3PeriodPointData) :
    Set k3Lattice.obj.carrier :=
  {r | r ∈ k3NeronSeveriLatticeData p ∧ k3Lattice.obj.pairing r r = -2}

/-- The real reflection hyperplane orthogonal to an integral K3 root. -/
def k3PeriodRootHyperplaneData (r : k3Lattice.obj.carrier) :
    Set K3RealPeriodAmbientData :=
  {x | k3RealPeriodPairingData x (k3IntegralRealCoordinatesData r) = 0}

/-- The union of all reflection hyperplanes for roots orthogonal to the
period line. -/
def k3PeriodRootHyperplaneArrangementData (p : K3PeriodPointData) :
    Set K3RealPeriodAmbientData :=
  ⋃ r ∈ k3PeriodRootSetData p, k3PeriodRootHyperplaneData r

/-- The light cone with all period-orthogonal root hyperplanes removed. -/
def k3PeriodWeylRegularLocusData (p : K3PeriodPointData) :
    Set K3RealPeriodAmbientData :=
  k3PeriodLightConeData p \ k3PeriodRootHyperplaneArrangementData p

/-- The root-hyperplane complement inside one light-cone component. -/
def k3PeriodWeylRegularLocusInComponentData (p : K3PeriodPointData)
    (C : Set K3RealPeriodAmbientData) : Set K3RealPeriodAmbientData :=
  C \ k3PeriodRootHyperplaneArrangementData p

/-- The Weyl chambers inside one chosen light-cone component.  When the root
set is empty, this construction reduces to the connected components of that
light-cone component, matching the source convention without a special case. -/
def k3PeriodWeylChambersInComponentData (p : K3PeriodPointData)
    (C : Set K3RealPeriodAmbientData) :
    Set (Set K3RealPeriodAmbientData) :=
  Set.range fun x : k3PeriodWeylRegularLocusInComponentData p C ↦
    connectedComponentIn (k3PeriodWeylRegularLocusInComponentData p C) x.1

/-- The signed Weyl chambers over a period point: connected components of the
root-hyperplane complement in each light-cone component.  Taking all
light-cone components keeps both source signs without choosing one. -/
def k3PeriodSignedWeylChambersData (p : K3PeriodPointData) :
    Set (Set K3RealPeriodAmbientData) :=
  ⋃ C ∈ k3PeriodLightConeComponentsData p,
    k3PeriodWeylChambersInComponentData p C

/-- The supplementary chamber fibre over a period point in FC11-C19-U031. -/
abbrev k3StrongMarkingChamberFiberData (p : K3PeriodPointData) :
    Set (Set K3RealPeriodAmbientData) :=
  k3PeriodSignedWeylChambersData p

/-- The root half selected by a chamber: the roots pairing positively with
every point of that chamber. -/
def k3PeriodChamberPositiveRootsData (p : K3PeriodPointData)
    (C : Set K3RealPeriodAmbientData) : Set k3Lattice.obj.carrier :=
  {r | r ∈ k3PeriodRootSetData p ∧
    ∀ x ∈ C, 0 < k3RealPeriodPairingData x (k3IntegralRealCoordinatesData r)}

/-- The opposite root half attached to the same chamber. -/
def k3PeriodChamberNegativeRootsData (p : K3PeriodPointData)
    (C : Set K3RealPeriodAmbientData) : Set k3Lattice.obj.carrier :=
  {r | -r ∈ k3PeriodChamberPositiveRootsData p C}

/-- The ordered pair `(Δ_u^P,-Δ_u^P)` associated to a chamber.  Exhaustion
and disjointness are theorem content and are deliberately not constructor
fields. -/
def k3PeriodChamberRootPartitionData (p : K3PeriodPointData)
    (C : Set K3RealPeriodAmbientData) :
    Set k3Lattice.obj.carrier × Set k3Lattice.obj.carrier :=
  (k3PeriodChamberPositiveRootsData p C,
    k3PeriodChamberNegativeRootsData p C)

end LeanCategories.Lattices.Valued
