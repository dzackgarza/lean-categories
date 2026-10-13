/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.MilnorFiberHomologyData
public import LeanCategories.Topology.SingularLinkingNumberData
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Geometric intersection data for the Milnor fibre

Definition-level completion of Peters--Sterk FC11-C18-U025.

The actual Milnor fibre and its integral middle homology are constructed in
MilnorFiberData and MilnorFiberHomologyData. What remains in the source
definition is the geometric middle-dimensional intersection pairing.

The repository already represents geometric chain intersection in
SingularLinkingNumberData: because Mathlib has no manifold-chain
transversality/intersection-number API, an oriented transverse-intersection
operation is explicit low-level geometric data. This file reuses the same
owner in degrees (n,n). It does not accept a bilinear form on homology.
Instead a candidate homology pairing is characterized by the requirement that
on every pair of transverse middle-cycle representatives its value is exactly
their oriented chain intersection number.

Existence of transverse representatives, independence of representatives,
descent of the geometric intersection number to homology, bilinearity,
symmetry for even n, freeness/rank of middle homology, and nondegeneracy
properties are result-layer statements and are not proved in Sweep III.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology

namespace LeanCategories.Topology

/-- The integral singular chain complex of the actual Milnor fibre. -/
abbrev milnorIntegralSingularChainComplexData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (singularChainFunctor ℤ).obj (TopCat.of (MilnorFiberData f eta t))

/-- Concrete middle cycles of the Milnor fibre, before quotienting by
boundaries. -/
abbrev MilnorMiddleCycleData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r) :=
  (forget₂ (ModuleCat.{0} ℤ) Ab).obj
    ((milnorIntegralSingularChainComplexData f eta t).cycles n)

/-- The underlying singular middle chain of a cycle representative. -/
def milnorMiddleCycleChainData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r)
    (z : MilnorMiddleCycleData f eta t) :
    IntegralSingularChain (MilnorFiberData f eta t) n :=
  (forget₂ (ModuleCat.{0} ℤ) Ab).map
    ((milnorIntegralSingularChainComplexData f eta t).iCycles n) z

/-- The middle-homology class represented by a concrete middle cycle. -/
def milnorMiddleCycleClassData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r)
    (z : MilnorMiddleCycleData f eta t) :
    (forget₂ (ModuleCat.{0} ℤ) Ab).obj
      (milnorIntegralMiddleHomologyData f eta t) :=
  (forget₂ (ModuleCat.{0} ℤ) Ab).map
    ((milnorIntegralSingularChainComplexData f eta t).homologyπ n) z

/-- Geometric transverse-intersection input specialized to middle-dimensional
chains in the Milnor fibre. -/
abbrev MilnorMiddleIntersectionData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r) :=
  SingularChainIntersectionDataInDegrees
    (MilnorFiberData f eta t) n n

/-- Raw candidate for the source intersection pairing on actual middle
homology. No bilinearity or symmetry is built into this carrier. -/
abbrev MilnorIntersectionPairingCandidateData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r) :=
  (forget₂ (ModuleCat.{0} ℤ) Ab).obj
      (milnorIntegralMiddleHomologyData f eta t) →
    (forget₂ (ModuleCat.{0} ℤ) Ab).obj
      (milnorIntegralMiddleHomologyData f eta t) →
    ℤ

/-- Exact representative-level graph for the geometric Milnor intersection
pairing: whenever two middle-cycle representatives meet transversely, the
homology pairing is their oriented chain intersection number. -/
def IsMilnorIntersectionPairingData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r)
    (I : MilnorMiddleIntersectionData f eta t)
    (pairing : MilnorIntersectionPairingCandidateData f eta t) : Prop :=
  ∀ (z w : MilnorMiddleCycleData f eta t)
    (hzw : I.Transverse
      (milnorMiddleCycleChainData f eta t z)
      (milnorMiddleCycleChainData f eta t w)),
    pairing
      (milnorMiddleCycleClassData f eta t z)
      (milnorMiddleCycleClassData f eta t w) =
        I.intersectionNumber
          (milnorMiddleCycleChainData f eta t z)
          (milnorMiddleCycleChainData f eta t w) hzw

/-- Peters--Sterk's geometric middle-homology pairing, selected by its exact
transverse-representative graph. The source section is restricted to even
complex dimension; hEven records that scope without turning symmetry into a
constructor proof. -/
noncomputable def milnorIntersectionPairingData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r) (_hEven : Even n)
    (I : MilnorMiddleIntersectionData f eta t) :
    MilnorIntersectionPairingCandidateData f eta t :=
  Classical.epsilon (IsMilnorIntersectionPairingData f eta t I)

/-- The source-facing raw Milnor-lattice datum (H_n(M_*; Z), dot).

The carrier is the actual native middle homology from U025 and the pairing is
the geometric pairing above. Freeness and the symmetric-bilinear lattice laws
remain results rather than structure fields. -/
structure MilnorLatticeData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r) where
  pairing : MilnorIntersectionPairingCandidateData f eta t

/-- The raw Milnor-lattice datum determined by the geometric intersection
operation in even complex dimension. -/
noncomputable def milnorLatticeData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r) (hEven : Even n)
    (I : MilnorMiddleIntersectionData f eta t) :
    MilnorLatticeData f eta t where
  pairing := milnorIntersectionPairingData f eta t hEven I

end LeanCategories.Topology
