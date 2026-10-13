/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.K3PeriodDomainData
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Enriques period-domain hyperplane data

Definition-level realization of Peters--Sterk FC11-C21-U019 on the corrected
projective-line K3 period carrier.

The standard K3 decomposition used by the source is
`Λ = U₀ ⊥ (U₁ ⊥ E₈,₀(-1)) ⊥ (U₂ ⊥ E₈,₁(-1))`.  The lattice Enriques
involution negates `U₀` and swaps the last two factors.  Hence its
anti-invariant eigenspace is described, in the fixed K3 basis, by opposite
coordinates on the two exchanged `U` and `E₈` factors.  This coordinate
description lets the period-domain and root-hyperplane constructions be
formed without packaging or proving an isometry law for the involution.

The equality of the resulting hyperplane intersection with the geometric
nodal-type stratum `{[ω] | Δ_ω = Δ}` is result content and is not asserted
here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Lattices.Valued

/-- Integral vectors in the anti-invariant lattice of the standard Enriques
involution on the K3 lattice.  The first hyperbolic-plane coordinate is free
because that summand is negated; the other two hyperbolic planes and the two
`E₈(-1)` summands occur with opposite coordinates. -/
def IsK3EnriquesAntiInvariantIntegralData
    (x : k3Lattice.obj.carrier) : Prop :=
  (∀ a : Fin 2,
    k3Basis.repr x (Sum.inl ⟨1, a⟩) =
      -k3Basis.repr x (Sum.inl ⟨2, a⟩)) ∧
  (∀ a : Fin 8,
    k3Basis.repr x (Sum.inr ⟨0, a⟩) =
      -k3Basis.repr x (Sum.inr ⟨1, a⟩))

/-- Complex vectors in the complexified anti-invariant lattice of the
standard Enriques involution. -/
def IsK3EnriquesAntiInvariantComplexData
    (v : LatticeComplexificationData k3Lattice.obj.carrier) : Prop :=
  (∀ a : Fin 2,
    (k3Basis.baseChange ℂ).repr v (Sum.inl ⟨1, a⟩) =
      -(k3Basis.baseChange ℂ).repr v (Sum.inl ⟨2, a⟩)) ∧
  (∀ a : Fin 8,
    (k3Basis.baseChange ℂ).repr v (Sum.inr ⟨0, a⟩) =
      -(k3Basis.baseChange ℂ).repr v (Sum.inr ⟨1, a⟩))

/-- The type-IV K3 period locus whose projective period line lies in the
anti-invariant complex subspace for the standard Enriques involution. -/
def k3EnriquesAntiInvariantPeriodLocusData : Set K3PeriodPointData :=
  {p | ∀ v ∈ p.val.submodule, IsK3EnriquesAntiInvariantComplexData v}

/-- Square-`-2` roots in the integral anti-invariant lattice. -/
def k3EnriquesAntiInvariantRootSetData :
    Set k3Lattice.obj.carrier :=
  {r |
    IsK3EnriquesAntiInvariantIntegralData r ∧
      k3Lattice.obj.pairing r r = -2}

/-- The period hyperplane cut out by an integral K3-lattice vector.  Membership
is representation-independent because `k3NeronSeveriLatticeData` uses the
whole projective period line. -/
def k3PeriodRootHyperplanePeriodData
    (r : k3Lattice.obj.carrier) : Set K3PeriodPointData :=
  {p | r ∈ k3NeronSeveriLatticeData p}

/-- The Enriques period domain `D_Enr`: the anti-invariant type-IV locus with
the hyperplanes of anti-invariant square-`-2` roots removed. -/
def k3EnriquesPeriodDomainData : Set K3PeriodPointData :=
  {p |
    p ∈ k3EnriquesAntiInvariantPeriodLocusData ∧
      ∀ r ∈ k3EnriquesAntiInvariantRootSetData,
        p ∉ k3PeriodRootHyperplanePeriodData r}

/-- FC11-C21-U019: the intersection of the Enriques period domain with the
hyperplanes indexed by the supplied anti-invariant root differences
`Δ⁻`.  The vectors in `Δ⁻` need not themselves have square `-2`
(adapted pairs give square `-4` vectors), so the construction deliberately
accepts their set directly. -/
def k3EnriquesRootHyperplaneIntersectionData
    (Δminus : Set k3Lattice.obj.carrier) : Set K3PeriodPointData :=
  {p |
    p ∈ k3EnriquesPeriodDomainData ∧
      ∀ r ∈ Δminus, p ∈ k3PeriodRootHyperplanePeriodData r}

/-- FC11-C21-U030: for the primitive lattice `S` attached to a fixed nodal
type, the Enriques period domain is exactly the intersection
`D(S) ∩ D_Enr`.  The subsequent generic Néron--Severi and codimension
statements are not part of this constructor. -/
def k3EnriquesLatticeMarkedPeriodDomainData
    (S : Submodule ℤ k3Lattice.obj.carrier) : Set K3PeriodPointData :=
  k3LatticeMarkedPeriodDomainData S ∩ k3EnriquesPeriodDomainData

end LeanCategories.Lattices.Valued
