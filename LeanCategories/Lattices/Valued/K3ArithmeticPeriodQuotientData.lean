/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.K3PeriodDomainData
public import LeanCategories.Modules.Bilinear.Valued.OrthogonalGroup
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Arithmetic K3 period-quotient data

Peters--Sterk FC11-C19-U022, following the degree-`2k` period domain from
U021.  For a fixed primitive class `ℓ`, the source first passes to the
orthogonal lattice `ℓ⊥`, deletes the hyperplanes perpendicular to its
`(-2)`-roots, and then forms the orbit quotient by `O(ℓ⊥)`.

This file records exactly that data-level construction.  The orthogonal
complement carries the restricted integral form already provided by the
lattice infrastructure.  Its period domain is the existing positive
isotropic projective-line construction.  A root hyperplane is deleted by
requiring the corresponding root not to lie in the integral orthogonality
lattice of the period line.

For each integral isometry, Mathlib's existing `LinearEquiv.baseChange`
and projectivization action give the induced transformation of the ambient
complex projective space.  The arithmetic quotient carrier is represented
as the set of orbit subsets of the open period domain.  This avoids adding
a new proof-valued group-action structure in Sweep III.

Preservation of the period conditions and root complement, the group-action
laws after restriction, proper discontinuity, quasiprojectivity, and the
identification with geometric K3 moduli are proposition/result clauses and
are not asserted here.
-/

@[expose] public noncomputable section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The formed integral module `ℓ⊥` for the fixed degree-`2k` class. -/
abbrev K3DegreePolarizationOrthogonalFormData (k : ℕ)
    (ℓ : K3DegreePolarizationClassData k) :=
  k3Lattice.obj.restrict
    (orthogonalSubmodule k3Lattice (Submodule.span ℤ {ℓ.vector}))

/-- Period points for the orthogonal form `ℓ⊥`. -/
abbrev K3DegreePolarizationOrthogonalPeriodPointData (k : ℕ)
    (ℓ : K3DegreePolarizationClassData k) :=
  LatticePeriodPointData (K3DegreePolarizationOrthogonalFormData k ℓ).bilinMap

/-- The `(-2)`-roots of `ℓ⊥` used in the deleted hyperplane arrangement. -/
def k3DegreePolarizationRootData (k : ℕ)
    (ℓ : K3DegreePolarizationClassData k) :
    Set (K3DegreePolarizationOrthogonalFormData k ℓ).carrier :=
  {r | (K3DegreePolarizationOrthogonalFormData k ℓ).pairing r r = -2}

/-- The source domain
`D°(ℓ⊥) = D(ℓ⊥) - ⋃_{r·r=-2} (r⊥ ∩ D(ℓ⊥))`.

Membership says directly that no `(-2)`-root belongs to the integral
orthogonality lattice of the period line. -/
def k3DegreePolarizedOpenPeriodDomainData (k : ℕ)
    (ℓ : K3DegreePolarizationClassData k) :
    Set (K3DegreePolarizationOrthogonalPeriodPointData k ℓ) :=
  {p | ∀ r ∈ k3DegreePolarizationRootData k ℓ,
    r ∉ latticePeriodNeronSeveriData
      (K3DegreePolarizationOrthogonalFormData k ℓ).bilinMap p}

/-- A point of the deleted degree-`2k` period domain. -/
abbrev K3DegreePolarizedOpenPeriodPointData (k : ℕ)
    (ℓ : K3DegreePolarizationClassData k) :=
  {p : K3DegreePolarizationOrthogonalPeriodPointData k ℓ //
    p ∈ k3DegreePolarizedOpenPeriodDomainData k ℓ}

/-- The ambient projective transformation induced by an element of
`O(ℓ⊥)`: extend the integral isometry to `ℂ`, then use Mathlib's native
action of complex linear equivalences on projective lines. -/
def k3DegreePolarizedProjectiveTransformData (k : ℕ)
    (ℓ : K3DegreePolarizationClassData k)
    (g : BilinModuleCat.OrthogonalGroup
      (K3DegreePolarizationOrthogonalFormData k ℓ))
    (p : Projectivization ℂ
      (LatticeComplexificationData
        (K3DegreePolarizationOrthogonalFormData k ℓ).carrier)) :
    Projectivization ℂ
      (LatticeComplexificationData
        (K3DegreePolarizationOrthogonalFormData k ℓ).carrier) :=
  (g.1.baseChange ℤ ℂ
    (K3DegreePolarizationOrthogonalFormData k ℓ).carrier
    (K3DegreePolarizationOrthogonalFormData k ℓ).carrier) • p

/-- The raw `O(ℓ⊥)`-orbit of an open period point, restricted to the
source domain.  The target point itself carries the open-domain membership;
no invariance theorem is used to construct this set. -/
def k3DegreePolarizedArithmeticOrbitData (k : ℕ)
    (ℓ : K3DegreePolarizationClassData k)
    (p : K3DegreePolarizedOpenPeriodPointData k ℓ) :
    Set (K3DegreePolarizedOpenPeriodPointData k ℓ) :=
  {q | ∃ g : BilinModuleCat.OrthogonalGroup
      (K3DegreePolarizationOrthogonalFormData k ℓ),
    q.1.1 = k3DegreePolarizedProjectiveTransformData k ℓ g p.1.1}

/-- The underlying arithmetic quotient carrier `O(ℓ⊥)\D°(ℓ⊥)`,
represented as the collection of orbit subsets of the open period domain.
No topology, analytic structure, or algebraic-variety structure is added. -/
def k3DegreePolarizedArithmeticQuotientData (k : ℕ)
    (ℓ : K3DegreePolarizationClassData k) :
    Set (Set (K3DegreePolarizedOpenPeriodPointData k ℓ)) :=
  Set.range (k3DegreePolarizedArithmeticOrbitData k ℓ)

end LeanCategories.Lattices.Valued
