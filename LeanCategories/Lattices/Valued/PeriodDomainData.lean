/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The integral-linear conjugation construction is adapted from the Tau Ceti
contributors, Apache-2.0, TauCeti/Geometry/Hodge/Conjugation.lean at revision
f962d4a1e6a5eb6a87cd76a3900bc845df3f5950.
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Positive isotropic period lines of an integral form

This is the projective-line clause of Peters--Sterk FC11-B-U032, used by
FC11-C19-U021/U025/U033. For an integral form `b`, the period points are the
complex lines on which `b_ℂ` vanishes and `b_ℂ(u, conjugate u)` is positive
for every nonzero vector. Orthogonality to a fixed integral class or
sublattice supplies the Chapter-19 subdomains and the lattice `NS(u)`.

Native tensor products and `BilinForm.baseChange` construct the ambient
space and its form. Conjugation is the integral-linear tensor map from the
pinned reference; no conjugate-linearity or involution proof is ported.
Native `Projectivization.submodule` already supplies the actual line, so
the defining conditions quantify over its vectors rather than requiring a
new quotient-descent argument. The integral orthogonality lattice is an
intersection of native linear-map kernels.

TauCeti's `PeriodDomain.Point` is not used as a substitute for this source
carrier. It requires a full Hodge--Riemann polarization with a different
sign convention; its positivity conditions do not describe the full K3
intersection-form domain. No polarization predicate on all of `H²`, Hodge
decomposition, Torelli comparison, or manifold structure is asserted here.
-/

@[expose] public noncomputable section

open scoped TensorProduct ComplexOrder

namespace LeanCategories.Lattices.Valued

universe u

variable (L : Type u) [AddCommGroup L] [Module ℤ L]

/-- The tensor-product complexification of the integral module. -/
abbrev LatticeComplexificationData := ℂ ⊗[ℤ] L

/-- The canonical integral-to-complex map `x ↦ 1 ⊗ x`. -/
def latticeComplexificationMapData : L →ₗ[ℤ] LatticeComplexificationData L :=
  (TensorProduct.mk ℤ ℂ L) 1

/-- The underlying integral-linear conjugation map on the tensor model.
This is the pinned reference's `concreteLatticeConjIntLinear` construction;
its involution and complex-semilinearity assertions remain separate. -/
def latticeConjugationData :
    LatticeComplexificationData L →ₗ[ℤ] LatticeComplexificationData L :=
  TensorProduct.map (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap
    (LinearMap.id : L →ₗ[ℤ] L)

variable {L}

/-- The positive isotropic projective-line locus for the complexified form.
Complex-order positivity includes the requirement that the value be real. -/
def latticePeriodDomainData (b : LinearMap.BilinForm ℤ L) :
    Set (Projectivization ℂ (LatticeComplexificationData L)) :=
  {p | ∀ v ∈ p.submodule,
    b.baseChange ℂ v v = 0 ∧
      (v ≠ 0 → 0 < b.baseChange ℂ v (latticeConjugationData L v))}

/-- An actual complex projective line satisfying the source period
conditions. No vector representative or supplied Hodge filtration is input. -/
abbrev LatticePeriodPointData (b : LinearMap.BilinForm ℤ L) :=
  {p : Projectivization ℂ (LatticeComplexificationData L) //
    p ∈ latticePeriodDomainData b}

/-- The source's integral orthogonality lattice `NS(u)`: all integral
vectors pairing to zero with the period line, constructed by native kernels.
No geometric divisor-class interpretation is asserted. -/
def latticePeriodNeronSeveriData (b : LinearMap.BilinForm ℤ L)
    (p : LatticePeriodPointData b) : Submodule ℤ L :=
  ⨅ v : p.val.submodule,
    ((((b.baseChange ℂ).flip v.val).restrictScalars ℤ).comp
      (latticeComplexificationMapData L)).ker

/-- The locus `D(S⊥)` cut out by orthogonality to an integral submodule.
It is defined for every submodule; primitive embeddings give the
source's lattice-marked specialization without a new construction. -/
def latticePeriodOrthogonalDomainData (b : LinearMap.BilinForm ℤ L)
    (S : Submodule ℤ L) : Set (LatticePeriodPointData b) :=
  {p | S ≤ latticePeriodNeronSeveriData b p}

end LeanCategories.Lattices.Valued
