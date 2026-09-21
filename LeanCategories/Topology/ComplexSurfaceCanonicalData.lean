/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Complex-surface canonical-bundle data

Definition-level realization of the construction part of Peters--Steenbrink
FC11-C02-U029.

The checked libraries do not provide a holomorphic tangent/cotangent bundle
for an arbitrary compact complex surface.  This file therefore starts from
the source-supplied family of complex tangent fibres.  It constructs the
cotangent fibres by linear duality and the canonical fibres as their second
exterior powers.  Sections, holomorphic-section predicates, and
nowhere-vanishing are then direct data-level notions.

The identities involving first Chern classes and the theorem that a
nowhere-vanishing holomorphic section trivializes the holomorphic line bundle
are result-layer statements and are not asserted here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u v

variable {X : Type u} (T : X → Type v)
variable [∀ x, AddCommGroup (T x)] [∀ x, Module ℂ (T x)]

/-- The cotangent fibre `T_x^*` of a source-supplied complex tangent fibre. -/
abbrev complexSurfaceCotangentFiberData (x : X) :=
  Module.Dual ℂ (T x)

/-- The canonical-line fibre `Λ² T_x^*`. -/
abbrev complexSurfaceCanonicalFiberData (x : X) :=
  ⋀[ℂ]^2 (complexSurfaceCotangentFiberData T x)

/-- Raw sections of the fibrewise canonical line. -/
abbrev ComplexSurfaceCanonicalSectionData :=
  ∀ x : X, complexSurfaceCanonicalFiberData T x

/-- A source-supplied holomorphicity predicate on canonical sections.

This separates the missing holomorphic-bundle analytic layer from the
algebraic construction of `Λ² T^*`. -/
def IsHolomorphicTwoFormData
    (isHolomorphicSection : ComplexSurfaceCanonicalSectionData T → Prop)
    (ω : ComplexSurfaceCanonicalSectionData T) : Prop :=
  isHolomorphicSection ω

/-- A canonical section is nowhere vanishing when it is nonzero in every
canonical fibre. -/
def IsNowhereVanishingCanonicalSectionData
    (ω : ComplexSurfaceCanonicalSectionData T) : Prop :=
  ∀ x, ω x ≠ 0

end LeanCategories.Topology
