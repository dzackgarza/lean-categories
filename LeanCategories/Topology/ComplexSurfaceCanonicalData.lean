/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Geometry.HolomorphicFormCoreData

/-!
# Complex-surface canonical-form data

Definition-level realization of Peters--Steenbrink FC11-C02-U029.

The canonical bundle of a complex surface is the bundle of holomorphic
two-covectors.  The project now has an intrinsic holomorphic-form sheaf on an
actual complex manifold, so this owner no longer accepts a tangent-fibre family
or a holomorphicity predicate from the caller.  Its fibres are the native
continuous alternating complex two-covectors on the tangent spaces, and its
global sections are literally the global sections of `Omega_X^2`.

The Chern-class identities and the theorem that a nowhere-vanishing global
section trivializes the canonical bundle remain statements about this
construction, not inputs to it.
-/

@[expose] public noncomputable section

open scoped ContDiff Manifold Topology

namespace LeanCategories.Topology

universe u

variable {E H X : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [TopologicalSpace H]
variable (I : ModelWithCorners ℂ E H) [I.Boundaryless]
variable [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ω X]

/-- The cotangent fibre at `x`, as continuous complex-linear functionals on
the actual complex-manifold tangent space. -/
abbrev complexSurfaceCotangentFiberData (x : X) :=
  TangentSpace I x →L[ℂ] ℂ

/-- The canonical fibre `Lambda^2 T_x^*`, represented by the native
continuous alternating complex two-covectors. -/
abbrev complexSurfaceCanonicalFiberData (x : X) :=
  LeanCategories.Geometry.CanonicalPFormFiberData (X := X) I 2 x

/-- The canonical sheaf `Omega_X^2` of holomorphic two-forms. -/
abbrev complexSurfaceCanonicalSheafData :=
  LeanCategories.Geometry.canonicalPFormSheafData (X := X) I 2

/-- Global holomorphic sections of the canonical bundle.  Holomorphicity is
part of the section type and is not supplied as a predicate. -/
abbrev ComplexSurfaceCanonicalSectionData :=
  (complexSurfaceCanonicalSheafData (X := X) I).presheaf.obj
    (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of X)))

/-- A canonical section is nowhere vanishing when its actual fibre value is
nonzero at every point. -/
def IsNowhereVanishingCanonicalSectionData
    (omega : ComplexSurfaceCanonicalSectionData (X := X) I) : Prop :=
  ∀ x : X,
    LeanCategories.Geometry.canonicalPFormSectionValueData
      (X := X) I 2 _ omega ⟨x, Set.mem_univ x⟩ ≠ 0

end LeanCategories.Topology
