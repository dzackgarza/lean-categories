/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Absolute Frobenius formula data

Definition-level transcription of Hartshorne FC06-C04-U028, following the
`absoluteFrobenius` construction in the Dieudonne reference.

Sweep III records only the source formulas: the identity map on points and the
`p`th-power operation on sections of the structure sheaf.  The assertions that
these maps are compatible with restrictions, define local ring maps, and
assemble to a scheme morphism are result/law content and are deliberately left
for Sweep IV.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace LeanCategories.AlgebraicGeometry

universe u

/-- Raw data underlying the absolute Frobenius formula on a scheme.

For a characteristic-`p` scheme the intended realization has the identity map
on points and raises every local section to its `p`th power.  No morphism laws
are included in this Sweep-III carrier. -/
structure AbsoluteFrobeniusData (X : Scheme.{u}) (p : ℕ) where
  pointMap : X → X
  sectionMap (U : X.Opens) :
    X.presheaf.obj (.op U) → X.presheaf.obj (.op U)

/-- Hartshorne's defining formulas for absolute Frobenius, before the sheaf and
local-ring compatibility laws needed to package them as a scheme morphism. -/
def absoluteFrobeniusData (X : Scheme.{u}) (p : ℕ) : AbsoluteFrobeniusData X p where
  pointMap := id
  sectionMap := fun _ f => f ^ p

end LeanCategories.AlgebraicGeometry
