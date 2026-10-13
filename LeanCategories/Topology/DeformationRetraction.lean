/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Deformation-retraction data

Definition-level transcription of Hatcher FC07-C00-U001, following the
strong-deformation-retraction interface in the sphere-six-complex reference.

Sweep III keeps the continuous maps as data and states the endpoint, image, and
fixed-subspace conditions as a predicate.  It does not ask a constructor to
carry proofs of those conditions.
-/

@[expose] public section

namespace LeanCategories.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The continuous-map data in a deformation retraction of `X`.

The homotopy uses Mathlib's interval-first convention `I × X`. -/
structure DeformationRetractionData (X : Type u) [TopologicalSpace X] where
  retract : C(X, X)
  homotopy : C(unitInterval × X, X)

/-- Hatcher's deformation-retraction conditions on raw continuous-map data.

At time zero the family is the identity, at time one it is the supplied
retraction, the image of the retraction is exactly `A`, and every point of `A`
is fixed throughout the family. -/
def IsDeformationRetraction (A : Set X) (D : DeformationRetractionData X) : Prop :=
  (∀ x, D.homotopy (0, x) = x) ∧
    (∀ x, D.homotopy (1, x) = D.retract x) ∧
      Set.range D.retract = A ∧
        ∀ t x, x ∈ A → D.homotopy (t, x) = x

end LeanCategories.Topology
