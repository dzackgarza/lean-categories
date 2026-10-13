/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.AffineAlgebraicGroup

/-!
# Vector-group data

Definition-level realization of Humphreys FC16-C07-U033.

The source defines a vector group to be an algebraic group isomorphic to
some power `G_a^n`.  The additive-group powers are upstream data from
FC16-C02-U003; this file records only the defining isomorphism predicate
and does not reconstruct their group-scheme laws.
-/

@[expose] public section

namespace LeanCategories.AlgebraicGeometry

open CategoryTheory
open _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- An affine algebraic group is a vector group when it is isomorphic,
as a group scheme over `Spec K`, to one of the supplied additive-group
powers `G_a^n`.

For FC16-C07-U033, `additiveGroupPower n` is the `G_a^n` object owned
by FC16-C02-U003. -/
def IsVectorGroup
    (additiveGroupPower : ℕ → AffineAlgebraicGroup K)
    (G : AffineAlgebraicGroup K) : Prop :=
  ∃ n : ℕ, Nonempty (G.1 ≅ (additiveGroupPower n).1)

end LeanCategories.AlgebraicGeometry
