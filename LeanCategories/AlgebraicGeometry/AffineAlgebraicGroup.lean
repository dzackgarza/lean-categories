/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Irreducible

/-!
# Affine algebraic groups

Definition-level realization of Humphreys FC16-C02-U001 and FC16-C02-U006.

Mathlib's `Grp (Over (Spec K))` is an internal group object in schemes over
`Spec K`: its multiplication, identity, and inversion are therefore
`K`-scheme morphisms and the group identities are intrinsic constructor
fields.  Humphreys' classical affine-variety hypotheses are the additional
affine, reduced, and finite-type conditions on the underlying scheme.

No structure theorem, Hopf-algebra comparison, component theorem, or
representation result is included here.
-/

@[expose] public section

namespace LeanCategories.AlgebraicGeometry

open CategoryTheory
open _root_.AlgebraicGeometry

universe u

/-- Humphreys' definition-level predicate for an affine algebraic group over
an algebraically closed field `K`.

Affineness already implies separatedness in Mathlib, so the source variety
separation axiom does not need a duplicate field here. -/
def IsAffineAlgebraicGroup
    (K : Type u) [Field K] [IsAlgClosed K]
    (G : Grp (Over (Spec (.of K)))) : Prop :=
  IsAffine G.X.left ∧
    IsReduced G.X.left ∧
    LocallyOfFiniteType G.X.hom

/-- The carrier of affine algebraic groups over `K`, represented exactly as
affine finite-type reduced group schemes over `Spec K`. -/
abbrev AffineAlgebraicGroup
    (K : Type u) [Field K] [IsAlgClosed K] :=
  {G : Grp (Over (Spec (.of K))) // IsAffineAlgebraicGroup K G}

namespace AffineAlgebraicGroup

variable {K : Type u} [Field K] [IsAlgClosed K]

open MonObj in
/-- The identity point of an affine algebraic group, obtained by evaluating the
unit section at the unique point of `Spec K`. -/
noncomputable def identityPoint (G : AffineAlgebraicGroup K) : G.1.X.left :=
  η[G.1.X].left (IsLocalRing.closedPoint K)

/-- Humphreys' identity component `G°`: the irreducible component of the
identity point.  Its subgroup and finite-index properties are result-layer
statements, not part of this definition. -/
noncomputable def identityComponent (G : AffineAlgebraicGroup K) : Set G.1.X.left :=
  irreducibleComponent G.identityPoint

end AffineAlgebraicGroup

end LeanCategories.AlgebraicGeometry
