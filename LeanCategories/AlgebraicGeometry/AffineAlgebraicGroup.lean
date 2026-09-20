/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Affine algebraic groups

Definition-level realization of Humphreys FC16-C02-U001.

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

end LeanCategories.AlgebraicGeometry
