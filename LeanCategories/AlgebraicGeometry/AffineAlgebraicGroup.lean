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

Definition-level realization of Humphreys FC16-C02-U001, FC16-C02-U006,
and FC16-C02-U017.

Mathlib's `Grp (Over (Spec K))` is an internal group object in schemes over
`Spec K`: its multiplication, identity, and inversion are therefore
`K`-scheme morphisms and the group identities are intrinsic constructor
fields.  Humphreys' classical affine-variety hypotheses are the additional
affine, reduced, and finite-type conditions on the underlying scheme.

No structure theorem, component theorem beyond its defining carrier, or
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

/-- The coordinate Hopf algebra of an affine group scheme over a commutative base. -/
noncomputable def coordinateHopfAlgebraOf
    (R : CommRingCat) (G : Grp (Over (Spec R))) [IsAffine G.X.left] :
    CommHopfAlgCat R :=
  letI : G.X.left.Over (Spec R) := OverClass.fromOver G.X
  letI : GrpObj (G.X.left.asOver (Spec R)) := G.grp
  CommHopfAlgCat.of R Γ(G.X.left, ⊤)

/-- The coordinate Hopf algebra `K[G]` of an affine algebraic group.

This is the global-sections algebra of the underlying affine group scheme,
bundled with Mathlib's native Hopf structure induced by the group-object
multiplication, unit, and inverse. -/
noncomputable def coordinateHopfAlgebra (G : AffineAlgebraicGroup K) :
    CommHopfAlgCat K :=
  letI : IsAffine G.1.X.left := G.2.1
  coordinateHopfAlgebraOf (.of K) G.1

/-- The comultiplication on `K[G]` induced by multiplication on `G`. -/
noncomputable def coordinateComultiplication (G : AffineAlgebraicGroup K) :
    coordinateHopfAlgebra G →ₐ[K]
      TensorProduct K (coordinateHopfAlgebra G) (coordinateHopfAlgebra G) :=
  Bialgebra.comulAlgHom K (coordinateHopfAlgebra G)

/-- The counit on `K[G]` induced by the identity section of `G`. -/
noncomputable def coordinateCounit (G : AffineAlgebraicGroup K) :
    coordinateHopfAlgebra G →ₐ[K] K :=
  Bialgebra.counitAlgHom K (coordinateHopfAlgebra G)

/-- The antipode on `K[G]` induced by inversion on `G`. -/
noncomputable def coordinateAntipode (G : AffineAlgebraicGroup K) :
    coordinateHopfAlgebra G →ₐ[K] coordinateHopfAlgebra G :=
  HopfAlgebra.antipodeAlgHom K (coordinateHopfAlgebra G)

end AffineAlgebraicGroup

end LeanCategories.AlgebraicGeometry
