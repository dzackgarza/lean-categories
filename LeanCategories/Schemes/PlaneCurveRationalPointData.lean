/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Rational-point data for pointed plane curves

Definition-level realization of the construction clause of Hartshorne
FC06-C04-U123.

Let k0 be a subfield of k. For a plane curve X over k whose equation and
distinguished point are defined over k0, Hartshorne writes X(k0) for the
points having homogeneous coordinates over k0.

This file records that predicate directly on projective points. A projective
point is defined over k0 when it has a nonzero homogeneous representative
whose coordinates are images of elements of k0. Rational points of a supplied
plane curve are the corresponding subtype.

The statement that these points are closed under the elliptic group law and
hence form a subgroup of X(k) is result content. No group-closure proof,
Weierstrass normal-form choice, or descent comparison is performed in
Sweep III.
-/

@[expose] public noncomputable section

open scoped LinearAlgebra.Projectivization

namespace LeanCategories.Schemes

universe u v

variable (k₀ : Type u) (k : Type v)
variable [Field k₀] [Field k] [Algebra k₀ k]

/-- Homogeneous coordinate vectors in the projective plane over a field. -/
abbrev PlaneHomogeneousCoordinatesData (K : Type*) [Field K] :=
  Fin 3 → K

/-- Extend homogeneous coordinates from k0 to k coefficientwise. -/
def planeCoordinatesBaseChangeData
    (v : PlaneHomogeneousCoordinatesData k₀) :
    PlaneHomogeneousCoordinatesData k :=
  fun i => algebraMap k₀ k (v i)

/-- A projective-plane point over k is defined over k0 when it admits a
nonzero homogeneous representative obtained by coefficientwise base change
from k0. -/
def IsProjectivePlanePointDefinedOverData
    (P : ℙ k (PlaneHomogeneousCoordinatesData k)) : Prop :=
  ∃ v : PlaneHomogeneousCoordinatesData k₀,
    ∃ hv : planeCoordinatesBaseChangeData k₀ k v ≠ 0,
      P = Projectivization.mk k
        (planeCoordinatesBaseChangeData k₀ k v) hv

/-- Points of a supplied plane curve. -/
abbrev PlaneCurvePointData
    (curve : Set (ℙ k (PlaneHomogeneousCoordinatesData k))) :=
  {P : ℙ k (PlaneHomogeneousCoordinatesData k) // P ∈ curve}

/-- Hartshorne's rational-point carrier X(k0): curve points whose projective
coordinates are defined over k0. -/
abbrev PlaneCurveRationalPointData
    (curve : Set (ℙ k (PlaneHomogeneousCoordinatesData k))) :=
  {P : PlaneCurvePointData k curve //
    IsProjectivePlanePointDefinedOverData k₀ k P.1}

/-- Source hypothesis that the distinguished point of a pointed plane curve is
defined over k0. The condition that the defining cubic equation itself has
coefficients in k0 is separate equation data and is not reconstructed here. -/
def IsPointedPlaneCurveOriginDefinedOverData
    (curve : Set (ℙ k (PlaneHomogeneousCoordinatesData k)))
    (P₀ : ℙ k (PlaneHomogeneousCoordinatesData k)) : Prop :=
  P₀ ∈ curve ∧ IsProjectivePlanePointDefinedOverData k₀ k P₀

end LeanCategories.Schemes
