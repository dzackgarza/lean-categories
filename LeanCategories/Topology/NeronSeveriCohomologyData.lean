/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.Divisors
public import LeanCategories.Topology.SurfaceGysinData
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Divisor cohomology and Néron--Severi data

Definition-level support for Peters--Sterk FC11-B-U016.

The geometric input still missing from the checked stack is the codimension-one
cycle-class homomorphism from Div(X) to H²(X, ℤ).

Once that homomorphism is supplied, all remaining definitions in the source
row are ordinary algebra: homological equivalence is equality of cohomology
classes, algebraic classes are the image, the Néron--Severi group is identified
with that image, and the Picard number is its integral rank.

No existence, Lefschetz (1,1), finite-generation, or comparison theorem is
proved here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace LeanCategories.Topology

variable (X : Scheme.{0})

/-- Integral degree-two singular cohomology of the underlying topological
space of a scheme. -/
noncomputable abbrev SchemeIntegralH2Data : Type _ :=
  SingularIntegralCohomologyData (X : TopCat) 2

/-- Presentation input for the geometric divisor cycle-class map.

The map itself is the unresolved geometric construction in FC11-B-U016.
Downstream source definitions consume only this additive homomorphism. -/
structure DivisorCycleClassPresentationData where
  classMap :
    LeanCategories.Schemes.WeilDivisor X →ₗ[ℤ]
      SchemeIntegralH2Data X

/-- Geometric input reduced to prime divisors only.

Since the Weil-divisor group is free abelian on prime divisors, a class for
each prime divisor extends canonically to all divisors. -/
structure PrimeDivisorCycleClassPresentationData where
  primeClass :
    LeanCategories.Schemes.PrimeDivisor X →
      SchemeIntegralH2Data X

/-- Linear extension of prime-divisor cohomology classes to the full
Weil-divisor group. -/
noncomputable def divisorCycleClassMapData
    (D : PrimeDivisorCycleClassPresentationData X) :
    LeanCategories.Schemes.WeilDivisor X →ₗ[ℤ]
      SchemeIntegralH2Data X :=
  Finsupp.linearCombination ℤ D.primeClass

/-- Package a prime-divisor class assignment as divisor cycle-class
presentation data. -/
noncomputable def divisorCycleClassPresentationData
    (D : PrimeDivisorCycleClassPresentationData X) :
    DivisorCycleClassPresentationData X where
  classMap := divisorCycleClassMapData X D

/-- Homological equivalence of divisors: equality of integral cohomology
classes. -/
def DivisorHomologicallyEquivalentData
    (D : DivisorCycleClassPresentationData X)
    (A B : LeanCategories.Schemes.WeilDivisor X) : Prop :=
  D.classMap A = D.classMap B

/-- Algebraic degree-two cohomology classes: the image of the divisor
cycle-class map. -/
abbrev AlgebraicCohomologyClassData
    (D : DivisorCycleClassPresentationData X) :
    Submodule ℤ (SchemeIntegralH2Data X) :=
  D.classMap.range

/-- Peters--Sterk's convention identifying NS(X) with its image inside
H²(X,ℤ). -/
abbrev NeronSeveriCohomologyData
    (D : DivisorCycleClassPresentationData X) :
    Submodule ℤ (SchemeIntegralH2Data X) :=
  D.classMap.range

/-- Alias emphasizing the integral-module structure used by lattice/rank
constructions. -/
abbrev NeronSeveriModuleData
    (D : DivisorCycleClassPresentationData X) :=
  NeronSeveriCohomologyData X D

/-- Picard number of supplied divisor-cycle-class data.

Finite generation of NS(X) is theorem content; Module.finrank is defined for
the carrier independently of that theorem. -/
noncomputable def picardNumberData
    (D : DivisorCycleClassPresentationData X) : ℕ :=
  Module.finrank ℤ (NeronSeveriModuleData X D)

end LeanCategories.Topology
