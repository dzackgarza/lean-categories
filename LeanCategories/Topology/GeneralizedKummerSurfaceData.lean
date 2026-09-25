/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.KummerSurfaceData
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Topology.Constructions

/-!
# Generalized Kummer-surface data

Definition-level realization of Peters--Sterk FC11-C20-U081.

The source defines a generalized Kummer surface to be the minimal resolution
of a quotient of a two-dimensional complex torus by a finite group.

The ordinary inversion quotient already realized for Kummer surfaces is a
special case.  Here the quotient is Mathlib's native orbit quotient for the
supplied finite group action.  The target locus that must be resolved is the
image of points with nontrivial stabilizer.  Raw resolution data and the
minimal-resolution predicate reuse the existing complex-surface resolution
owner.

No theorem that the quotient has only the expected surface singularities, that
the selected raw resolution satisfies the predicate, that the resolution is a
K3 surface, or that the finite groups are restricted to the classification
listed later in the source is asserted in Sweep III.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open LeanCategories.Lattices.Valued

universe u v

section

variable (G : Type v) [Group G] [Finite G]
variable (A : ComplexTorus.{u}) [MulAction G A.carrier]

/-- The source condition that the complex torus has complex dimension two. -/
def IsComplexTwoTorusData : Prop :=
  Module.finrank ℂ A.V = 2

/-- The finite action is holomorphic in the analytic interface used by the
surface-resolution layer. -/
def IsHolomorphicFiniteTorusActionData
    (I : ComplexSurfaceResolutionInterface.{u}) : Prop :=
  ∀ g : G,
    I.IsHolomorphicMap
      (X := TopCat.of A.carrier) (Y := TopCat.of A.carrier)
      (fun x : A.carrier => g • x)

/-- The orbit relation of the supplied finite group action. -/
abbrev generalizedKummerOrbitSetoid : Setoid A.carrier :=
  MulAction.orbitRel G A.carrier

/-- The finite quotient carrier A/G. -/
abbrev GeneralizedKummerQuotient : Type u :=
  Quotient (generalizedKummerOrbitSetoid G A)

/-- The quotient A/G with its ordinary quotient topology. -/
def generalizedKummerQuotientTopCat : TopCat.{u} :=
  TopCat.of (GeneralizedKummerQuotient G A)

/-- Canonical quotient map A -> A/G. -/
def generalizedKummerQuotientMk :
    A.carrier → GeneralizedKummerQuotient G A :=
  Quotient.mk (generalizedKummerOrbitSetoid G A)

/-- Points whose stabilizer for the finite action is nontrivial. -/
def generalizedKummerNonfreeLocus : Set A.carrier :=
  {x | ∃ g : G, g ≠ 1 ∧ g • x = x}

/-- Image in A/G of the nonfree locus.  These are the quotient points that
form the exceptional target locus for the generalized Kummer resolution. -/
def generalizedKummerExceptionalTargetData :
    Set (generalizedKummerQuotientTopCat G A) :=
  generalizedKummerQuotientMk G A '' generalizedKummerNonfreeLocus G A

/-- Raw resolution data for the finite complex-torus quotient. -/
abbrev GeneralizedKummerSurfaceResolutionData :=
  ComplexSurfaceResolutionData (generalizedKummerQuotientTopCat G A)

/-- Defining conditions for generalized Kummer resolution data.

The torus is two-dimensional, the finite action is holomorphic, and the raw
data are a minimal complex-surface resolution of the quotient away from the
image of the nonfree locus. -/
def IsGeneralizedKummerSurfaceResolutionData
    (I : ComplexSurfaceResolutionInterface.{u})
    (R : GeneralizedKummerSurfaceResolutionData G A) : Prop :=
  IsComplexTwoTorusData A ∧
    IsHolomorphicFiniteTorusActionData (G := G) (A := A) I ∧
      IsMinimalComplexSurfaceResolutionData I
        (generalizedKummerExceptionalTargetData G A) R

/-- Raw generalized Kummer resolution selected from the exact source
predicate.  Existence of a datum satisfying that predicate is result content. -/
noncomputable def generalizedKummerSurfaceResolutionData
    (I : ComplexSurfaceResolutionInterface.{u}) :
    GeneralizedKummerSurfaceResolutionData G A :=
  Classical.epsilon (IsGeneralizedKummerSurfaceResolutionData G A I)

/-- Peters--Sterk's generalized Kummer-surface carrier at the definition-data
level: the source of the selected minimal-resolution candidate. -/
noncomputable abbrev GeneralizedKummerSurface
    (I : ComplexSurfaceResolutionInterface.{u}) : TopCat.{u} :=
  (generalizedKummerSurfaceResolutionData G A I).source

/-- Resolution map from the selected generalized Kummer surface to A/G. -/
noncomputable def generalizedKummerSurfaceResolutionMap
    (I : ComplexSurfaceResolutionInterface.{u}) :
    GeneralizedKummerSurface G A I → generalizedKummerQuotientTopCat G A :=
  (generalizedKummerSurfaceResolutionData G A I).map

end

end LeanCategories.Topology
