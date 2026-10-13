/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Constructions

/-!
# Data for Hartshorne's valuation curve

Hartshorne, *Algebraic Geometry*, Chapter I, §6 (FC06-C01-U122).

Sweep III records the source-defined point carrier, cofinite topology, regularity
predicate for rational functions on an open set, and residue evaluation formula.
It does not prove restriction or sheaf laws, assemble a locally ringed space, or
identify the resulting function field with the ambient field.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u v

variable (k : Type u) (K : Type v)
variable [Field k] [Field K] [Algebra k K]

/-- A point of Hartshorne's valuation curve: a discrete valuation subring of
`K` containing the image of the ground field `k`. -/
def ValuationCurvePoint :=
  { R : ValuationSubring K //
      IsDiscreteValuationRing R ∧
        ∀ x : k, algebraMap k K x ∈ R }

namespace ValuationCurvePoint

/-- The discrete valuation subring represented by a valuation-curve point. -/
def ring (P : ValuationCurvePoint k K) : ValuationSubring K :=
  P.1

/-- The residue field at a valuation-curve point. -/
abbrev residueField (P : ValuationCurvePoint k K) :=
  IsLocalRing.ResidueField (ring k K P)

/-- Residue evaluation for an element together with its membership in the
valuation ring at `P`. -/
def residueValue (P : ValuationCurvePoint k K) (f : K)
    (hf : f ∈ ring k K P) : residueField k K P :=
  IsLocalRing.residue (ring k K P) ⟨f, hf⟩

end ValuationCurvePoint

/-- Hartshorne's valuation curve carrier equipped with the cofinite topology. -/
abbrev ValuationCurve :=
  CofiniteTopology (ValuationCurvePoint k K)

namespace ValuationCurve

/-- The valuation-ring point underlying a point of the cofinite valuation curve. -/
def underlyingPoint (P : ValuationCurve k K) : ValuationCurvePoint k K :=
  (CofiniteTopology.of).symm P

/-- A rational function is regular on `U` when it belongs to every valuation
ring represented by a point of `U`. This is the membership predicate for
Hartshorne's source formula `O(U) = ⋂_{P∈U} R_P`. -/
def IsRegularOn (U : Set (ValuationCurve k K)) (f : K) : Prop :=
  ∀ P : ValuationCurve k K, P ∈ U →
    f ∈ (underlyingPoint k K P).1

/-- Hartshorne's ring of functions regular on `U`, expressed literally as
the intersection of the valuation subrings at the points of `U`. -/
def regularRing (U : Set (ValuationCurve k K)) : Subring K :=
  ⨅ P : { P : ValuationCurve k K // P ∈ U },
    (underlyingPoint k K P.1).1.toSubring

/-- The source-defined regular sections on `U`. -/
abbrev RegularSection (U : Set (ValuationCurve k K)) : Type v :=
  regularRing k K U

namespace RegularSection

/-- Evaluate a regular section at a point by passing to the residue field of
the corresponding valuation ring. -/
def valueAt {U : Set (ValuationCurve k K)}
    (f : RegularSection k K U) (P : ValuationCurve k K) (hP : P ∈ U) :
    ValuationCurvePoint.residueField k K (underlyingPoint k K P) :=
  ValuationCurvePoint.residueValue k K (underlyingPoint k K P) f.1
    ((Subring.mem_iInf.mp f.2) ⟨P, hP⟩)

end RegularSection

end ValuationCurve

end LeanCategories.AlgebraicGeometry
