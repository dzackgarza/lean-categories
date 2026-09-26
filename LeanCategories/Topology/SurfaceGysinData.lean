/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.FourManifoldIntersectionData
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Degree-two Gysin data for oriented compact surfaces

Definition-level realization of Peters--Sterk FC11-C20-U053.

For the resolved quotient map between the two smooth surfaces in the source,
the Gysin map on integral degree-two cohomology is defined to be Poincare dual
to the induced map on degree-two homology.

The current topology stack has native singular homology and singular
cohomology but no packaged Poincare-duality isomorphism.  Sweep III therefore
records the source definition by exact representative graphs and packages
valid candidates as subtypes:

* Kronecker pairing data satisfy evaluation of cocycle representatives on
  cycle representatives;
* degree-two Poincare-duality data satisfy the equation saying
  that Kronecker evaluation against its image equals the already-realized
  cup/fundamental-class intersection pairing;
* the map on degree-two homology is the native singular-homology map induced
  by the supplied continuous surface map;
* Gysin data satisfy the exact equation
  PD_Y(gysin(a)) = f_*(PD_X(a)).

No arbitrary wrong-way map is selected.  Existence and uniqueness of the
duality maps, invertibility of Poincare duality, functoriality of the
Gysin construction, and preservation of the Hodge decomposition are
result-layer statements and are not proved in Sweep III.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology

namespace LeanCategories.Topology

/-- The native integral singular chain complex of a space. -/
noncomputable abbrev SingularIntegralChainComplexData (X : TopCat) :=
  ((singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj X

/-- The native integral singular cochain complex of a space. -/
noncomputable abbrev SingularIntegralCochainComplexData (X : TopCat) :=
  singularCochainComplexData ℤ X (ModuleCat.of ℤ ℤ)

/-- Integral singular homology in degree n. -/
noncomputable abbrev SingularIntegralHomologyData (X : TopCat) (n : ℕ) :=
  ((SingularIntegralChainComplexData X).homology n : Type)

/-- Integral singular cohomology in degree n. -/
noncomputable abbrev SingularIntegralCohomologyData (X : TopCat) (n : ℕ) :=
  ((SingularIntegralCochainComplexData X).homology n : Type)

/-- Candidate Kronecker evaluation pairing in degree n. -/
abbrev SingularKroneckerPairingCandidateData (X : TopCat) (n : ℕ) :=
  SingularIntegralCohomologyData X n →
    SingularIntegralHomologyData X n → ℤ

/-- Exact representative graph for the Kronecker pairing: a cohomology class
represented by a cocycle evaluates on a homology class represented by a cycle
by literal cochain evaluation on that chain. -/
def IsSingularKroneckerPairingData
    (X : TopCat) (n : ℕ)
    (pairing : SingularKroneckerPairingCandidateData X n) : Prop :=
  let C := SingularIntegralCochainComplexData X
  let K := SingularIntegralChainComplexData X
  ∀ (phi : C.cycles n) (z : K.cycles n),
    pairing ((C.homologyπ n).hom phi) ((K.homologyπ n).hom z) =
      ((C.iCycles n).hom phi).hom ((K.iCycles n).hom z)

/-- Source-faithful integral Kronecker pairing data.  Representative
independence/existence is result content. -/
abbrev SingularKroneckerPairingData
    (X : TopCat) (n : ℕ) :
    Type _ :=
  {pairing : SingularKroneckerPairingCandidateData X n //
    IsSingularKroneckerPairingData X n pairing}

/-- Candidate degree-two Poincare-duality map from integral cohomology to
integral homology. -/
abbrev SurfacePoincareDualCandidateData (X : TopCat) :=
  SingularIntegralCohomologyData X 2 →ₗ[ℤ]
    SingularIntegralHomologyData X 2

/-- Exact graph characterizing degree-two Poincare duality through the
intersection form:

    <b, PD(a)> = <a cup b, [X]>.

The right-hand side uses the already-realized degree-four fundamental-class
evaluation. -/
def IsSurfacePoincareDualData
    (X : TopCat)
    (omega : FourManifoldFundamentalEvaluationData X)
    (ev : FourManifoldCohomologyEvaluationData X omega)
    (cup : SingularCohomologyCupData ℤ X)
    (pairing : SingularKroneckerPairingData X 2)
    (pd : SurfacePoincareDualCandidateData X) : Prop :=
  ∀ a b : SingularIntegralCohomologyData X 2,
    pairing.1 b (pd a) =
      ev.1 (singularCohomologyCupMulData ℤ X cup (p := 2) (q := 2) a b)

/-- Degree-two Poincare-duality data satisfying the exact cup/intersection
graph.  Existence, uniqueness and invertibility are result-layer obligations. -/
abbrev SurfacePoincareDualData
    (X : TopCat)
    (omega : FourManifoldFundamentalEvaluationData X)
    (ev : FourManifoldCohomologyEvaluationData X omega)
    (cup : SingularCohomologyCupData ℤ X)
    (pairing : SingularKroneckerPairingData X 2) :=
  {pd : SurfacePoincareDualCandidateData X //
    IsSurfacePoincareDualData X omega ev cup pairing pd}

/-- The native pushforward on degree-two integral singular homology induced by
a supplied continuous map of spaces. -/
noncomputable def surfaceSecondHomologyPushforwardData
    {X Y : TopCat} (f : C(X, Y)) :
    SingularIntegralHomologyData X 2 →ₗ[ℤ]
      SingularIntegralHomologyData Y 2 :=
  (((singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).hom

/-- Candidate Gysin map on degree-two integral cohomology. -/
abbrev SurfaceDegreeTwoGysinCandidateData (X Y : TopCat) :=
  SingularIntegralCohomologyData X 2 →ₗ[ℤ]
    SingularIntegralCohomologyData Y 2

/-- Exact Poincare-dual graph for the degree-two Gysin map:

    PD_Y(gysin(a)) = f_*(PD_X(a)).

This is the source definition stripped of the later Hodge-compatibility
assertion. -/
def IsSurfaceDegreeTwoGysinData
    {X Y : TopCat}
    {omegaX : FourManifoldFundamentalEvaluationData X}
    {omegaY : FourManifoldFundamentalEvaluationData Y}
    {evX : FourManifoldCohomologyEvaluationData X omegaX}
    {evY : FourManifoldCohomologyEvaluationData Y omegaY}
    {cupX : SingularCohomologyCupData ℤ X}
    {cupY : SingularCohomologyCupData ℤ Y}
    {pairingX : SingularKroneckerPairingData X 2}
    {pairingY : SingularKroneckerPairingData Y 2}
    (pdX : SurfacePoincareDualData X omegaX evX cupX pairingX)
    (pdY : SurfacePoincareDualData Y omegaY evY cupY pairingY)
    (f : C(X, Y))
    (gysin : SurfaceDegreeTwoGysinCandidateData X Y) : Prop :=
  ∀ a : SingularIntegralCohomologyData X 2,
    pdY.1 (gysin a) =
      surfaceSecondHomologyPushforwardData f
        (pdX.1 a)

/-- Degree-two Gysin data satisfying the exact Poincare-dual graph.

For FC11-C20-U053, specialize f to the resolved quotient map.  Preservation
of the Hodge decomposition is theorem content and is deliberately absent from
this construction. -/
abbrev SurfaceDegreeTwoGysinData
    {X Y : TopCat}
    {omegaX : FourManifoldFundamentalEvaluationData X}
    {omegaY : FourManifoldFundamentalEvaluationData Y}
    {evX : FourManifoldCohomologyEvaluationData X omegaX}
    {evY : FourManifoldCohomologyEvaluationData Y omegaY}
    {cupX : SingularCohomologyCupData ℤ X}
    {cupY : SingularCohomologyCupData ℤ Y}
    {pairingX : SingularKroneckerPairingData X 2}
    {pairingY : SingularKroneckerPairingData Y 2}
    (pdX : SurfacePoincareDualData X omegaX evX cupX pairingX)
    (pdY : SurfacePoincareDualData Y omegaY evY cupY pairingY)
    (f : C(X, Y)) :=
  {gysin : SurfaceDegreeTwoGysinCandidateData X Y //
    IsSurfaceDegreeTwoGysinData pdX pdY f gysin}

end LeanCategories.Topology
