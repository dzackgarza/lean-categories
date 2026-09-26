/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.BiellipticSurfaceData
public import LeanCategories.Schemes.CompleteLinearSystemData
public import LeanCategories.Schemes.CurveMorphismDegreeData
public import LeanCategories.Schemes.LocalIntersectionMultiplicityData
public import LeanCategories.Schemes.PointBlowupData
public import Mathlib.AlgebraicGeometry.Limits

/-!
# A (2,2)-pencil on P¹ × P¹ and its eight-point blow-up

Definition-level realization of Peters--Sterk FC11-C20-U051.

The source starts with two smooth elliptic curves of bidegree `(2,2)` on
`P¹ × P¹`, takes their pencil, and blows up their eight transverse common
points.  Smoothness/rationality and the Euler-characteristic computation for
the resulting surface are result clauses and are not asserted here.

The bidegree condition is intrinsic: each embedded elliptic curve has degree
two under each projection to `P¹`.  The pencil reuses the projective-linear
system presentation from FC12-C02-U005.  The eight-point blow-up is kept as
candidate data with its exact source graph; existence of that blow-up remains
separate theorem content.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open LeanCategories.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace LeanCategories.Schemes

universe u

/-- The scheme `P¹_ℂ × P¹_ℂ`, formed as the fibre product over `Spec ℂ`. -/
abbrev complexProjectiveLineProductData : Scheme :=
  pullback (complexProjectiveSpaceToSpec 1) (complexProjectiveSpaceToSpec 1)

/-- An elliptic curve together with a specified map to `P¹ × P¹`. -/
structure P1ProductEllipticCurveData where
  curve : AbelianVariety ℂ
  embedding : curve.toOver.left ⟶ complexProjectiveLineProductData

/-- Source predicate that an embedded elliptic curve has bidegree `(2,2)`.

For a curve in `P¹ × P¹`, the two bidegrees are the degrees of the composites
with the two projections. -/
def IsP1ProductBidegreeTwentyTwoCurveData
    (C : P1ProductEllipticCurveData) : Prop :=
  IsClosedImmersion C.embedding ∧
    IsEllipticCurveData C.curve ∧
    ∃ hP1 : IsIntegral (ProjectiveSpace ℂ 1),
      letI : IsIntegral (ProjectiveSpace ℂ 1) := hP1
      letI : GeometricallyIntegral C.curve.toOver.hom := C.curve.geometricallyIntegral
      letI : IsIntegral C.curve.toOver.left :=
        GeometricallyIntegral.isIntegral_of_subsingleton C.curve.toOver.hom
      IsCurveMorphismDegreeData
          (C.embedding ≫ pullback.fst
            (complexProjectiveSpaceToSpec 1) (complexProjectiveSpaceToSpec 1)) 2 ∧
        IsCurveMorphismDegreeData
          (C.embedding ≫ pullback.snd
            (complexProjectiveSpaceToSpec 1) (complexProjectiveSpaceToSpec 1)) 2

/-- Set-theoretic support of a Weil divisor, expressed through its prime
components with nonzero coefficient. -/
def WeilDivisor.supportData {X : Scheme.{u}} [DivisorStandingHypothesis X]
    (D : WeilDivisor X) : Set X :=
  {x | ∃ Y : PrimeDivisor X, D Y ≠ 0 ∧ x ∈ Set.range Y.ideal.subschemeι}

/-- Candidate data for blowing up eight specified points simultaneously.

The source uses the blow-up only as a geometric construction.  All geometric
properties are therefore kept in `IsEightPointBlowupData`. -/
structure EightPointBlowupCandidateData
    (S : SmoothProjectiveComplexSurface) (p : Fin 8 → S.scheme) where
  surface : SmoothProjectiveComplexSurface
  projection : surface.scheme ⟶ S.scheme
  exceptionalScheme : Fin 8 → Scheme
  exceptionalι (i : Fin 8) : exceptionalScheme i ⟶ surface.scheme

/-- Exact source graph for the simultaneous blow-up of eight distinct points.
It records the isomorphism away from the centers and the eight exceptional
projective lines as the corresponding fibres. -/
def IsEightPointBlowupData
    (S : SmoothProjectiveComplexSurface) (p : Fin 8 → S.scheme)
    (B : EightPointBlowupCandidateData S p) : Prop :=
  Function.Injective p ∧
    B.projection ≫ S.structureMap = B.surface.structureMap ∧
    (∃ U : S.scheme.Opens,
      (U : Set S.scheme) = (Set.range p)ᶜ ∧ IsIso (B.projection ∣_ U)) ∧
    ∀ i : Fin 8,
      IsClosedImmersion (B.exceptionalι i) ∧
        Set.range (B.exceptionalι i).base = B.projection.base ⁻¹' {p i} ∧
        Nonempty (B.exceptionalScheme i ≅ ProjectiveSpace ℂ 1)

/-- Candidate data for the Peters--Sterk `(2,2)` elliptic-pencil example. -/
structure P1ProductPencilBlowupCandidateData where
  base : SmoothProjectiveComplexSurface
  baseIso : base.scheme ≅ complexProjectiveLineProductData
  curves : Fin 2 → P1ProductEllipticCurveData
  divisorClass : WeilDivisor base.scheme
  pencil : DivisorLinearSystemPresentationData ℂ divisorClass
  generators : Fin 2 → ℙ ℂ pencil.parameterSpace
  points : Fin 8 → base.scheme
  blowup : EightPointBlowupCandidateData base points

/-- The two embedded elliptic curves, transported from `P¹ × P¹` to the
chosen base-surface presentation. -/
def P1ProductPencilBlowupCandidateData.curveEmbedding
    (D : P1ProductPencilBlowupCandidateData) (i : Fin 2) :
    (D.curves i).curve.toOver.left ⟶ D.base.scheme :=
  (D.curves i).embedding ≫ D.baseIso.inv

/-- Exact definition-level graph of the `(2,2)` pencil and eight-point blow-up.

The two chosen projective points generate the pencil.  Their associated Weil
divisors have supports equal to the two embedded elliptic curves.  The eight
listed points are exactly the common support, and the curve germs are
transverse there. -/
def IsP1ProductPencilBlowupData
    (D : P1ProductPencilBlowupCandidateData) : Prop :=
  ∃ hDiv : DivisorStandingHypothesis D.base.scheme,
    letI : DivisorStandingHypothesis D.base.scheme := hDiv
    (∀ i : Fin 2, IsP1ProductBidegreeTwentyTwoCurveData (D.curves i)) ∧
      IsDivisorLinearSystemPresentationData D.pencil ∧
      IsDivisorPencilData D.pencil ∧
      D.generators 0 ≠ D.generators 1 ∧
      D.pencil.subspace =
        Projectivization.Subspace.span {D.generators 0, D.generators 1} ∧
      (∀ i : Fin 2,
        (D.pencil.pointToDivisor (D.generators i)).supportData =
          Set.range (D.curveEmbedding i).base) ∧
      Set.range D.points =
        (D.pencil.pointToDivisor (D.generators 0)).supportData ∩
          (D.pencil.pointToDivisor (D.generators 1)).supportData ∧
      Function.Injective D.points ∧
      (∃ h0 : IsClosedImmersion (D.curveEmbedding 0),
        ∃ h1 : IsClosedImmersion (D.curveEmbedding 1),
          letI : IsClosedImmersion (D.curveEmbedding 0) := h0
          letI : IsClosedImmersion (D.curveEmbedding 1) := h1
          ∀ i : Fin 8,
            ∃ hAlg : Algebra ℂ (D.base.scheme.presheaf.stalk (D.points i)),
              letI : Algebra ℂ (D.base.scheme.presheaf.stalk (D.points i)) := hAlg
              AreLocallyTransverseData
                (D.curveEmbedding 0) (D.curveEmbedding 1) (D.points i)) ∧
      IsEightPointBlowupData D.base D.points D.blowup

end LeanCategories.Schemes
