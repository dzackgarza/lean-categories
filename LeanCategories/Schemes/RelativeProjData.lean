/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.RelativeProjHypothesis
public import LeanCategories.AlgebraicGeometry.AmpleSheaf
public import LeanCategories.Schemes.ProjGradedModuleData
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Relative Proj data

Definition-level realization of Hartshorne FC06-C02-U231.

For a graded algebra sheaf `S` satisfying condition (+), Hartshorne constructs
`Proj S` by gluing the ordinary affine-base schemes `Proj Γ(U,S)` over affine
opens `U ⊆ X`; the local twisting sheaves `O(1)` glue at the same time.

The existence of those gluings and all overlap compatibilities are theorem
content.  Sweep III therefore records the exact affine local presentation as a
predicate on a candidate scheme, projection, and module.  The selected datum is
named by that specification without constructing gluing proofs.

To keep the local statement source-faithful, an affine graded-ring presentation
records a genuine internally graded commutative ring whose degree-`d` piece is
additively equivalent to `S_d(U)`; compatibility with the degree-zero unit and
homogeneous multiplication is stated propositionally.  The local `O(1)` is
specified using the shifted graded-module section carrier already realized in
FC06-C02-U128.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open LeanCategories.AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

variable {X : Scheme.{u}}

/-- A concrete internally graded ring presenting the section algebra
`Γ(U,S)=⊕_d S_d(U)` on an affine open.  Compatibility with the source algebra is
kept in `IsRelativeProjAffineRingPresentationData` rather than proof fields. -/
structure RelativeProjAffineRingPresentationData
    (S : RelativeProjAlgebraData X) (U : X.Opens) where
  ring : CommRingCat.{u}
  grading : ℕ → Submodule ℤ ring
  gradedRing : GradedRing grading
  componentEquiv (d : ℕ) : (grading d : Type u) ≃+ S.algebra.Sections d U
  degreeZeroEquiv : (grading 0 : Type u) ≃+* Γ(X, U)

/-- Exact compatibility condition saying that an affine graded-ring
presentation is the graded section algebra of `S` on `U`. -/
def IsRelativeProjAffineRingPresentationData
    (S : RelativeProjAlgebraData X) (U : X.Opens)
    (A : RelativeProjAffineRingPresentationData S U) : Prop :=
  letI : GradedRing A.grading := A.gradedRing
  (∀ a : Γ(X, U),
      A.componentEquiv 0 (A.degreeZeroEquiv.symm a) =
        S.algebra.degreeZeroHom.val.app (op U) a) ∧
    ∀ (i j : ℕ) (x : A.grading i) (y : A.grading j),
      A.componentEquiv (i + j)
          ⟨(x : A.ring) * (y : A.ring),
            SetLike.GradedMonoid.toGradedMul.mul_mem x.2 y.2⟩ =
        S.algebra.mulSections U (A.componentEquiv i x) (A.componentEquiv j y)

/-- The canonical projection of an affine local `Proj Γ(U,S)` chart to its
affine base `U`, through the degree-zero identification. -/
def affineRelativeProjToBaseData
    (U : X.Opens) (hU : IsAffineOpen U)
    {S : RelativeProjAlgebraData X}
    (A : RelativeProjAffineRingPresentationData S U) :
    letI : GradedRing A.grading := A.gradedRing
    Proj A.grading ⟶ U.toScheme := by
  letI : GradedRing A.grading := A.gradedRing
  exact Proj.toSpecZero A.grading ≫
    Spec.map (CommRingCat.ofHom A.degreeZeroEquiv.symm.toRingHom) ≫
      hU.isoSpec.inv

/-- The `ℤ`-grading of the shifted module `A(1)`: degree `d` is `A_{d+1}`
when `d+1≥0`, and zero otherwise. -/
def relativeProjShiftOneGradingData
    {S : RelativeProjAlgebraData X} {U : X.Opens}
    (A : RelativeProjAffineRingPresentationData S U) :
    ℤ → AddSubgroup A.ring :=
  fun d =>
    if _h : 0 ≤ d + 1 then
      (A.grading (d + 1).toNat).toAddSubgroup
    else ⊥

/-- Raw section carrier of the local twisting module `A(1)~` on an affine
`Proj` chart, using the FC06-C02-U128 graded-module construction. -/
def relativeProjTwistOneSectionData
    {S : RelativeProjAlgebraData X} {U : X.Opens}
    (A : RelativeProjAffineRingPresentationData S U) :
    letI : GradedRing A.grading := A.gradedRing
    (V : (Proj A.grading).Opens) →
      Set (projGradedModuleSectionFamilyData
        (M := A.ring) A.grading V) := by
  letI : GradedRing A.grading := A.gradedRing
  intro V
  exact projGradedModuleSectionData A.grading
    (relativeProjShiftOneGradingData A) V

/-- Specification for a bundled local `O(1)` module: its sections are exactly
the shifted-module section carriers and its restriction maps agree with raw
family restriction.

This predicate does not prove that the raw carriers form a sheaf; it only
states what a candidate bundled module must realize. -/
def IsRelativeProjTwistOneData
    {S : RelativeProjAlgebraData X} {U : X.Opens}
    (A : RelativeProjAffineRingPresentationData S U) :
    letI : GradedRing A.grading := A.gradedRing
    (L : (Proj A.grading).Modules) → Prop := by
  letI : GradedRing A.grading := A.gradedRing
  exact fun L =>
    ∃ e : ∀ V : (Proj A.grading).Opens,
        (L.val.obj (op V) : Type u) ≃
          {s // s ∈ relativeProjTwistOneSectionData A V},
      ∀ (V W : (Proj A.grading).Opens) (hWV : W ≤ V)
        (s : L.val.obj (op V)),
        (e W (L.val.map (homOfLE hWV).op s)).1 =
          projGradedModuleSectionFamilyRestrictData
            A.grading hWV (e V s).1

/-- Candidate data for relative `Proj`: the glued scheme, its structural
projection, and the prospective twisting sheaf `O(1)`. -/
structure RelativeProjCandidateData (X : Scheme.{u}) where
  scheme : Scheme.{u}
  projection : scheme ⟶ X
  twistOne : scheme.Modules

/-- Ambient candidate data is nonempty independently of the relative-Proj
existence theorem. -/
instance (X : Scheme.{u}) : Nonempty (RelativeProjCandidateData X) :=
  ⟨⟨X, 𝟙 X, schemeModuleUnit X⟩⟩

/-- Hartshorne's relative-Proj specification.

Over every affine base open, the candidate is identified with ordinary `Proj`
of the graded section algebra; the projection agrees with the degree-zero
structural map, and the candidate `O(1)` pulls back to the shifted local
twisting module.  Invertibility is recorded propositionally rather than proved
as part of construction. -/
def IsRelativeProjData (S : RelativeProjHypothesis X)
    (P : RelativeProjCandidateData X) : Prop :=
  IsTensorInvertible P.twistOne ∧
    ∀ (U : X.Opens) (hU : IsAffineOpen U),
      ∃ A : RelativeProjAffineRingPresentationData
          S.toRelativeProjAlgebraData U,
        IsRelativeProjAffineRingPresentationData
            S.toRelativeProjAlgebraData U A ∧
          letI : GradedRing A.grading := A.gradedRing
          ∃ e : (P.projection ⁻¹ᵁ U).toScheme ≅ Proj A.grading,
            e.hom ≫ affineRelativeProjToBaseData U hU A =
                P.projection ∣_ U ∧
              IsRelativeProjTwistOneData A
                ((Scheme.Modules.pullback e.inv).obj
                  (P.twistOne.restrict (P.projection ⁻¹ᵁ U).ι))

/-- The relative-Proj datum selected by its affine local specification.  The
later gluing theorem establishes that this selection satisfies
`IsRelativeProjData`. -/
def relativeProjData (S : RelativeProjHypothesis X) :
    RelativeProjCandidateData X :=
  Classical.epsilon (IsRelativeProjData S)

/-- The selected relative `Proj S` scheme. -/
abbrev relativeProjSchemeData (S : RelativeProjHypothesis X) : Scheme.{u} :=
  (relativeProjData S).scheme

/-- The selected structural projection `Proj S → X`. -/
def relativeProjProjectionData (S : RelativeProjHypothesis X) :
    relativeProjSchemeData S ⟶ X :=
  (relativeProjData S).projection

/-- The selected relative twisting sheaf `O_{Proj S}(1)`. -/
def relativeProjTwistingSheafOneData (S : RelativeProjHypothesis X) :
    (relativeProjSchemeData S).Modules :=
  (relativeProjData S).twistOne

end LeanCategories.Schemes
