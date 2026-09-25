/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.RelativeProjData
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Projective-space bundle data

Definition-level realization of Hartshorne FC06-C02-U236.

For a noetherian scheme `X` and a locally free coherent module `E`,
Hartshorne defines

`P(E) = Proj Sym(E)`.

The sheaf-level symmetric algebra is not packaged in the current Mathlib pin.
At Sweep-III level it is therefore specified on affine opens by the concrete
ring-level `SymmetricAlgebra`: the degree-`d` part is the span of products of
exactly `d` degree-one generators.  The resulting graded algebra is then fed
to the existing relative-Proj data owner.

Existence and compatibility of these affine presentations, and the statement
that a rank-`n+1` trivialization identifies the bundle locally with relative
`P^n`, are result content and are deliberately not proved here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open LeanCategories.AlgebraicGeometry
open scoped BigOperators

namespace LeanCategories.Schemes

universe u

variable {X : Scheme.{u}}

/-- The homogeneous degree-`d` part of the concrete symmetric algebra,
presented without any grading theorem: it is the submodule spanned by products
of exactly `d` degree-one generators. -/
def symmetricAlgebraDegreeData
    (R : Type u) [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] (d : ℕ) :
    Submodule R (SymmetricAlgebra R M) :=
  Submodule.span R <| Set.range fun x : Fin d → M =>
    ∏ i, SymmetricAlgebra.ι R M (x i)

/-- An affine graded-section presentation of `S` is the symmetric algebra of
`E` when its underlying ring is identified with the native symmetric algebra,
the degree-zero identification is the algebra map, and every homogeneous piece
is exactly the corresponding degree span.

This is a proposition about candidate data; no sheaf gluing or grading
existence proof is part of the construction. -/
def IsSymmetricAlgebraAffinePresentationData
    (E : X.Modules) {S : RelativeProjHypothesis X} (U : X.Opens)
    (A : RelativeProjAffineRingPresentationData
      S.toRelativeProjAlgebraData U) : Prop :=
  letI : GradedRing A.grading := A.gradedRing
  ∃ e : A.ring ≃+*
      SymmetricAlgebra Γ(X, U) Γ(E, U),
    (∀ r : Γ(X, U),
      e (A.degreeZeroEquiv.symm r : A.ring) =
        algebraMap Γ(X, U)
          (SymmetricAlgebra Γ(X, U) Γ(E, U)) r) ∧
    ∀ d : ℕ,
      e '' (A.grading d : Set A.ring) =
        (symmetricAlgebraDegreeData
          Γ(X, U) Γ(E, U) d :
            Set (SymmetricAlgebra Γ(X, U) Γ(E, U)))

/-- The relative-Proj algebra `S` is the sheaf-level symmetric algebra of
`E` when every affine section algebra has a presentation by the concrete
symmetric algebra of the corresponding sections of `E`. -/
def IsSymmetricAlgebraRelativeProjData
    (E : X.Modules) (S : RelativeProjHypothesis X) : Prop :=
  ∀ (U : X.Opens) (_hU : IsAffineOpen U),
    ∃ A : RelativeProjAffineRingPresentationData
        S.toRelativeProjAlgebraData U,
      IsRelativeProjAffineRingPresentationData
          S.toRelativeProjAlgebraData U A ∧
        IsSymmetricAlgebraAffinePresentationData E U A

/-- Hartshorne's projective-space-bundle specification:
`P(E)` is relative `Proj` of the symmetric algebra sheaf of `E`.

Local identification with ordinary projective space for a free trivialization
is a comparison theorem, not a constructor field. -/
def IsProjectiveBundleData
    [IsNoetherian X] (E : X.Modules)
    [E.IsLocallyFree] [E.IsFinitePresentation]
    (P : RelativeProjCandidateData X) : Prop :=
  ∃ S : RelativeProjHypothesis X,
    IsSymmetricAlgebraRelativeProjData E S ∧
      P = relativeProjData S

/-- The projective-space-bundle datum `P(E)=Proj Sym(E)`, selected by the exact
definition-level specification above. -/
def projectiveBundleData
    [IsNoetherian X] (E : X.Modules)
    [E.IsLocallyFree] [E.IsFinitePresentation] :
    RelativeProjCandidateData X :=
  Classical.epsilon (IsProjectiveBundleData E)

/-- The scheme underlying `P(E)`. -/
abbrev projectiveBundleSchemeData
    [IsNoetherian X] (E : X.Modules)
    [E.IsLocallyFree] [E.IsFinitePresentation] : Scheme.{u} :=
  (projectiveBundleData E).scheme

/-- The structural projection `P(E) → X`. -/
def projectiveBundleProjectionData
    [IsNoetherian X] (E : X.Modules)
    [E.IsLocallyFree] [E.IsFinitePresentation] :
    projectiveBundleSchemeData E ⟶ X :=
  (projectiveBundleData E).projection

/-- The selected twisting sheaf `O_{P(E)}(1)`. -/
def projectiveBundleTwistingSheafOneData
    [IsNoetherian X] (E : X.Modules)
    [E.IsLocallyFree] [E.IsFinitePresentation] :
    (projectiveBundleSchemeData E).Modules :=
  (projectiveBundleData E).twistOne

end LeanCategories.Schemes
