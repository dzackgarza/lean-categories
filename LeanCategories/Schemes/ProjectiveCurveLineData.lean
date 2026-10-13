/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Collinear

/-!
# Secant and tangent-line data for embedded curves

Definition-level realization of Hartshorne FC06-C04-U047.

For an embedded curve in projective space, the secant through two distinct
points is their projective span. The tangent line at a point is characterized
as the projective line through that point whose embedded tangent subspace is
the tangent subspace of the curve.

The current projective-space API supplies spans and projective subspaces, but
does not supply the scheme-theoretic embedded-tangent comparison. Sweep III
therefore stores the tangent-line assignment itself as proof-free presentation
data, and records Hartshorne's incidence/rank/tangent-space conditions
separately as a source-faithfulness predicate.
-/

@[expose] public noncomputable section

open scoped LinearAlgebra.Projectivization

namespace LeanCategories.Schemes

universe u v w

variable (k : Type u) [Field k]
variable (V : Type v) [AddCommGroup V] [Module k V]

/-- The secant line through two projective points: their projective span. -/
def projectiveSecantLineData (P Q : ℙ k V) :
    Projectivization.Subspace k V :=
  Projectivization.Subspace.span {P, Q}

/-- Source-level tangent presentation for a curve embedded in projective
space.

For every ambient projective point `P`, `T P` is the vector space
`T_P(P(V))`.  The two assignments land in submodules of that *same* ambient
tangent space: the embedded tangent subspace of the curve and the embedded
tangent subspace of a candidate projective line.  Their scheme-theoretic
construction is an earlier geometric input; no comparison theorem is bundled
into this data. -/
structure ProjectiveCurveTangentPresentationData
    (curve : Set (ℙ k V))
    (T : ℙ k V → Type w)
    [∀ P, AddCommGroup (T P)] [∀ P, Module k (T P)] where
  curveTangent :
    (P : ℙ k V) → P ∈ curve → Submodule k (T P)
  lineTangent :
    Projectivization.Subspace k V → (P : ℙ k V) →
      P ∈ curve → Submodule k (T P)
  tangentLine :
    (P : ℙ k V) → P ∈ curve → Projectivization.Subspace k V

/-- Hartshorne's graph for the tangent line at P: it is a projective line
through P and has the same embedded tangent subspace there as the curve. -/
def IsProjectiveCurveTangentLineData
    {curve : Set (ℙ k V)}
    {T : ℙ k V → Type w}
    [∀ P, AddCommGroup (T P)] [∀ P, Module k (T P)]
    (D : ProjectiveCurveTangentPresentationData k V curve T)
    (P : ℙ k V) (hP : P ∈ curve)
    (L : Projectivization.Subspace k V) : Prop :=
  P ∈ L ∧
    Module.finrank k L.submodule = 2 ∧
      D.lineTangent L P hP = D.curveTangent P hP

/-- Source-faithfulness of a supplied tangent-line assignment. -/
def IsProjectiveCurveTangentPresentationData
    {curve : Set (ℙ k V)}
    {T : ℙ k V → Type w}
    [∀ P, AddCommGroup (T P)] [∀ P, Module k (T P)]
    (D : ProjectiveCurveTangentPresentationData k V curve T) : Prop :=
  ∀ (P : ℙ k V) (hP : P ∈ curve),
    IsProjectiveCurveTangentLineData k V D P hP (D.tangentLine P hP)

/-- The tangent line supplied by source-level presentation data. -/
def projectiveTangentLineData
    {curve : Set (ℙ k V)}
    {T : ℙ k V → Type w}
    [∀ P, AddCommGroup (T P)] [∀ P, Module k (T P)]
    (D : ProjectiveCurveTangentPresentationData k V curve T)
    (P : ℙ k V) (hP : P ∈ curve) :
    Projectivization.Subspace k V :=
  D.tangentLine P hP

end LeanCategories.Schemes
