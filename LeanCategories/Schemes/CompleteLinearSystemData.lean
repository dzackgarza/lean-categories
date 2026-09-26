/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.WeilDivisorClassGroupData
public import Mathlib.LinearAlgebra.Projectivization.Collinear

/-!
# Complete linear systems of Weil divisors

Definition-level realization of Hartshorne FC06-C02-U219.

For a fixed divisor `D₀`, the complete linear system `|D₀|` is the set of
effective divisors linearly equivalent to `D₀`.

Hartshorne's further identification of this set with the projective space of
nonzero sections of `L(D₀)` modulo scalars is Proposition 7.7 / FC06-C02-U218
and is result/comparison content rather than part of this definition.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace LeanCategories.Schemes

open AlgebraicGeometry

universe u v w

variable {X : Scheme.{u}} [DivisorStandingHypothesis X]

/-- Hartshorne's complete linear system
`|D₀| = {D | D ≥ 0 and D ~ D₀}`. -/
def completeLinearSystemData (D₀ : WeilDivisor X) : Set (WeilDivisor X) :=
  {D | D.IsEffective ∧ D.LinearlyEquivalentData D₀}

/-- Presentation data for a divisor linear system inside the complete linear
system of D₀.

The projective parameter space and its projective subspace are genuine
projective-linear data. The map to divisors is kept as raw data; the separate
predicate IsDivisorLinearSystemPresentationData records that its restriction
to the chosen projective subspace is injective and lands in |D₀|. This avoids
importing the result-layer identification of |D₀| with a projectivized space
of global sections. -/
structure DivisorLinearSystemPresentationData (k : Type v) [Field k]
    (D₀ : WeilDivisor X) where
  parameterSpace : ModuleCat.{w} k
  subspace : Projectivization.Subspace k parameterSpace
  pointToDivisor : ℙ k parameterSpace → WeilDivisor X

/-- The divisor members represented by a supplied projective linear system. -/
def divisorLinearSystemMembersData {k : Type v} [Field k] {D₀ : WeilDivisor X}
    (L : DivisorLinearSystemPresentationData k D₀) : Set (WeilDivisor X) :=
  L.pointToDivisor '' (L.subspace : Set (ℙ k L.parameterSpace))

/-- Source-faithfulness predicate for a supplied projective linear system:
projective points of the chosen subspace parameterize distinct effective
divisors linearly equivalent to D₀. -/
def IsDivisorLinearSystemPresentationData {k : Type v} [Field k]
    {D₀ : WeilDivisor X} (L : DivisorLinearSystemPresentationData k D₀) : Prop :=
  (∀ p ∈ (L.subspace : Set (ℙ k L.parameterSpace)),
      L.pointToDivisor p ∈ completeLinearSystemData D₀) ∧
    Set.InjOn L.pointToDivisor (L.subspace : Set (ℙ k L.parameterSpace))

/-- A one-dimensional divisor linear system (a pencil): its projective
subspace is the span of two distinct projective points. -/
def IsDivisorPencilData {k : Type v} [Field k] {D₀ : WeilDivisor X}
    (L : DivisorLinearSystemPresentationData k D₀) : Prop :=
  ∃ P Q : ℙ k L.parameterSpace,
    P ≠ Q ∧ L.subspace = Projectivization.Subspace.span {P, Q}

/-- A prime divisor is a fixed component of a divisor family when it occurs
with positive coefficient in every member. -/
def IsFixedComponentData (𝓛 : Set (WeilDivisor X)) (Y : PrimeDivisor X) : Prop :=
  ∀ D ∈ 𝓛, 0 < D Y

/-- Exact graph of the fixed part of a divisor family. It is characterized as
the greatest effective divisor lying coefficientwise below every member.
Existence of such a divisor is deliberately separate from this definition. -/
def IsFixedPartData (𝓛 : Set (WeilDivisor X)) (F : WeilDivisor X) : Prop :=
  F.IsEffective ∧
    (∀ D ∈ 𝓛, F ≤ D) ∧
    ∀ E : WeilDivisor X, E.IsEffective → (∀ D ∈ 𝓛, E ≤ D) → E ≤ F

/-- A point lies on the support of a Weil divisor when it lies on one of its
prime components with nonzero coefficient. -/
def WeilDivisor.ContainsPointData (D : WeilDivisor X) (x : X) : Prop :=
  ∃ Y : PrimeDivisor X, D Y ≠ 0 ∧ x ∈ Set.range Y.ideal.subschemeι

/-- A base point of a divisor family is a point contained in every member. -/
def IsDivisorLinearSystemBasePointData
    (𝓛 : Set (WeilDivisor X)) (x : X) : Prop :=
  ∀ D ∈ 𝓛, D.ContainsPointData x

end LeanCategories.Schemes
