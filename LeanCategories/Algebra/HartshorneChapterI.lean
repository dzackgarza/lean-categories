/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Birational.Dominant
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Kaehler.Basic
public import LeanCategories.Algebra.ShafarevichChapterI
public import LeanCategories.Schemes.Divisors
public import LeanCategories.Schemes.Projective

/-!
# Hartshorne, Algebraic Geometry, Chapters I--III: routed vocabulary

This file records the standard names from the Hartshorne catalogue at their
existing mathematical owners.  Classical point-set affine varieties use the
Shafarevich and Dummit--Foote routes.  Scheme morphisms, rational maps,
function fields, dimension, cycles, and differentials use Mathlib directly.

No second variety hierarchy is introduced.  Hartshorne's unmatched
pointwise tangent, singularity, Weil-divisor, Cartier-divisor, and projective
morphism definitions remain explicit catalogue residue.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace LeanCategories.Algebra.HartshorneChapterI

universe u v

section AffineVarieties

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {σ : Type v}

/-- Hartshorne I.1 affine algebraic sets, routed to the Dummit--Foote owner. -/
abbrev AffineAlgebraicSet (V : Set (σ → K)) : Prop :=
  Shafarevich.AffineAlgebraicSet (k := k) (K := K) V

/-- The vanishing ideal of an affine algebraic set. -/
abbrev AffineAlgebraicSetIdeal (V : Set (σ → K)) : Ideal (MvPolynomial σ k) :=
  Shafarevich.VanishingIdeal (k := k) (V := V)

/-- Hartshorne I.1 affine varieties, presented by prime polynomial ideals. -/
abbrev AffineVariety (V : Set (σ → K)) : Prop :=
  Shafarevich.IrreducibleAffineVariety (k := k) (K := K) V

/-- The coordinate algebra attached to a prime-presented affine variety. -/
abbrev CoordinateAlgebra
    (P : Shafarevich.AffineVarietyPrimeIdeal (k := k) (σ := σ)) : Type (max u v) :=
  Shafarevich.AffineVarietyCoordinateAlgebra P

end AffineVarieties

section ProjectiveVarieties

variable {k : Type u} [CommRing k]

/-- Hartshorne I.2 projective `n`-space, routed to `Proj` over the standard grading. -/
abbrev ProjectiveSpace (n : ℕ) : Scheme.{u} :=
  Schemes.ProjectiveSpace k n

/-- A scheme admitting the standard closed-immersion presentation in projective space. -/
abbrev ProjectiveVariety (X : Scheme.{u}) : Prop :=
  Schemes.IsProjectiveVariety k X

/-- A scheme open in a projective variety. -/
abbrev QuasiProjectiveVariety (X : Scheme.{u}) : Prop :=
  Schemes.IsQuasiProjectiveVariety k X

end ProjectiveVarieties

section SchemeMaps

variable {X Y : Scheme.{u}}

/-- A morphism of varieties is routed to a morphism of schemes. -/
abbrev VarietyMorphism := X ⟶ Y

/-- An isomorphism of varieties is routed to an isomorphism of schemes. -/
abbrev VarietyIsomorphism := X ≅ Y

/-- A rational map is Mathlib's quotient of partial maps on dense opens. -/
abbrev RationalMap := Scheme.RationalMap X Y

/-- Dominance of a rational map uses Mathlib's exact rational-map predicate. -/
abbrev DominantRationalMap (f : Scheme.RationalMap X Y) : Prop :=
  f.IsDominant

/-- Birationality is Mathlib's partial-isomorphism relation on schemes. -/
abbrev Birational : Prop := Scheme.Birational X Y

end SchemeMaps

section FunctionFieldsAndDimension

variable {X : Scheme.{u}}
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {σ : Type v}

/-- The function field of an irreducible scheme. -/
noncomputable abbrev FunctionField [IrreducibleSpace X] : CommRingCat.{u} :=
  Scheme.functionField X

/-- Prime-chain height, the scheme-theoretic local dimension route. -/
abbrev PointDimension (x : X) : ℕ∞ :=
  Order.coheight x

/-- The Krull dimension of the ring presenting an affine variety. -/
abbrev AffineDimension (P : Shafarevich.AffineVarietyPrimeIdeal (k := k) (σ := σ)) :
    Cardinal.{u} :=
  LeanCategories.Algebra.AffineVarietyDimension P

end FunctionFieldsAndDimension

section CyclesAndDifferentials

variable (X : Scheme.{u})

/-- Integer-coefficient algebraic cycles, the available divisor-group route. -/
abbrev IntegerAlgebraicCycles := Schemes.IntegerAlgebraicCycle X

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The module of Kähler differentials `Ω[S/R]`. -/
abbrev KaehlerDifferentials := KaehlerDifferential R S

/-- The universal derivation into the module of Kähler differentials. -/
abbrev UniversalDerivation := KaehlerDifferential.D R S

end CyclesAndDifferentials

end LeanCategories.Algebra.HartshorneChapterI
