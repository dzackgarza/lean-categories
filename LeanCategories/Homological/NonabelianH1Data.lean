/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Nonabelian first-cohomology data

Definition-level realization of Serre FC10-C07-U039.

Only the source's raw data are recorded here: fixed points, the crossed-cocycle
predicate, the cohomology relation, and the unit representative. Packaging the
relation as a setoid/quotient and installing the distinguished point requires
proofs that the relation is an equivalence and that the unit function is a
cocycle, so those steps are intentionally outside Sweep III.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v

variable (G : Type u) (A : Type v)
variable [Group G] [Group A] [MulDistribMulAction G A]

/-- Serre's nonabelian degree-zero cohomology data: the fixed-point locus
`A^G` (FC10-C07-U039). -/
def serreNonabelianH0Data : Set A :=
  MulAction.fixedPoints G A

/-- Serre's multiplicative crossed-cocycle predicate
`a_(st) = a_s * s(a_t)` (FC10-C07-U039). -/
def serreIsNonabelianOneCocycleData (f : G → A) : Prop :=
  ∀ s t : G, f (s * t) = f s * (s • f t)

/-- Serre's cohomology relation on raw one-cocycle functions
`b_s = a⁻¹ a_s s(a)` (FC10-C07-U039).

Whether this relation is reflexive, symmetric, and transitive on the cocycle
locus is result content and is not bundled here. -/
def serreNonabelianCohomologousData (f g : G → A) : Prop :=
  ∃ a : A, ∀ s : G, g s = a⁻¹ * f s * (s • a)

/-- The unit-function representative used for the distinguished class in
Serre's nonabelian `H¹` (FC10-C07-U039).

The fact that it satisfies the cocycle predicate is deliberately not proved or
stored in this Sweep-III datum. -/
def serreNonabelianUnitCocycleData : G → A :=
  fun _ => 1

/-- Raw degree-zero functoriality data for a homomorphism of coefficient
groups (FC10-C07-U040).

Restricting this function to fixed-point loci requires equivariance of f;
that preservation statement is result content. -/
def serreNonabelianH0MapData {B : Type*} [Group B] (f : A →* B) : A → B :=
  f

/-- Raw pointwise map on nonabelian one-cocycle functions
(FC10-C07-U040).

For an equivariant homomorphism f, proving that this sends cocycles to
cocycles, respects Serre's cohomology relation, and descends to the pointed
quotient is result content. -/
def serreNonabelianH1CocycleMapData {B : Type*} [Group B]
    (f : A →* B) (c : G → A) : G → B :=
  fun s => f (c s)

/-- The ambient B-valued boundary associated to a chosen lift b in a
nonabelian extension (FC10-C07-U044), namely s ↦ b⁻¹ * s • b.

The source's exact-sequence hypotheses imply that these values lie in the
embedded kernel A, form a cocycle there, and determine a lift-independent
class in H¹(G,A). Those implications are result content. -/
def serreNonabelianConnectingAmbientData {B : Type*} [Group B]
    [MulDistribMulAction G B] (b : B) : G → B :=
  fun s => b⁻¹ * (s • b)

/-- Raw predicate selecting an A-valued lift of Serre's ambient connecting
boundary through a supplied inclusion A → B (FC10-C07-U044).

Existence and independence of such a lift are not construction fields. -/
def serreIsNonabelianConnectingLiftData {B : Type*} [Group B]
    [MulDistribMulAction G B] (i : A →* B) (b : B) (a : G → A) : Prop :=
  ∀ s : G, i (a s) = serreNonabelianConnectingAmbientData G b s

/-- The ambient B-valued factor set associated to chosen lifts of a
nonabelian one-cocycle (FC10-C07-U045):
  (s,t) ↦ b_s * s(b_t) * b_(st)⁻¹.

Under Serre's central exact-extension hypotheses these values lie in the
embedded subgroup A and define an abelian two-cocycle there. Those statements
are result content. -/
def serreNonabelianConnectingTwoAmbientData {B : Type*} [Group B]
    [MulDistribMulAction G B] (b : G → B) : G → G → B :=
  fun s t => b s * (s • b t) * (b (s * t))⁻¹

/-- Raw predicate selecting an A-valued lift of the ambient factor set through
the supplied inclusion A → B (FC10-C07-U045).

Existence, the two-cocycle equation, independence of the chosen lifts, and
descent to H²(G,A) remain theorem-layer obligations. -/
def serreIsNonabelianConnectingTwoLiftData {B : Type*} [Group B]
    [MulDistribMulAction G B] (i : A →* B) (b : G → B)
    (a : G → G → A) : Prop :=
  ∀ s t : G, i (a s t) = serreNonabelianConnectingTwoAmbientData G b s t

end LeanCategories.Homological
