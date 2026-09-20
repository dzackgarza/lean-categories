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

end LeanCategories.Homological
