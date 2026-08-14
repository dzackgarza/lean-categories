/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

@[expose] public section

/-!
# Zariski rings

A Zariski ring is a Noetherian ring with an adic ideal contained in its Jacobson
radical. This predicate is project-owned because the pinned Mathlib version does
not provide it.
-/

namespace LeanCategories.Algebra

universe u

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- An ideal witnessing that `R` is a Zariski ring. -/
def IsZariskiRing (I : Ideal R) : Prop :=
  IsNoetherianRing R ∧ IsAdic I ∧ I ≤ Ring.jacobson R

/-- The predicate that a commutative ring is a Zariski ring. -/
def ZariskiRing : Prop := ∃ I : Ideal R, IsZariskiRing R I

end LeanCategories.Algebra
