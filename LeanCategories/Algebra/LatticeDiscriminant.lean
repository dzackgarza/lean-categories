/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Lattice discriminant carrier

Definition-level realization of Serre FC10-C03-U008.

For an `A`-submodule `X` of a finite field extension `L/K`, the discriminant
carrier is the `A`-span in `K` of the discriminants of all `K`-bases of `L`
whose vectors lie in `X`.  For a lattice this is the reference presentation of
Serre's discriminant ideal.

Sweep III records only the generator set and its span.  Showing that this span
is nonzero, fractional, or agrees with the top-exterior presentation is result
content.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Algebra

universe uA uK uL

variable
  (A : Type uA) [CommRing A]
  (K : Type uK) [Field K] [Algebra A K]
  (L : Type uL) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L]

/-- Discriminants of `K`-bases of `L` whose basis vectors all lie in `X`. -/
def latticeDiscriminantGenerators (X : Submodule A L) : Set K :=
  {d | ∃ b : Basis (Fin (Module.finrank K L)) K L,
    (∀ i, b i ∈ X) ∧ d = Algebra.discr K b}

/-- The lattice-discriminant carrier: the `A`-span of all admissible basis
discriminants. -/
def latticeDiscriminant (X : Submodule A L) : Submodule A K :=
  Submodule.span A (latticeDiscriminantGenerators A K L X)

/-- Serre's discriminant of the integral closure, obtained by applying the
lattice-discriminant carrier to the integral-closure submodule. -/
def integralClosureDiscriminant : Submodule A K :=
  latticeDiscriminant A K L (integralClosure A L).toSubmodule

end LeanCategories.Algebra
