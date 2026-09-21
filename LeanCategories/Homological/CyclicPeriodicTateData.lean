/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Two-periodic Tate cohomology notation

Definition-level realization of Serre FC10-C08-U017.

For a finite cyclic group, Serre regards the periodic Tate complex as
`ℤ/2`-graded and writes `H⁰(A)` and `H¹(A)` for its even and odd
cohomology groups.  The checked ClassFieldTheory reference identifies the
explicit even quotient with Tate degree `0` and the explicit odd quotient
with Tate degree `-1`; its two-periodicity theorem later identifies the odd
carrier with degree `1`.

Sweep III records only these two parity carriers.  Two-periodicity,
the comparison isomorphisms, and the exact cohomology hexagon attached to a
short exact sequence are result content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

variable {G : Type} [Group G] [Fintype G] [IsCyclic G]

/-- Serre's `H⁰(A)` for the `ℤ/2`-graded periodic cyclic-group complex:
the even Tate carrier, represented by degree `0`. -/
abbrev cyclicPeriodicH0Data (A : Rep ℤ G) :=
  tateCohomology A 0

/-- Serre's `H¹(A)` for the `ℤ/2`-graded periodic cyclic-group complex:
the odd Tate carrier, represented by degree `-1`.

The external periodicity theorem identifies this carrier with Tate degree
`1`; that comparison is deliberately not part of the notation datum. -/
abbrev cyclicPeriodicH1Data (A : Rep ℤ G) :=
  tateCohomology A (-1)

end LeanCategories.Homological
