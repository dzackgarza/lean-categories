/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Herbrand quotient data

Definition-level realization of Neukirch FC09-C04-U080 and Serre
FC10-C08-U018.

The checked class-field-theory reference defines the Herbrand quotient for a
finite cyclic group as the ratio of the cardinalities of Tate cohomology in
degrees `0` and `-1`, under the source hypothesis that both groups are
finite.

Sweep III records only this ratio.  Periodicity, multiplicativity in short
exact sequences, and the value on finite modules are result content.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

variable {G : Type} [Group G] [Fintype G] [IsCyclic G]

/-- The Herbrand cardinality ratio `#Hhat^0(G,A) / #Hhat^(-1)(G,A)`.

The two `Finite` assumptions are precisely Neukirch's proviso that both
orders occurring in the quotient are finite. -/
def herbrandQuotient (A : Rep ℤ G)
    [Finite (tateCohomology A 0)]
    [Finite (tateCohomology A (-1))] : ℚ :=
  (Nat.card (tateCohomology A 0) : ℚ) /
    (Nat.card (tateCohomology A (-1)) : ℚ)

end LeanCategories.Homological
