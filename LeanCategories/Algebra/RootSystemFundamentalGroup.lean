/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Fundamental group of a root system

Definition-level realization of Humphreys FC14-C03-U057.  Once the weight
lattice `Λ` and its root sublattice `Λᵣ` have been supplied by U055, the
fundamental group is simply the additive quotient `Λ / Λᵣ`.

Finiteness, the determinant formula for its order, and the irreducible-type
order table are result content and are not included here.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

/-- Humphreys' fundamental group `Λ / Λᵣ` of a root system, expressed from
the already supplied weight-lattice carrier and root sublattice. -/
abbrev RootSystemFundamentalGroup
    (Λ : Type u) [AddCommGroup Λ] (Λr : AddSubgroup Λ) :=
  Λ ⧸ Λr

end LeanCategories.Algebra
