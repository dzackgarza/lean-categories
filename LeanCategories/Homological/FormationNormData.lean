/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Raw relative-norm data for class formations

Definition-level realization of the transfer formula underlying Serre,
*Local Fields*, Chapter XI, `FC10-C11-U021`.

For a finite-index subgroup `S ≤ H ≤ G` and a multiplicative `G`-module `A`,
the relative norm is represented by the product of the translates of a
coefficient over a chosen set of coset representatives.  Sweep III records
that displayed product only.

Independence of the chosen representatives, the assertion that an
`S`-fixed coefficient is sent to an `H`-fixed coefficient, multiplicativity,
tower laws, and agreement with the ordinary field norm are result content.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanCategories.Homological

universe u v

variable {G : Type u} [Group G]
variable {A : Type v} [CommGroup A] [MulDistribMulAction G A]

/-- Raw transfer/norm product for a finite-index subgroup `S ≤ H ≤ G`.

The quotient representative selected by `Quotient.out` is deliberately part
of the raw data.  Its irrelevance for `S`-fixed inputs is a theorem. -/
def formationRelativeNormRaw
    (H : Subgroup G) (S : Subgroup H) [S.FiniteIndex] (a : A) : A := by
  letI := S.fintypeQuotientOfFiniteIndex
  exact ∏ q : H ⧸ S, (((Quotient.out q : H) : G) • a)

/-- The raw image set of the relative norm.  When restricted to the
appropriate fixed coefficient group and after proving the norm laws, this is
Serre's norm subgroup. -/
def formationNormImageData
    (H : Subgroup G) (S : Subgroup H) [S.FiniteIndex] : Set A :=
  Set.range (formationRelativeNormRaw (A := A) H S)

/-- Raw predicate expressing that a subset is the norm image attached to a
given finite-index subgroup pair (FC10-C11-U022).

After proving that the relative norm is a homomorphism on the appropriate
fixed coefficient group, this image is a subgroup.  That closure statement is
not part of the Sweep-III carrier. -/
def IsFormationNormGroupData
    (H : Subgroup G) (S : Subgroup H) [S.FiniteIndex] (I : Set A) : Prop :=
  I = formationNormImageData (A := A) H S

end LeanCategories.Homological
