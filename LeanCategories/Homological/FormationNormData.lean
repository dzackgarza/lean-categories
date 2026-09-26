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

/-- The relative norm as an actual multiplicative homomorphism.  This is the
same finite-coset product as `formationRelativeNormRaw`; multiplicativity is
part of constructing the map rather than deferred to a later graph. -/
def formationRelativeNormHom
    (H : Subgroup G) (S : Subgroup H) [S.FiniteIndex] : A →* A where
  toFun := formationRelativeNormRaw (A := A) H S
  map_one' := by
    classical
    simp [formationRelativeNormRaw]
  map_mul' a b := by
    classical
    simp [formationRelativeNormRaw, Finset.prod_mul_distrib]

/-- Serre's norm group: the subgroup which is the image of the relative norm
homomorphism. -/
def formationNormGroupData
    (H : Subgroup G) (S : Subgroup H) [S.FiniteIndex] : Subgroup A :=
  (formationRelativeNormHom (A := A) H S).range

/-- The underlying set of the norm group. -/
def formationNormImageData
    (H : Subgroup G) (S : Subgroup H) [S.FiniteIndex] : Set A :=
  formationNormGroupData (A := A) H S

/-- Compatibility predicate for legacy set-level consumers. -/
def IsFormationNormGroupData
    (H : Subgroup G) (S : Subgroup H) [S.FiniteIndex] (I : Set A) : Prop :=
  I = formationNormImageData (A := A) H S

end LeanCategories.Homological
