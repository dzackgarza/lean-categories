/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsets
public import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
public import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.NormNum
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Finite integer square bounds, with their original inclusion

For each natural radius `r`, the selected comprehension is
`{n : ℤ | n² ≤ r²}`. Mathlib's `sq_le_sq` identifies it with the bounded
integer interval `[-r,r]`, whose finiteness is formal. The finite-set
refinement forgets to this exact subtype. The associated finite-subset
admission uses the existing `FiniteSubsets.admit`, retaining the original
comprehension as its extent.
-/

open CategoryTheory

namespace CasCatalogue.Foundation.IntegerSquareBounds

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- For a natural radius `r`, the integer subset defined by
`n ∈ squareBound r ↔ n ^ 2 ≤ (r : ℤ) ^ 2`. The theorem
`squareBound_eq_Icc` identifies this exact predicate with
`-(r : ℤ) ≤ n ∧ n ≤ (r : ℤ)`, and `squareBound_finite` proves finiteness. -/
def squareBound (r : ℕ) : Set ℤ := {n | n ^ 2 ≤ (r : ℤ) ^ 2}

theorem squareBound_eq_Icc (r : ℕ) :
    squareBound r = Set.Icc (-(r : ℤ)) (r : ℤ) := by
  ext n
  simp only [squareBound, Set.mem_ofPred_eq, Set.mem_Icc, sq_le_sq,
    abs_of_nonneg (Int.natCast_nonneg r), abs_le]

theorem squareBound_finite (r : ℕ) : (squareBound r).Finite := by
  rw [squareBound_eq_Icc]
  exact Set.finite_Icc _ _

/-- For `r : ℕ`, the set object with carrier
`{n : ℤ // n ^ 2 ≤ (r : ℤ) ^ 2}`. An element retains its integer and its
membership in the square-bound predicate; equivalently its integer lies in
`[-r, r]` by `squareBound_eq_Icc`. `inclusion r` sends the element to that
integer in the ambient set `ℤ`. Every natural radius is admitted. -/
abbrev extent (r : ℕ) : SetsCat.{0} := squareBound r

instance extent_finite (r : ℕ) : Finite (extent r) := (squareBound_finite r).to_subtype

/-- For `r : ℕ`, the inclusion from
`{n : ℤ // n ^ 2 ≤ (r : ℤ) ^ 2}` into the set of all integers, sending
`⟨n, hn⟩` to `n`. Its domain is `extent r`, and `inclusion_mono` proves
monicity. The ambient codomain remains the full integer set. -/
def inclusion (r : ℕ) : extent r ⟶ integers := TypeCat.ofHom Subtype.val

instance inclusion_mono (r : ℕ) : Mono (inclusion r) :=
  (CategoryTheory.mono_iff_injective _).mpr Subtype.val_injective

/-- For `r : ℕ`, the finite-set object with the same carrier
`{n : ℤ // n ^ 2 ≤ (r : ℤ) ^ 2}` as `extent r`, equipped with finiteness
from `squareBound_finite`. `finiteIdentification` identifies its forgotten
set with that very subtype by the identity. Membership is equivalently
`-r ≤ n ≤ r` by `squareBound_eq_Icc`; the integer inclusion is `inclusion r`. -/
abbrev finiteExtent (r : ℕ) : LeanCategories.Foundation.Mathlib.FiniteSets.{0} :=
  FintypeCat.of (extent r)

/-- The identity set isomorphism from the forgotten `finiteExtent r` to
`extent r`, retaining both the integer and the square-bound membership.
Both directions act as the identity on the same subtype. -/
def finiteIdentification (r : ℕ) :
    LeanCategories.Foundation.Mathlib.finite.forget.toFunctor.obj (finiteExtent r) ≅
      extent r := Iso.refl _

/-- For `r : ℕ`, the constant point `Fin 1 → Set ℤ` with value
`{n : ℤ | n ^ 2 ≤ (r : ℤ) ^ 2}`, equivalently the closed integer interval
`[-r, r]` by `squareBound_eq_Icc`. The codomain is the power set of all
integers; its returned value is the complete selected subset. -/
def subset (r : ℕ) : fin 1 ⟶ powerSet ℤ := TypeCat.ofHom fun _ => squareBound r

/-- For `r : ℕ`, the constant point `Fin 1 → Finset ℤ` representing exactly
the finite subset `{n : ℤ | n ^ 2 ≤ (r : ℤ) ^ 2}`. It is formed by
`FiniteSubsets.admit` using `squareBound_finite`, so its elements are precisely
the integers from `-r` to `r`. `admission_retains_subset` states that coercing
this finite subset into `Set ℤ` recovers the point `subset r`. -/
noncomputable def admittedSubset (r : ℕ) : fin 1 ⟶ FiniteSubsets.finiteSubsets ℤ :=
  FiniteSubsets.admit ℤ (squareBound r) (squareBound_finite r)

theorem admission_retains_subset (r : ℕ) :
    admittedSubset r ≫ FiniteSubsets.inclusion ℤ = subset r :=
  FiniteSubsets.inclusion_admit ℤ (squareBound r) (squareBound_finite r)

theorem finiteHolds (r : ℕ) :
    Classifier.Holds LeanCategories.Foundation.Mathlib.finite (extent r) :=
  (Finiteness.finiteHolds_iff _).mpr inferInstance

theorem integers_not_finiteHolds :
    ¬ Classifier.Holds LeanCategories.Foundation.Mathlib.finite integers := by
  rw [Finiteness.finiteHolds_iff]
  intro h
  exact Finite.false (α := ℤ) h

theorem squareBound_three : squareBound 3 = {n : ℤ | n ^ 2 ≤ 9} := by
  norm_num [squareBound]

theorem squareBound_three_members :
    squareBound 3 = ({-3, -2, -1, 0, 1, 2, 3} : Set ℤ) := by
  ext n
  rw [squareBound_eq_Icc]
  simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

theorem extent_three_card : Nat.card (extent 3) = 7 := by
  change Nat.card (squareBound 3) = 7
  rw [squareBound_eq_Icc]
  norm_num [Nat.card_eq_fintype_card, Int.card_Icc]
  decide

end CasCatalogue.Foundation.IntegerSquareBounds

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.integer_square_bound"⟩, category := CategoryId.sets
    name := "IntegerSquareBound", declaration := `CasCatalogue.Foundation.IntegerSquareBounds.extent
    inclusion := some `CasCatalogue.Foundation.IntegerSquareBounds.inclusion }

normalized_registry .object
  { id := ⟨"obj.finite_sets.integer_square_bound"⟩, category := CategoryId.finiteSets
    name := "IntegerSquareBound", declaration := `CasCatalogue.Foundation.IntegerSquareBounds.finiteExtent
    refines := some
      { base := ⟨"obj.sets.integer_square_bound"⟩
        route := #[.classifierForget ClassifierId.setsFinite]
        identification := `CasCatalogue.Foundation.IntegerSquareBounds.finiteIdentification } }

normalized_registry .morphism
  { id := ⟨"mor.sets.integer_square_bound_subset"⟩, category := CategoryId.sets
    name := "integer_square_bound_subset", declaration := `CasCatalogue.Foundation.IntegerSquareBounds.subset }

normalized_registry .morphism
  { id := ⟨"mor.sets.integer_square_bound_admitted"⟩, category := CategoryId.sets
    name := "integer_square_bound_admitted"
    declaration := `CasCatalogue.Foundation.IntegerSquareBounds.admittedSubset }

end CasCatalogue
