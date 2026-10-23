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

/-- The actual square-inequality comprehension in the integers. -/
def squareBound (r : ℕ) : Set ℤ := {n | n ^ 2 ≤ (r : ℤ) ^ 2}

theorem squareBound_eq_Icc (r : ℕ) :
    squareBound r = Set.Icc (-(r : ℤ)) (r : ℤ) := by
  ext n
  simp only [squareBound, Set.mem_ofPred_eq, Set.mem_Icc, sq_le_sq,
    abs_of_nonneg (Int.natCast_nonneg r), abs_le]

theorem squareBound_finite (r : ℕ) : (squareBound r).Finite := by
  rw [squareBound_eq_Icc]
  exact Set.finite_Icc _ _

/-- The set of members, preserving the defining predicate. -/
abbrev extent (r : ℕ) : SetsCat.{0} := squareBound r

instance extent_finite (r : ℕ) : Finite (extent r) := (squareBound_finite r).to_subtype

/-- Inclusion of this subset into the original infinite ambient set. -/
def inclusion (r : ℕ) : extent r ⟶ integers := TypeCat.ofHom Subtype.val

instance inclusion_mono (r : ℕ) : Mono (inclusion r) :=
  (CategoryTheory.mono_iff_injective _).mpr Subtype.val_injective

/-- The same subtype equipped with its formally established finiteness. -/
abbrev finiteExtent (r : ℕ) : LeanCategories.Foundation.Mathlib.FiniteSets.{0} :=
  FintypeCat.of (extent r)

def finiteIdentification (r : ℕ) :
    LeanCategories.Foundation.Mathlib.finite.forget.toFunctor.obj (finiteExtent r) ≅
      extent r := Iso.refl _

/-- The original comprehension as a point of the power set. -/
def subset (r : ℕ) : fin 1 ⟶ powerSet ℤ := TypeCat.ofHom fun _ => squareBound r

/-- Admission uses the preexisting finite-subset operation and a formal proof. -/
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
