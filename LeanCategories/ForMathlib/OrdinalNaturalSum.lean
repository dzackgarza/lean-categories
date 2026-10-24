/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Adapted from Copyright (c) 2022 Violeta Hernández Palacios (Apache 2.0).
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.SetTheory.Ordinal.Family

/-!
# Hessenberg natural sum of ordinals

The recursive construction follows Violeta Hernández Palacios,
`LeanPool/MisereGames/Mathlib/NatOrdinal.lean` (Apache-2.0): the sum is the least ordinal
strictly above all sums obtained by decreasing either argument. This is the natural sum,
not ordinary ordinal addition. The cited source identifies this recursion with Hessenberg sum;
no separate Cantor-normal-form comparison is proved here. The construction is stated for all
ordinals of one universe.
-/

@[expose] public noncomputable section

namespace LeanCategories.ForMathlib.OrdinalNatural

universe u

/-- Hessenberg natural sum, recursively above every decrease of either operand. -/
def naturalSum (a b : Ordinal.{u}) : Ordinal.{u} :=
  max (⨆ x : Set.Iio a, naturalSum x.1 b + 1)
      (⨆ y : Set.Iio b, naturalSum a y.1 + 1)
termination_by (a, b)
decreasing_by
  · exact Prod.Lex.left _ _ x.property
  · exact Prod.Lex.right _ y.property

theorem naturalSum_def (a b : Ordinal.{u}) :
    naturalSum a b =
      max (⨆ x : Set.Iio a, naturalSum x.1 b + 1)
          (⨆ y : Set.Iio b, naturalSum a y.1 + 1) := by
  rw [naturalSum]

/-- Natural sum is symmetric, unlike ordinary ordinal sum. -/
theorem naturalSum_comm (a b : Ordinal.{u}) : naturalSum a b = naturalSum b a := by
  rw [naturalSum_def, naturalSum_def, max_comm]
  congr with x <;> cases x <;> exact congrArg (· + 1) (naturalSum_comm ..)
termination_by (a, b)

/-- Increasing the first operand strictly increases natural sum. -/
theorem naturalSum_lt_left {a a' b : Ordinal.{u}} (h : a < a') :
    naturalSum a b < naturalSum a' b := by
  rw [naturalSum_def a' b]
  exact (Order.lt_succ _).trans_le
    ((Ordinal.le_iSup (fun x : Set.Iio a' => naturalSum x.1 b + 1) ⟨a, h⟩).trans
      (le_max_left _ _))

/-- Increasing the second operand strictly increases natural sum. -/
theorem naturalSum_lt_right {a b b' : Ordinal.{u}} (h : b < b') :
    naturalSum a b < naturalSum a b' := by
  rw [naturalSum_def a b']
  exact (Order.lt_succ _).trans_le
    ((Ordinal.le_iSup (fun y : Set.Iio b' => naturalSum a y.1 + 1) ⟨b, h⟩).trans
      (le_max_right _ _))

theorem naturalSum_mono_left {a a' b : Ordinal.{u}} (h : a ≤ a') :
    naturalSum a b ≤ naturalSum a' b := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact (naturalSum_lt_left h).le

theorem naturalSum_mono_right {a b b' : Ordinal.{u}} (h : b ≤ b') :
    naturalSum a b ≤ naturalSum a b' := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact (naturalSum_lt_right h).le

theorem naturalSum_mono {a a' b b' : Ordinal.{u}} (ha : a ≤ a') (hb : b ≤ b') :
    naturalSum a b ≤ naturalSum a' b' :=
  (naturalSum_mono_left ha).trans (naturalSum_mono_right hb)

end LeanCategories.ForMathlib.OrdinalNatural
