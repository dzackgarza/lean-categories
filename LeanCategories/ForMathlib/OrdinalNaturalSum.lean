/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Adapted from Copyright (c) 2022 Violeta Hernández Palacios (Apache 2.0).
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.SetTheory.Ordinal.Family
public import Mathlib.Order.SuccPred.CompleteLinearOrder

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

theorem naturalSum_zero (a : Ordinal.{u}) : naturalSum a 0 = a := by
  rw [naturalSum_def]
  rw [ciSup_of_empty (fun _ : Set.Iio 0 => _), max_bot_right]
  calc
    (⨆ x : Set.Iio a, naturalSum x.1 0 + 1) =
        ⨆ x : Set.Iio a, Order.succ x.1 := by
          congr with x
          rw [naturalSum_zero]
          rfl
    _ = a := iSup_succ a
termination_by a
decreasing_by exact x.property

/-- Zero is also the left identity for Hessenberg sum. -/
theorem naturalSum_zero_left (a : Ordinal.{u}) : naturalSum 0 a = a := by
  rw [naturalSum_comm, naturalSum_zero]

theorem naturalSum_lt_of_lt_of_le {a a' b b' : Ordinal.{u}}
    (ha : a < a') (hb : b ≤ b') : naturalSum a b < naturalSum a' b' :=
  (naturalSum_lt_left ha).trans_le (naturalSum_mono_right hb)

theorem naturalSum_lt_of_le_of_lt {a a' b b' : Ordinal.{u}}
    (ha : a ≤ a') (hb : b < b') : naturalSum a b < naturalSum a' b' :=
  (naturalSum_mono_left ha).trans_lt (naturalSum_lt_right hb)

/-- Hessenberg natural product: the least ordinal `c` for which every simultaneous decrease
of `a` and `b` satisfies `(a' ⊗ b) ⊕ (a ⊗ b') < c ⊕ (a' ⊗ b')`, with the products on the
left interpreted recursively. This is the recursive source definition, with `⊕` explicitly
the natural sum above. -/
def naturalProduct (a b : Ordinal.{u}) : Ordinal.{u} :=
  sInf {c | ∀ a' < a, ∀ b' < b,
    naturalSum (naturalProduct a' b) (naturalProduct a b') <
      naturalSum c (naturalProduct a' b')}
termination_by (a, b)

theorem naturalProduct_def (a b : Ordinal.{u}) :
    naturalProduct a b = sInf {c | ∀ a' < a, ∀ b' < b,
      naturalSum (naturalProduct a' b) (naturalProduct a b') <
        naturalSum c (naturalProduct a' b')} := by
  rw [naturalProduct]

/-- The recursive constraint defining natural product always has an ordinal solution. -/
theorem naturalProduct_admissible (a b : Ordinal.{u}) :
    ({c : Ordinal.{u} | ∀ a' < a, ∀ b' < b,
      naturalSum (naturalProduct a' b) (naturalProduct a b') <
        naturalSum c (naturalProduct a' b')}).Nonempty := by
  let f : Set.Iio a × Set.Iio b → Ordinal.{u} :=
    fun x => naturalSum (naturalProduct x.1.1 b) (naturalProduct a x.2.1)
  obtain ⟨c, hc⟩ : BddAbove (Set.range f) := Ordinal.bddAbove_of_small
  refine ⟨c + 1, ?_⟩
  intro a' ha b' hb
  have hle : naturalSum (naturalProduct a' b) (naturalProduct a b') ≤ c := by
    exact hc (Set.mem_range_self ((⟨a', ha⟩, ⟨b', hb⟩) : Set.Iio a × Set.Iio b))
  have hright : c + 1 ≤ naturalSum (c + 1) (naturalProduct a' b') := by
    calc
      c + 1 = naturalSum (c + 1) 0 := (naturalSum_zero _).symm
      _ ≤ _ := naturalSum_mono_right zero_le
  exact (Order.lt_succ_of_le hle).trans_le hright

/-- The recursively defined product satisfies every constraint used to define it. -/
theorem naturalProduct_constraint {a a' b b' : Ordinal.{u}} (ha : a' < a) (hb : b' < b) :
    naturalSum (naturalProduct a' b) (naturalProduct a b') <
      naturalSum (naturalProduct a b) (naturalProduct a' b') := by
  rw [naturalProduct_def a b]
  exact csInf_mem (naturalProduct_admissible a b) a' ha b' hb

/-- Natural product is symmetric. The defining inequalities are exchanged by swapping the
operands and using symmetry of natural sum. -/
theorem naturalProduct_comm (a b : Ordinal.{u}) : naturalProduct a b = naturalProduct b a := by
  rw [naturalProduct_def a b, naturalProduct_def b a]
  congr 1
  ext c
  constructor
  · intro H b' hb a' ha
    simpa only [naturalSum_comm, naturalProduct_comm a' b,
      naturalProduct_comm a b', naturalProduct_comm a' b'] using H a' ha b' hb
  · intro H a' ha b' hb
    simpa only [naturalSum_comm, naturalProduct_comm a' b,
      naturalProduct_comm a b', naturalProduct_comm a' b'] using H b' hb a' ha
termination_by (a, b)

theorem naturalProduct_zero (a : Ordinal.{u}) : naturalProduct a 0 = 0 := by
  rw [naturalProduct_def]
  simp

theorem naturalProduct_zero_left (a : Ordinal.{u}) : naturalProduct 0 a = 0 := by
  rw [naturalProduct_comm, naturalProduct_zero]

/-- One is the right identity of Hessenberg natural product. -/
theorem naturalProduct_one (a : Ordinal.{u}) : naturalProduct a 1 = a := by
  rw [naturalProduct_def]
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, fun _ _ => zero_le⟩
    · intro a' ha b' hb
      have : b' = 0 := Order.lt_one_iff.mp hb
      subst b'
      simpa [naturalProduct_zero, naturalSum_zero, naturalProduct_one a'] using ha
  · apply le_csInf (naturalProduct_admissible a 1)
    intro c hc
    have h : ∀ a' < a, a' < c := by
      intro a' ha
      have := hc a' ha 0 (zero_lt_one' Ordinal)
      simpa [naturalProduct_zero, naturalSum_zero, naturalProduct_one a'] using this
    calc
      a = ⨆ x : Set.Iio a, Order.succ x.1 := (iSup_succ a).symm
      _ ≤ c := by
        apply Ordinal.iSup_le
        intro x
        exact Order.succ_le_of_lt (h x.1 x.2)
termination_by a
decreasing_by all_goals assumption

/-- One is also the left identity of Hessenberg natural product. -/
theorem naturalProduct_one_left (a : Ordinal.{u}) : naturalProduct 1 a = a := by
  rw [naturalProduct_comm, naturalProduct_one]

end LeanCategories.ForMathlib.OrdinalNatural
