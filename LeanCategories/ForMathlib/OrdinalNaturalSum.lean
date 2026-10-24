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

/-- Translation by a fixed ordinal reflects strict order under Hessenberg sum. -/
theorem naturalSum_lt_iff_left {a a' b : Ordinal.{u}} :
    naturalSum a b < naturalSum a' b ↔ a < a' := by
  constructor
  · intro h
    by_contra hn
    exact (naturalSum_mono_left (le_of_not_gt hn)).not_gt h
  · exact naturalSum_lt_left

theorem naturalSum_lt_iff_right {a b b' : Ordinal.{u}} :
    naturalSum a b < naturalSum a b' ↔ b < b' := by
  constructor
  · intro h
    by_contra hn
    exact (naturalSum_mono_right (le_of_not_gt hn)).not_gt h
  · exact naturalSum_lt_right

theorem naturalSum_cancel_right {a a' b : Ordinal.{u}}
    (h : naturalSum a b = naturalSum a' b) : a = a' := by
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · exact False.elim ((naturalSum_lt_left hlt).ne h)
  · exact heq
  · exact False.elim ((naturalSum_lt_left hgt).ne h.symm)

theorem naturalSum_cancel_left {a b b' : Ordinal.{u}}
    (h : naturalSum a b = naturalSum a b') : b = b' := by
  apply naturalSum_cancel_right
  simpa only [naturalSum_comm a b, naturalSum_comm a b'] using h

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

/-- Each argument embeds monotonically below its Hessenberg sum. -/
theorem le_naturalSum_left (a b : Ordinal.{u}) : a ≤ naturalSum a b := by
  calc
    a = naturalSum a 0 := (naturalSum_zero a).symm
    _ ≤ naturalSum a b := naturalSum_mono_right zero_le

theorem le_naturalSum_right (a b : Ordinal.{u}) : b ≤ naturalSum a b := by
  calc
    b = naturalSum 0 b := (naturalSum_zero_left b).symm
    _ ≤ naturalSum a b := naturalSum_mono_left zero_le

theorem naturalSum_eq_zero_iff (a b : Ordinal.{u}) :
    naturalSum a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    exact ⟨(le_zero_iff.mp ((le_naturalSum_left a b).trans_eq h)),
      (le_zero_iff.mp ((le_naturalSum_right a b).trans_eq h))⟩
  · rintro ⟨rfl, rfl⟩
    exact naturalSum_zero 0

theorem naturalSum_lt_of_lt_of_le {a a' b b' : Ordinal.{u}}
    (ha : a < a') (hb : b ≤ b') : naturalSum a b < naturalSum a' b' :=
  (naturalSum_lt_left ha).trans_le (naturalSum_mono_right hb)

theorem naturalSum_lt_of_le_of_lt {a a' b b' : Ordinal.{u}}
    (ha : a ≤ a') (hb : b < b') : naturalSum a b < naturalSum a' b' :=
  (naturalSum_mono_left ha).trans_lt (naturalSum_lt_right hb)

/-- Natural addition by one is ordinal successor. -/
theorem naturalSum_one (a : Ordinal.{u}) : naturalSum a 1 = Order.succ a := by
  rw [naturalSum_def]
  have hleft : (⨆ x : Set.Iio a, naturalSum x.1 1 + 1) ≤ Order.succ a := by
    apply Ordinal.iSup_le
    intro x
    rw [naturalSum_one]
    exact Order.succ_le_succ (Order.succ_le_of_lt x.2)
  have hright : (⨆ y : Set.Iio (1 : Ordinal.{u}), naturalSum a y.1 + 1) =
      Order.succ a := by
    rw [ciSup_unique]
    simp [naturalSum_zero, Order.succ_eq_add_one]
  rw [hright]
  exact max_eq_right hleft
termination_by a
decreasing_by exact x.2

/-- Hessenberg sum commutes with successor in the second argument. -/
theorem naturalSum_succ (a b : Ordinal.{u}) :
    naturalSum a (Order.succ b) = Order.succ (naturalSum a b) := by
  rw [naturalSum_def]
  apply le_antisymm
  · apply max_le
    · apply Ordinal.iSup_le
      intro x
      rw [naturalSum_succ x.1 b]
      exact Order.succ_le_succ
        (Order.succ_le_of_lt (naturalSum_lt_left x.2))
    · apply Ordinal.iSup_le
      intro y
      exact Order.succ_le_succ
        (naturalSum_mono_right (Order.le_of_lt_succ y.2))
  · have h : naturalSum a b + 1 ≤
        (⨆ y : Set.Iio (Order.succ b), naturalSum a y.1 + 1) :=
      Ordinal.le_iSup (fun y : Set.Iio (Order.succ b) => naturalSum a y.1 + 1)
        ⟨b, Order.lt_succ b⟩
    exact h.trans (le_max_right _ _)
termination_by (a, b)
decreasing_by exact Prod.Lex.left _ _ x.2

/-- Hessenberg sum also commutes with successor in the first argument. -/
theorem naturalSum_succ_left (a b : Ordinal.{u}) :
    naturalSum (Order.succ a) b = Order.succ (naturalSum a b) := by
  rw [naturalSum_comm, naturalSum_succ, naturalSum_comm]

/-- Associativity when the third summand is a successor. -/
theorem naturalSum_assoc_succ (a b c : Ordinal.{u}) :
    naturalSum (naturalSum a b) (Order.succ c) =
      naturalSum a (naturalSum b (Order.succ c)) ↔
    naturalSum (naturalSum a b) c = naturalSum a (naturalSum b c) := by
  rw [naturalSum_succ, naturalSum_succ, naturalSum_succ]
  exact Order.succ_eq_succ_iff

/-- On finite right operands, Hessenberg sum agrees with ordinary ordinal addition. -/
theorem naturalSum_natCast (a : Ordinal.{u}) (n : ℕ) :
    naturalSum a (n : Ordinal.{u}) = a + n := by
  induction n with
  | zero => simp [naturalSum_zero]
  | succ n ih =>
    rw [Nat.cast_succ, ← Order.succ_eq_add_one, naturalSum_succ, ih]
    simp [Order.succ_eq_add_one, add_assoc]

/-- Associativity holds when the third Hessenberg summand is finite. -/
theorem naturalSum_assoc_natCast (a b : Ordinal.{u}) (n : ℕ) :
    naturalSum (naturalSum a b) (n : Ordinal.{u}) =
      naturalSum a (naturalSum b (n : Ordinal.{u})) := by
  induction n with
  | zero => simp [naturalSum_zero]
  | succ n ih =>
    rw [Nat.cast_succ, ← Order.succ_eq_add_one]
    exact (naturalSum_assoc_succ a b (n : Ordinal.{u})).2 ih

/-- Finite tails commute with Hessenberg addition, without assuming general associativity. -/
theorem naturalSum_add_nat (a b : Ordinal.{u}) (n : ℕ) :
    naturalSum a (b + n) = naturalSum a b + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, ← add_assoc,
      ← Order.succ_eq_add_one, naturalSum_succ, ih,
      Order.succ_eq_add_one, add_assoc]

/-- Finite tails in the first argument satisfy the same identity. -/
theorem naturalSum_add_nat_left (a b : Ordinal.{u}) (n : ℕ) :
    naturalSum (a + n) b = naturalSum a b + n := by
  rw [naturalSum_comm, naturalSum_add_nat, naturalSum_comm]

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

/-- The Hessenberg product of two positive ordinals is positive. -/
theorem naturalProduct_pos {a b : Ordinal.{u}} (ha : 0 < a) (hb : 0 < b) :
    0 < naturalProduct a b := by
  have h := naturalProduct_constraint (a' := 0) (b' := 0) ha hb
  simpa [naturalProduct_zero, naturalProduct_zero_left,
    naturalSum_zero, naturalSum_zero_left] using h

theorem naturalProduct_eq_zero_iff (a b : Ordinal.{u}) :
    naturalProduct a b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    by_contra hn
    have ha : 0 < a := lt_of_le_of_ne zero_le (Ne.symm (not_or.mp hn).1)
    have hb : 0 < b := lt_of_le_of_ne zero_le (Ne.symm (not_or.mp hn).2)
    exact (naturalProduct_pos ha hb).ne' h
  · rintro (rfl | rfl)
    · exact naturalProduct_zero_left b
    · exact naturalProduct_zero a

/-- Multiplication by a positive ordinal is strictly monotone in its first argument. -/
theorem naturalProduct_lt_left {a a' b : Ordinal.{u}}
    (ha : a < a') (hb : 0 < b) :
    naturalProduct a b < naturalProduct a' b := by
  have h := naturalProduct_constraint (a' := a) (b' := 0) ha hb
  simpa [naturalProduct_zero, naturalSum_zero] using h

/-- Multiplication by a positive ordinal is strictly monotone in its second argument. -/
theorem naturalProduct_lt_right {a b b' : Ordinal.{u}}
    (ha : 0 < a) (hb : b < b') :
    naturalProduct a b < naturalProduct a b' := by
  simpa only [naturalProduct_comm a b, naturalProduct_comm a b'] using
    (naturalProduct_lt_left hb ha)

theorem naturalProduct_mono_left {a a' b : Ordinal.{u}}
    (ha : a ≤ a') : naturalProduct a b ≤ naturalProduct a' b := by
  rcases eq_or_lt_of_le ha with rfl | h
  · exact le_rfl
  · rcases eq_or_lt_of_le (zero_le : (0 : Ordinal.{u}) ≤ b) with rfl | hb
    · simp [naturalProduct_zero]
    · exact (naturalProduct_lt_left h hb).le

theorem naturalProduct_mono_right {a b b' : Ordinal.{u}}
    (hb : b ≤ b') : naturalProduct a b ≤ naturalProduct a b' := by
  simpa only [naturalProduct_comm a b, naturalProduct_comm a b'] using
    (naturalProduct_mono_left (a := b) (a' := b') (b := a) hb)

theorem naturalProduct_mono {a a' b b' : Ordinal.{u}}
    (ha : a ≤ a') (hb : b ≤ b') :
    naturalProduct a b ≤ naturalProduct a' b' :=
  (naturalProduct_mono_left ha).trans (naturalProduct_mono_right hb)

end LeanCategories.ForMathlib.OrdinalNatural
