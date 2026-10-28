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

/-- A finite left operand contributes a finite right tail, by commutativity. -/
theorem naturalSum_natCast_left (n : ℕ) (a : Ordinal.{u}) :
    naturalSum (n : Ordinal.{u}) a = a + n := by
  rw [naturalSum_comm, naturalSum_natCast]

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

/-- Associativity when the first summand is finite. This follows from the finite-tail
identity and commutativity, without assuming general associativity. -/
theorem naturalSum_assoc_natCast_left (n : ℕ) (b c : Ordinal.{u}) :
    naturalSum (naturalSum (n : Ordinal.{u}) b) c =
      naturalSum (n : Ordinal.{u}) (naturalSum b c) := by
  calc
    naturalSum (naturalSum (n : Ordinal.{u}) b) c = naturalSum (b + n) c := by
      rw [naturalSum_natCast_left]
    _ = naturalSum b c + n := naturalSum_add_nat_left b c n
    _ = naturalSum (n : Ordinal.{u}) (naturalSum b c) := by
      rw [naturalSum_natCast_left]

/-- Associativity when the middle summand is finite. -/
theorem naturalSum_assoc_natCast_middle (a : Ordinal.{u}) (n : ℕ) (c : Ordinal.{u}) :
    naturalSum (naturalSum a (n : Ordinal.{u})) c =
      naturalSum a (naturalSum (n : Ordinal.{u}) c) := by
  calc
    naturalSum (naturalSum a (n : Ordinal.{u})) c = naturalSum (a + n) c := by
      rw [naturalSum_natCast]
    _ = naturalSum a c + n := naturalSum_add_nat_left a c n
    _ = naturalSum a (naturalSum (n : Ordinal.{u}) c) := by
      rw [naturalSum_natCast_left, naturalSum_add_nat]

/-- One direction of associativity, proved by induction on the three ordinal operands.
The recursive definition makes each operand-decrease term cofinal below the corresponding sum,
including at limit ordinals. -/
theorem naturalSum_assoc_le (a b c : Ordinal.{u}) :
    naturalSum (naturalSum a b) c ≤ naturalSum a (naturalSum b c) := by
  rw [naturalSum_def]
  apply max_le
  · apply Ordinal.iSup_le
    intro x
    have hx := x.2.trans_eq (naturalSum_def a b)
    rcases lt_max_iff.mp hx with hx | hx
    · obtain ⟨⟨a', ha'⟩, hx'⟩ := Ordinal.lt_iSup_iff.mp hx
      have hx' : x.1 ≤ naturalSum a' b := Order.lt_succ_iff.mp hx'
      have hle : naturalSum x.1 c ≤ naturalSum (naturalSum a' b) c :=
        naturalSum_mono_left hx'
      have hrec := naturalSum_assoc_le a' b c
      exact Order.succ_le_of_lt ((hle.trans hrec).trans_lt (naturalSum_lt_left ha'))
    · obtain ⟨⟨b', hb'⟩, hx'⟩ := Ordinal.lt_iSup_iff.mp hx
      have hx' : x.1 ≤ naturalSum a b' := Order.lt_succ_iff.mp hx'
      have hle : naturalSum x.1 c ≤ naturalSum (naturalSum a b') c :=
        naturalSum_mono_left hx'
      have hrec := naturalSum_assoc_le a b' c
      exact Order.succ_le_of_lt <| (hle.trans hrec).trans_lt <|
        naturalSum_lt_right (a := a) (naturalSum_lt_left hb')
  · apply Ordinal.iSup_le
    intro z
    have hrec := naturalSum_assoc_le a b z.1
    exact Order.succ_le_of_lt <| hrec.trans_lt <| naturalSum_lt_right (a := a) <|
      naturalSum_lt_right (a := b) z.2
termination_by (a, b, c)
decreasing_by
  · exact Prod.Lex.left _ _ ha'
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ hb')
  · exact Prod.Lex.right _ (Prod.Lex.right _ z.2)

/-- Hessenberg natural sum is associative. -/
theorem naturalSum_assoc (a b c : Ordinal.{u}) :
    naturalSum (naturalSum a b) c = naturalSum a (naturalSum b c) := by
  apply le_antisymm
  · exact naturalSum_assoc_le a b c
  · calc
      naturalSum a (naturalSum b c) = naturalSum (naturalSum c b) a := by
        rw [naturalSum_comm b c, naturalSum_comm a (naturalSum c b)]
      _ ≤ naturalSum c (naturalSum b a) := naturalSum_assoc_le c b a
      _ = naturalSum (naturalSum a b) c := by
        rw [naturalSum_comm b a, naturalSum_comm c (naturalSum a b)]

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

/-- A positive factor makes natural multiplication an order embedding. -/
theorem naturalProduct_lt_iff_left {a a' b : Ordinal.{u}} (hb : 0 < b) :
    naturalProduct a b < naturalProduct a' b ↔ a < a' := by
  constructor
  · intro h
    by_contra hn
    exact (naturalProduct_mono_left (le_of_not_gt hn)).not_gt h
  · exact fun h => naturalProduct_lt_left h hb

theorem naturalProduct_lt_iff_right {a b b' : Ordinal.{u}} (ha : 0 < a) :
    naturalProduct a b < naturalProduct a b' ↔ b < b' := by
  simpa only [naturalProduct_comm a b, naturalProduct_comm a b'] using
    (naturalProduct_lt_iff_left (a := b) (a' := b') ha)

/-- Cancellation is valid with the positive-factor hypothesis. -/
theorem naturalProduct_cancel_right {a a' b : Ordinal.{u}}
    (hb : 0 < b) (h : naturalProduct a b = naturalProduct a' b) : a = a' := by
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · exact False.elim ((naturalProduct_lt_left hlt hb).ne h)
  · exact heq
  · exact False.elim ((naturalProduct_lt_left hgt hb).ne h.symm)

theorem naturalProduct_cancel_left {a b b' : Ordinal.{u}}
    (ha : 0 < a) (h : naturalProduct a b = naturalProduct a b') : b = b' := by
  apply naturalProduct_cancel_right ha
  simpa only [naturalProduct_comm a b, naturalProduct_comm a b'] using h

/-- Finite-arity Hessenberg sum, with a fixed parenthesization. The associativity theorem below
shows that this parenthesization does not affect the result. -/
def naturalSumList : List Ordinal.{u} → Ordinal.{u}
  | [] => 0
  | a :: as => naturalSum a (naturalSumList as)

/-- Finite-arity Hessenberg product with multiplicative empty-family value. -/
def naturalProductList : List Ordinal.{u} → Ordinal.{u}
  | [] => 1
  | a :: as => naturalProduct a (naturalProductList as)

@[simp] theorem naturalSumList_nil : naturalSumList ([] : List Ordinal.{u}) = 0 := rfl
@[simp] theorem naturalProductList_nil : naturalProductList ([] : List Ordinal.{u}) = 1 := rfl

@[simp] theorem naturalSumList_singleton (a : Ordinal.{u}) :
    naturalSumList [a] = a := by simp [naturalSumList, naturalSum_zero]

@[simp] theorem naturalProductList_singleton (a : Ordinal.{u}) :
    naturalProductList [a] = a := by simp [naturalProductList, naturalProduct_one]

theorem naturalSumList_pair (a b : Ordinal.{u}) :
    naturalSumList [a, b] = naturalSum a b := by
  simp [naturalSumList, naturalSum_zero]

/-- Concatenating two finite families computes the natural sum of their respective sums.
The general associativity theorem makes this independent of the chosen list split. -/
theorem naturalSumList_append (as bs : List Ordinal.{u}) :
    naturalSumList (as ++ bs) = naturalSum (naturalSumList as) (naturalSumList bs) := by
  induction as with
  | nil => simp [naturalSumList, naturalSum_zero_left]
  | cons a as ih =>
    simp only [List.cons_append, naturalSumList]
    rw [ih, ← naturalSum_assoc]

/-- Reordering two consecutive blocks of summands does not change their finite natural sum. -/
theorem naturalSumList_append_comm (as bs : List Ordinal.{u}) :
    naturalSumList (as ++ bs) = naturalSumList (bs ++ as) := by
  rw [naturalSumList_append, naturalSumList_append, naturalSum_comm]

/-- Finite Hessenberg sums are invariant under every permutation of their summands. -/
theorem naturalSumList_perm {as bs : List Ordinal.{u}} (h : as.Perm bs) :
    naturalSumList as = naturalSumList bs := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [naturalSumList]; rw [ih]
  | @swap a b tail =>
      simp only [naturalSumList]
      rw [← naturalSum_assoc, naturalSum_comm b a, naturalSum_assoc]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem naturalProductList_pair (a b : Ordinal.{u}) :
    naturalProductList [a, b] = naturalProduct a b := by
  simp [naturalProductList, naturalProduct_one]

/-- Pointwise comparisons of equally indexed finite families induce a comparison
of their Hessenberg sums by pointwise monotonicity. -/
theorem naturalSumList_mono {as bs : List Ordinal.{u}}
    (h : List.Forall₂ (· ≤ ·) as bs) : naturalSumList as ≤ naturalSumList bs := by
  induction h with
  | nil => exact le_rfl
  | @cons a b as bs hab _ ih => exact naturalSum_mono hab ih

/-- Pointwise comparisons induce a comparison of finite Hessenberg products. -/
theorem naturalProductList_mono {as bs : List Ordinal.{u}}
    (h : List.Forall₂ (· ≤ ·) as bs) :
    naturalProductList as ≤ naturalProductList bs := by
  induction h with
  | nil => exact le_rfl
  | @cons a b as bs hab _ ih => exact naturalProduct_mono hab ih

/-- A finite natural product vanishes exactly when one of its factors vanishes. -/
theorem naturalProductList_eq_zero_iff (as : List Ordinal.{u}) :
    naturalProductList as = 0 ↔ (0 : Ordinal.{u}) ∈ as := by
  induction as with
  | nil => simp [naturalProductList]
  | cons a as ih =>
    simp only [naturalProductList, naturalProduct_eq_zero_iff, ih,
      List.mem_cons]
    rw [eq_comm (a := (0 : Ordinal.{u})) (b := a)]

/-- A finite natural sum vanishes exactly when every summand vanishes. -/
theorem naturalSumList_eq_zero_iff (as : List Ordinal.{u}) :
    naturalSumList as = 0 ↔ ∀ a ∈ as, a = 0 := by
  induction as with
  | nil => simp [naturalSumList]
  | cons a as ih =>
    simp only [naturalSumList, naturalSum_eq_zero_iff, ih,
      List.mem_cons, forall_eq_or_imp]

/-- A finite natural product is positive precisely when all factors are positive;
the empty product is positive. -/
theorem naturalProductList_pos_iff (as : List Ordinal.{u}) :
    0 < naturalProductList as ↔ ∀ a ∈ as, 0 < a := by
  induction as with
  | nil => simp [naturalProductList]
  | cons a as ih =>
    simp only [naturalProductList, List.mem_cons, forall_eq_or_imp]
    rw [← ih]
    simp only [pos_iff_ne_zero, ne_eq, naturalProduct_eq_zero_iff, not_or]

/-- Appending a finite ordinal to a finite Hessenberg sum agrees with ordinary
ordinal addition by that finite ordinal. -/
theorem naturalSumList_append_nat (as : List Ordinal.{u}) (n : ℕ) :
    naturalSumList (as ++ [(n : Ordinal.{u})]) = naturalSumList as + n := by
  induction as with
  | nil => simp [naturalSumList, naturalSum_natCast]
  | cons a as ih =>
    simp only [List.cons_append, naturalSumList]
    rw [ih, naturalSum_add_nat]

/-- A finite product is zero as soon as one factor is zero, independently of its
position in the selected parenthesization. -/
theorem naturalProductList_zero_of_mem {as : List Ordinal.{u}}
    (h : (0 : Ordinal.{u}) ∈ as) : naturalProductList as = 0 :=
  (naturalProductList_eq_zero_iff as).2 h

/-- A finite natural sum is positive exactly when some summand is positive. -/
theorem naturalSumList_pos_iff (as : List Ordinal.{u}) :
    0 < naturalSumList as ↔ ∃ a ∈ as, 0 < a := by
  rw [pos_iff_ne_zero, ne_eq, naturalSumList_eq_zero_iff]
  push_neg
  simp only [pos_iff_ne_zero, ne_eq]

/-- Each finite summand is bounded above by the sum of the entire list. -/
theorem le_naturalSumList_of_mem {as : List Ordinal.{u}}
    {a : Ordinal.{u}} (h : a ∈ as) : a ≤ naturalSumList as := by
  induction as with
  | nil => cases h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with heq | h
    · subst a
      exact le_naturalSum_left b (naturalSumList bs)
    · exact (ih h).trans (le_naturalSum_right b (naturalSumList bs))

/-- Every finite factor is at most its product when all the other factors are
positive; this follows from monotonicity and the unit law. -/
theorem le_naturalProductList_of_mem {as : List Ordinal.{u}}
    {a : Ordinal.{u}} (h : a ∈ as)
    (hp : ∀ b ∈ as, 0 < b) : a ≤ naturalProductList as := by
  induction as with
  | nil => cases h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with heq | h
    · subst a
      have ht : 1 ≤ naturalProductList bs :=
        (Ordinal.one_le_iff_ne_zero).2
          (((naturalProductList_pos_iff bs).2
            (fun x hx => hp x (List.mem_cons_of_mem b hx))).ne')
      simpa [naturalProductList, naturalProduct_one] using
        (naturalProduct_mono_right (a := b) ht)
    · have hb : 1 ≤ b := (Ordinal.one_le_iff_ne_zero).2
        ((hp b (List.mem_cons_self ..)).ne')
      exact (ih h (fun x hx => hp x (List.mem_cons_of_mem b hx))).trans
        (by simpa [naturalProductList, naturalProduct_one_left] using
          (naturalProduct_mono_left (b := naturalProductList bs) hb))

/-- A pointwise strict increase of every entry strictly increases a nonempty
finite Hessenberg sum. -/
theorem naturalSumList_strictMono {as bs : List Ordinal.{u}}
    (h : List.Forall₂ (· < ·) as bs) (hne : as ≠ []) :
    naturalSumList as < naturalSumList bs := by
  induction h with
  | nil => exact False.elim (hne rfl)
  | @cons a b as bs hab htail ih =>
    have hweak : List.Forall₂ (· ≤ ·) as bs :=
      htail.imp (fun _ _ h => h.le)
    exact (naturalSum_lt_left hab).trans_le
      (naturalSum_mono_right (naturalSumList_mono hweak))

/-- A pointwise strict increase of positive factors strictly increases a
nonempty finite Hessenberg product. -/
theorem naturalProductList_strictMono {as bs : List Ordinal.{u}}
    (h : List.Forall₂ (· < ·) as bs) (hne : as ≠ [])
    (hp : ∀ b ∈ bs, 0 < b) :
    naturalProductList as < naturalProductList bs := by
  induction h with
  | nil => exact False.elim (hne rfl)
  | @cons a b as bs hab htail ih =>
    have hweak : List.Forall₂ (· ≤ ·) as bs :=
      htail.imp (fun _ _ h => h.le)
    have ht : 0 < naturalProductList bs :=
      (naturalProductList_pos_iff bs).2
        (fun x hx => hp x (List.mem_cons_of_mem b hx))
    exact (naturalProduct_mono_right (a := a) (naturalProductList_mono hweak)).trans_lt
      (naturalProduct_lt_left hab ht)

end LeanCategories.ForMathlib.OrdinalNatural
