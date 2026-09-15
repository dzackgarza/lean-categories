/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The first derived inverse limit of a sequential inverse system

Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), printed p. 104,
FC04-C10-U013, and Weibel, *An Introduction to Homological Algebra*, Definition 3.5.1,
FC05-C03-U046. For a sequential inverse system `A₀ ← A₁ ← ...`, the sources define
`dᴬ : ∏ Aₙ → ∏ Aₙ` by `dᴬ(a)ₙ = aₙ - θₙ₊₁(aₙ₊₁)` and denote its cokernel by
`lim¹ Aₙ`. The kernel is the ordinary coherent inverse limit. Weibel packages this as the
Eilenberg model for derived inverse limits, with all degrees at least two equal to zero.
-/

@[expose] public section

namespace SequentialInverseSystem

variable (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
variable (θ : ∀ n, A (n + 1) →+ A n)

/-- Atiyah--Macdonald's difference map `d^A` on the product of a sequential inverse system. -/
def difference : (∀ n, A n) →+ (∀ n, A n) where
  toFun a n := a n - θ n (a (n+1))
  map_zero' := by funext n; simp
  map_add' a b := by funext n; simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

@[simp] theorem difference_apply (a : ∀ n, A n) (n : ℕ) :
    difference A θ a n = a n - θ n (a (n+1)) := rfl

/-- The kernel of `d^A` is exactly the coherent inverse-limit families. -/
theorem mem_ker_difference_iff (a : ∀ n, A n) :
    a ∈ (difference A θ).ker ↔ ∀ n, θ n (a (n+1)) = a n := by
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h n
    have hn := congrFun h n
    change a n - θ n (a (n + 1)) = 0 at hn
    exact (sub_eq_zero.mp hn).symm
  · intro h
    funext n
    change a n - θ n (a (n + 1)) = 0
    exact sub_eq_zero.mpr (h n).symm

/-- The degree-zero term in Eilenberg's model: the kernel of the difference map. -/
abbrev limZero := (difference A θ).ker

theorem mem_limZero_iff (a : ∀ n, A n) :
    a ∈ limZero A θ ↔ ∀ n, θ n (a (n + 1)) = a n :=
  mem_ker_difference_iff A θ a

/-- The source's `lim¹ A_n`, defined as the cokernel of its difference map. -/
abbrev limOne := (∀ n, A n) ⧸ (difference A θ).range

/-- The zero group used for every Eilenberg-model degree at least two. -/
abbrev limHigher (_θ : ∀ n, A (n + 1) →+ A n) := (⊥ : AddSubgroup (∀ n, A n))

/-- Eilenberg's degree-indexed model for derived limits of a countable tower.

Degree zero is the coherent inverse limit, degree one is the cokernel of `difference`, and every
higher degree is the zero group. -/
def limNat (q : ℕ) : Type _ :=
  match q with
  | 0 => limZero A θ
  | 1 => limOne A θ
  | _ => limHigher A θ

instance (q : ℕ) : AddCommGroup (limNat A θ q) := by
  cases q with
  | zero =>
      change AddCommGroup (limZero A θ)
      infer_instance
  | succ q =>
      cases q with
      | zero =>
          change AddCommGroup (limOne A θ)
          infer_instance
      | succ q =>
          change AddCommGroup (limHigher A θ)
          infer_instance

@[simp] theorem limNat_zero : limNat A θ 0 = limZero A θ := rfl

@[simp] theorem limNat_one : limNat A θ 1 = limOne A θ := rfl

@[simp] theorem limNat_succ_succ (q : ℕ) :
    limNat A θ (q + 2) = limHigher A θ := by
  cases q <;> rfl

/-- Every Eilenberg-model term in degree at least two is the zero group. -/
theorem limNat_higher_subsingleton (q : ℕ) :
    Subsingleton (limNat A θ (q + 2)) := by
  rw [limNat_succ_succ]
  infer_instance

end SequentialInverseSystem
