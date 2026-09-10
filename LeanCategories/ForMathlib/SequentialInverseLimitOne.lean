/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The first derived inverse limit of a sequential inverse system

Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), printed p. 104,
FC04-C10-U013. For a sequential inverse system `A₀ ← A₁ ← ...`, the source
defines `dᴬ : ∏ Aₙ → ∏ Aₙ` by `dᴬ(a)ₙ = aₙ - θₙ₊₁(aₙ₊₁)` and denotes its
cokernel by `lim¹ Aₙ`. The kernel is the ordinary coherent inverse limit.
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

/-- The source's `lim¹ A_n`, defined as the cokernel of its difference map. -/
abbrev limOne := (∀ n, A n) ⧸ (difference A θ).range

end SequentialInverseSystem
