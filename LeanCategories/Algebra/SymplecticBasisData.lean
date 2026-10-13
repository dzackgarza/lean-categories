/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Symplectic-basis data

Definition-level realization of Lee FC08-C22-U009.  The source calls a basis
`(A₁, B₁, ..., Aₙ, Bₙ)` symplectic when its pairings have the standard
symplectic matrix.  The canonical-form theorem asserting existence of such a
basis is result content and is not included here.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

/-- Lee's symplectic-basis predicate, with the basis indexed by an `A` copy
and a `B` copy of `Fin n`. -/
def IsSymplecticBasis {V : Type u} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (ω : LinearMap.BilinForm ℝ V)
    (b : Module.Basis (Sum (Fin n) (Fin n)) ℝ V) : Prop :=
  (∀ i j, ω (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
    (∀ i j, ω (b (Sum.inr i)) (b (Sum.inr j)) = 0) ∧
    (∀ i j, ω (b (Sum.inl i)) (b (Sum.inr j)) =
      if i = j then 1 else 0) ∧
    (∀ i j, ω (b (Sum.inr i)) (b (Sum.inl j)) =
      if i = j then -1 else 0)

end LeanCategories.Algebra
