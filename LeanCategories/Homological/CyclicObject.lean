/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Cyclic objects

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.6.1,
pp. 330--337 (FC05-C09-U082).

The convention agrees with Weibel's rotation of the last coordinate to the front.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial

universe v u

variable {C : Type u} [Category.{v} C]

/-- Iterated categorical composition of an endomorphism. -/
def endPow {X : C} (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => endPow f n ≫ f

/-- A cyclic object: a simplicial object with degreewise cyclic operators satisfying
the standard order, face, and degeneracy identities. -/
structure CyclicObject where
  /-- Underlying simplicial object. -/
  obj : SimplicialObject C
  /-- Cyclic operator in every degree. -/
  t : ∀ n : ℕ, obj.obj (op ⦋n⦌) ≅ obj.obj (op ⦋n⦌)
  /-- `t_n` has order dividing `n+1`. -/
  order : ∀ n : ℕ, endPow (t n).hom (n + 1) = 𝟙 _
  /-- `d₀ t_n = d_n`. -/
  face_zero : ∀ n : ℕ,
    (t (n + 1)).hom ≫ obj.δ (0 : Fin (n + 2)) = obj.δ (Fin.last (n + 1))
  /-- `d_i t_n = t_{n-1} d_{i-1}` for `i>0`. -/
  face_succ : ∀ (n : ℕ) (i : Fin (n + 1)),
    (t (n + 1)).hom ≫ obj.δ i.succ = obj.δ i.castSucc ≫ (t n).hom
  /-- `s₀ t_n = t_{n+1}² s_n`. -/
  degeneracy_zero : ∀ n : ℕ,
    (t n).hom ≫ obj.σ (0 : Fin (n + 1)) =
      obj.σ (Fin.last n) ≫ (t (n + 1)).hom ≫ (t (n + 1)).hom
  /-- `s_i t_n = t_{n+1} s_{i-1}` for `i>0`. -/
  degeneracy_succ : ∀ (n : ℕ) (i : Fin n),
    (t n).hom ≫ obj.σ i.succ = obj.σ i.castSucc ≫ (t (n + 1)).hom

end LeanCategories.Homological
