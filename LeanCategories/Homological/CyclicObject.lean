/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Data.Fin.Tuple.Basic

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

/-! ## The group examples of 9.6.2: construction data

Sweep III records only the degreewise sets and displayed operators from Weibel's
Example 9.6.2. Showing that these operators satisfy the simplicial/cyclic
identities, assembling them into `CyclicObject`s, and identifying the free
linearization of `ZG` with the cyclic module of the group algebra are result
clauses and are deliberately not part of these definitions.
-/

section GroupCyclicSetData

variable (G : Type*) [Group G]

/-- Degree `n` of Weibel's cyclic set `ZG`: an `(n+1)`-tuple of group elements. -/
abbrev groupCyclicDegree (n : ℕ) := Fin (n + 1) → G

/-- Degree `n` of the classifying simplicial set `BG`: an `n`-tuple of group elements. -/
abbrev groupClassifyingDegree (n : ℕ) := Fin n → G

/-- The ordered product of a finite tuple. The order matters for noncommutative groups. -/
def groupTupleProduct {n : ℕ} (g : Fin n → G) : G :=
  (List.ofFn g).prod

/-- The adjacent face of `ZG`, multiplying entries `i` and `i+1` and deleting the latter. -/
def groupCyclicAdjacentFace {n : ℕ} (i : Fin (n + 1))
    (g : groupCyclicDegree G (n + 1)) : groupCyclicDegree G n :=
  Fin.removeNth i.succ
    (Function.update g i.castSucc (g i.castSucc * g i.succ))

/-- The last face of `ZG`,
`(g₀,…,gₙ₊₁) ↦ (gₙ₊₁g₀,g₁,…,gₙ)`. -/
def groupCyclicLastFace {n : ℕ}
    (g : groupCyclicDegree G (n + 1)) : groupCyclicDegree G n :=
  Fin.cons (g (Fin.last (n + 1)) * g 0) (fun i : Fin n => g i.succ.castSucc)

/-- The displayed face data of `ZG`: adjacent multiplication except at the last face. -/
def groupCyclicFace {n : ℕ} (i : Fin (n + 2))
    (g : groupCyclicDegree G (n + 1)) : groupCyclicDegree G n :=
  Fin.lastCases (groupCyclicLastFace G g)
    (fun j => groupCyclicAdjacentFace G j g) i

/-- The displayed degeneracy of `ZG`, inserting the identity immediately after entry `i`. -/
def groupCyclicDegeneracy {n : ℕ} (i : Fin (n + 1))
    (g : groupCyclicDegree G n) : groupCyclicDegree G (n + 1) :=
  Fin.insertNth i.succ 1 g

/-- The displayed cyclic rotation of `ZG`, moving the last entry to the front. -/
def groupCyclicRotate {n : ℕ}
    (g : groupCyclicDegree G n) : groupCyclicDegree G n :=
  Fin.cons (g (Fin.last n)) (Fin.init g)

/-- The displayed cyclic rotation on `BG`.
In positive degree it sends
`(g₁,…,gₙ)` to `((g₁⋯gₙ)⁻¹,g₁,…,gₙ₋₁)`; degree zero is the unique endomap. -/
def groupClassifyingRotate :
    (n : ℕ) → groupClassifyingDegree G n → groupClassifyingDegree G n
  | 0 => id
  | _n + 1 => fun g =>
      Fin.cons (groupTupleProduct G g)⁻¹ (Fin.init g)

/-- The degreewise map `BG → ZG` from Example 9.6.2, obtained by prepending the
inverse ordered product. -/
def groupClassifyingToCyclic {n : ℕ}
    (g : groupClassifyingDegree G n) : groupCyclicDegree G n :=
  Fin.cons (groupTupleProduct G g)⁻¹ g

end GroupCyclicSetData

end LeanCategories.Homological
