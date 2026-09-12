/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.HochschildShuffleElements
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Eulerian idempotents

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.4.12,
p. 325 (FC05-C09-U069).

The shuffle operator `s_n` has eigenvalues `λ_i=2^i-2`, `1≤i≤n`.
The Eulerian idempotent `e_n^(i)` is the corresponding Lagrange projector in
`ℚΣ_n`.  Weibel sets `e_0^(0)=1`, `e_n^(0)=0` for `n>0`, and
`e_n^(i)=0` for `i>n`.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open scoped BigOperators

/-- The shuffle eigenvalue `λ_i=2^i-2`. -/
def eulerianEigenvalue (i : ℕ) : ℚ :=
  (2 : ℚ) ^ i - 2

/-- The integral total shuffle element viewed in `ℚΣ_n`. -/
noncomputable def rationalTotalShuffleElement (n : ℕ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin n)) :=
  MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Int.castRingHom ℚ)
    (totalShuffleElement n)

/-- One Lagrange factor
`(λ_i-λ_j)⁻¹ (s_n-λ_j)` in `ℚΣ_n`. -/
noncomputable def eulerianLagrangeFactor (n i j : ℕ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin n)) :=
  MonoidAlgebra.single 1 ((eulerianEigenvalue i - eulerianEigenvalue j)⁻¹) *
    (rationalTotalShuffleElement n -
      MonoidAlgebra.single 1 (eulerianEigenvalue j))

/-- Ordered multiplication, used because `ℚΣ_n` is not a commutative ring. -/
def orderedProduct {A : Type*} [Monoid A] (xs : List A) : A :=
  xs.foldl (· * ·) 1

/-- Weibel's Eulerian idempotent `e_n^(i)`.

For `1≤i≤n`, this is the Lagrange projector
`∏_{1≤j≤n,j≠i}(λ_i-λ_j)⁻¹(s_n-λ_j)`. -/
noncomputable def eulerianIdempotent (n i : ℕ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin n)) := by
  classical
  by_cases hn : n = 0
  · subst n
    exact if i = 0 then 1 else 0
  by_cases hi0 : i = 0
  · exact 0
  by_cases hin : i ≤ n
  · exact orderedProduct <|
      ((Finset.range n).filter (fun j => j + 1 ≠ i)).toList.map
        (fun j => eulerianLagrangeFactor n i (j + 1))
  · exact 0

end LeanCategories.Homological
