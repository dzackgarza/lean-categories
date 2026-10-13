/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import LeanCategories.Homological.CyclicOperators
public import LeanCategories.Homological.MixedComplex

/-!
# Connes' operator attached to a cyclic object

Weibel, *An Introduction to Homological Algebra* (1994), §9.8,
pp. 344--345 (FC05-C09-U112).

For a cyclic object `A`, Weibel fixes the contraction
`s_n = σ_n ≫ t_{n+1}` of the companion Hochschild complex and defines

`B_n = N_n ≫ s_n ≫ (1 + (-1)^n t_{n+1})`.

Eliminating the odd acyclic columns of Tsygan's bicomplex gives Connes'
first-quadrant double complex with vertical differential `b` and horizontal
differential `B`.  This file records the formula and the corresponding
definition-layer double-complex realization.  The calculation that packages
`(A,b,B)` as a mixed complex is FC05-C09-U114; the comparison of its cyclic
homology with `HC_*(A)` is Proposition 9.8.3 and remains theorem-layer work.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Weibel's contraction `s_n = t a_n` of the companion Hochschild complex:
the last simplicial degeneracy followed by the cyclic operator in degree
`n+1`. -/
def connesContraction (A : CyclicObject (C := C)) (n : ℕ) :
    A.obj.obj (op ⦋n⦌) ⟶ A.obj.obj (op ⦋n + 1⦌) :=
  A.obj.σ (Fin.last n) ≫ (A.t (n + 1)).hom

/-- Connes' operator
`B_n = N_n s_n (1 + (-1)^n t_{n+1}) : A_n ⟶ A_{n+1}`
in categorical composition order. -/
def connesOperator (A : CyclicObject (C := C)) (n : ℕ) :
    A.obj.obj (op ⦋n⦌) ⟶ A.obj.obj (op ⦋n + 1⦌) :=
  cyclicNorm A n ≫ connesContraction A n ≫
    (𝟙 _ + ((-1 : ℤ) ^ n) • (A.t (n + 1)).hom)

/-- The Hochschild boundary `b = d₀-d₁+⋯+(-1)^{n+1}d_{n+1}` with its
source and target displayed directly as the degree objects of the cyclic
object. -/
def cyclicHochschildBoundary (A : CyclicObject (C := C)) (n : ℕ) :
    A.obj.obj (op ⦋n + 1⦌) ⟶ A.obj.obj (op ⦋n⦌) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • A.obj.δ i

lemma cyclicHochschildComplex_d (A : CyclicObject (C := C)) (n : ℕ) :
    (cyclicHochschildComplex A).d (n + 1) n = cyclicHochschildBoundary A n := by
  exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq A.obj n

end LeanCategories.Homological
