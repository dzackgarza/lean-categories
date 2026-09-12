/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DoubleComplexFirstPages
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

/-- A source-faithful realization of Connes' double complex obtained from a
cyclic object by eliminating the odd acyclic columns of Tsygan's bicomplex.

The bidegree `(p,q)` term is `A_{q-p}` for `p ≤ q`, the vertical differential
is the Hochschild differential `b`, and the horizontal differential is the
operator `B` above. -/
structure CyclicConnesDoubleComplexRealization (A : CyclicObject (C := C)) where
  /-- The first-quadrant double complex. -/
  bicomplex : FirstQuadrantDoubleComplex C
  /-- On and below the diagonal, bidegree `(p,q)` is `A_{q-p}`. -/
  nonzeroIso : ∀ (p q : ℕ), p ≤ q →
    CategoryTheory.Iso ((bicomplex.X p).X q) (A.obj.obj (op ⦋q - p⦌))
  /-- Above the diagonal the entries vanish. -/
  zeroAbove : ∀ (p q : ℕ), q < p → IsZero ((bicomplex.X p).X q)
  /-- The vertical differential is the Hochschild differential `b`. -/
  vertical : ∀ (p q : ℕ) (hpq : p ≤ q),
    (nonzeroIso p (q + 1) (by omega)).hom ≫
        (cyclicHochschildComplex A).d (q + 1 - p) (q - p) =
      (bicomplex.X p).d (q + 1) q ≫ (nonzeroIso p q hpq).hom
  /-- The horizontal differential is Connes' operator `B`. -/
  horizontal : ∀ (p q : ℕ) (hpq : p + 1 ≤ q),
    (nonzeroIso (p + 1) q hpq).hom ≫ connesOperator A (q - (p + 1)) ≫
        eqToHom
          (congrArg (fun n : ℕ => A.obj.obj (op ⦋n⦌))
            (show q - (p + 1) + 1 = q - p by omega)) =
      (bicomplex.d (p + 1) p).f q ≫
        (nonzeroIso p q (by omega)).hom

/-- The two identities in Weibel's calculation that make Connes' operator
`B` into the degree-raising differential of a mixed complex.  The equation
`b²=0` is already part of `cyclicHochschildComplex A`. -/
structure CyclicMixedComplexIdentities (A : CyclicObject (C := C)) where
  /-- `B²=0`. -/
  B_sq : ∀ n : ℕ, connesOperator A n ≫ connesOperator A (n + 1) = 0
  /-- The degree-zero instance of `bB+Bb=0`. -/
  mixed_zero :
    connesOperator A 0 ≫ cyclicHochschildBoundary A 0 = 0
  /-- `bB+Bb=0` in every positive degree. -/
  mixed_succ : ∀ n : ℕ,
    cyclicHochschildBoundary A n ≫ connesOperator A n +
      connesOperator A (n + 1) ≫
        cyclicHochschildBoundary A (n + 1) = 0

/-- The mixed complex `(A,b,B)` associated to a cyclic object once the
source calculation of `B²=0` and `bB+Bb=0` has been supplied.

This is exactly Weibel's construction immediately following Definition 9.8.1
(FC05-C09-U114): the chain differential is the Hochschild differential `b`
and the degree-raising operator is the source-defined `connesOperator`. -/
def cyclicMixedComplex (A : CyclicObject (C := C))
    (h : CyclicMixedComplexIdentities A) : MixedComplex C where
  chain := cyclicHochschildComplex A
  B := connesOperator A
  B_sq := h.B_sq
  mixed_zero := by
    rw [cyclicHochschildComplex_d]
    exact h.mixed_zero
  mixed_succ := fun n => by
    rw [cyclicHochschildComplex_d, cyclicHochschildComplex_d]
    exact h.mixed_succ n

end LeanCategories.Homological
