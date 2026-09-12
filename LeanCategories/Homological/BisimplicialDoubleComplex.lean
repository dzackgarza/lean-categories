/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DoubleComplexFirstPages
public import LeanCategories.Homological.SimplicialChainComplexes

/-!
# The double complex of a bisimplicial object

Weibel, *An Introduction to Homological Algebra* (1994), §8.5, p. 275
(FC05-C08-U051).

For a bisimplicial object `A`, Weibel defines the unnormalized first-quadrant
double complex `C(A)` by

* `C(A)_{p,q}=A_{p,q}`;
* `dʰ = ∑ᵢ (-1)^i ∂ᵢʰ`;
* `dᵛ = (-1)^p ∑ⱼ (-1)^j ∂ⱼᵛ` in horizontal degree `p`.

The factor `(-1)^p` is Weibel's sign trick 1.2.5, converting the commuting
horizontal/vertical simplicial operators into anticommuting double-complex
differentials.

Mathlib represents a bicomplex as a chain complex *of* chain complexes.  In
that representation the inner vertical differential is stored without the
`(-1)^p` factor so that the outer differential is a chain map; the standard
totalization sign reinstates that factor.  `bisimplicialWeibelVertical` below
records Weibel's signed vertical arrow explicitly.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The nested-complex realization of the unnormalized double complex attached
to a bisimplicial object.  The outer direction is horizontal and the inner
direction is vertical. -/
def bisimplicialDoubleComplex
    (A : SimplicialObject (SimplicialObject C)) : FirstQuadrantDoubleComplex C :=
  ((AlgebraicTopology.alternatingFaceMapComplex C).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
    (AlgebraicTopology.AlternatingFaceMapComplex.obj A)

@[simp]
lemma bisimplicialDoubleComplex_X
    (A : SimplicialObject (SimplicialObject C)) (p q : ℕ) :
    ((bisimplicialDoubleComplex A).X p).X q =
      (A.obj (op ⦋p⦌)).obj (op ⦋q⦌) :=
  rfl

/-- The horizontal differential is the alternating sum of horizontal face
maps, evaluated in fixed vertical degree `q`. -/
lemma bisimplicialDoubleComplex_horizontal
    (A : SimplicialObject (SimplicialObject C)) (p q : ℕ) :
    ((bisimplicialDoubleComplex A).d (p + 1) p).f q =
      ∑ i : Fin (p + 2),
        (-1 : ℤ) ^ (i : ℕ) • (A.δ i).app (op ⦋q⦌) := by
  change
    (((AlgebraicTopology.alternatingFaceMapComplex C).map
      ((AlgebraicTopology.AlternatingFaceMapComplex.obj A).d (p + 1) p)).f q) = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Functor.map_sum]
  change
    (HomologicalComplex.Hom.fAddMonoidHom q)
      (∑ i : Fin (p + 2),
        (AlgebraicTopology.alternatingFaceMapComplex C).map
          ((-1 : ℤ) ^ (i : ℕ) • A.δ i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Functor.map_zsmul, map_zsmul]
  change
    (-1 : ℤ) ^ (i : ℕ) •
      (((AlgebraicTopology.alternatingFaceMapComplex C).map (A.δ i)).f q) = _
  rw [AlgebraicTopology.alternatingFaceMapComplex_map_f]

/-- The inner differential stored by the nested-complex representation is the
unsigned vertical alternating-face differential. -/
lemma bisimplicialDoubleComplex_vertical_raw
    (A : SimplicialObject (SimplicialObject C)) (p q : ℕ) :
    ((bisimplicialDoubleComplex A).X p).d (q + 1) q =
      ∑ j : Fin (q + 2),
        (-1 : ℤ) ^ (j : ℕ) • (A.obj (op ⦋p⦌)).δ j := by
  change
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (A.obj (op ⦋p⦌))).d
        (q + 1) q = _
  exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq
    (A.obj (op ⦋p⦌)) q

/-- Weibel's signed vertical double-complex arrow
`dᵛ_{p,q}=(-1)^p Σ_j(-1)^j ∂ⱼᵛ`. -/
def bisimplicialWeibelVertical
    (A : SimplicialObject (SimplicialObject C)) (p q : ℕ) :
    (A.obj (op ⦋p⦌)).obj (op ⦋q + 1⦌) ⟶
      (A.obj (op ⦋p⦌)).obj (op ⦋q⦌) :=
  (-1 : ℤ) ^ p • ((bisimplicialDoubleComplex A).X p).d (q + 1) q

lemma bisimplicialWeibelVertical_eq
    (A : SimplicialObject (SimplicialObject C)) (p q : ℕ) :
    bisimplicialWeibelVertical A p q =
      (-1 : ℤ) ^ p •
        (∑ j : Fin (q + 2),
          (-1 : ℤ) ^ (j : ℕ) • (A.obj (op ⦋p⦌)).δ j) := by
  rw [bisimplicialWeibelVertical, bisimplicialDoubleComplex_vertical_raw]
  rfl

end LeanCategories.Homological
