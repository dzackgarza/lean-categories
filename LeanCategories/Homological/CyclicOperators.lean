/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CyclicObject
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# Chain operators attached to a cyclic object

Weibel, *An Introduction to Homological Algebra* (1994), Definitions 9.6.5,
pp. 330--337 (FC05-C09-U086).
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The Hochschild chain complex of a cyclic object: the alternating-face-map
complex of its underlying simplicial object. -/
noncomputable def cyclicHochschildComplex (A : CyclicObject (C := C)) : ChainComplex C ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj A.obj

/-- Weibel's companion differential `b'` in degree `n+1 → n`, obtained by
omitting the last face from the ordinary Hochschild differential. -/
noncomputable def cyclicCompanionDifferential (A : CyclicObject (C := C)) (n : ℕ) :
    A.obj.obj (op ⦋n + 1⦌) ⟶ A.obj.obj (op ⦋n⦌) :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • A.obj.δ i.castSucc

/-- The degree-`n` norm `N = 1 + t + ⋯ + t^n`. -/
noncomputable def cyclicNorm (A : CyclicObject (C := C)) (n : ℕ) :
    A.obj.obj (op ⦋n⦌) ⟶ A.obj.obj (op ⦋n⦌) :=
  ∑ i : Fin (n + 1), endPow (A.t n).hom (i : ℕ)

end LeanCategories.Homological
