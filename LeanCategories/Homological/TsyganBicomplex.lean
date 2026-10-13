/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CyclicOperators

/-!
# Tsygan's cyclic bicomplex

Weibel, *An Introduction to Homological Algebra* (1994), Definitions 9.6.6
and 9.6.7, pp. 330--337 (FC05-C09-U087, FC05-C09-U088).

For a cyclic object `A`, Tsygan's first-quadrant bicomplex has a copy of
`A_q` in every bidegree `(p,q)`.  Even columns use the Hochschild
differential `b`, odd columns use `b'`, and the horizontal maps alternate
between `1-(-1)^q t_q` and the norm `N_q`.

The bicomplex identities are theorem-layer consequences of the cyclic
identities; the Definitions sweep packages a realization of the displayed
formulas and defines cyclic homology as the homology of its direct-sum total
complex.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The signed cyclic difference `1-(-1)^q t_q` occurring in row `q` of
Tsygan's bicomplex. -/
def cyclicSignedDifference (A : CyclicObject (C := C)) (q : ℕ) :
    A.obj.obj (op ⦋q⦌) ⟶ A.obj.obj (op ⦋q⦌) :=
  𝟙 _ - ((-1 : ℤ) ^ q) • (A.t q).hom

end LeanCategories.Homological
