/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CyclicOperators
public import LeanCategories.Homological.DoubleComplexFiltrations

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

/-- A source-faithful realization of Tsygan's first-quadrant bicomplex. -/
structure TsyganBicomplexRealization (A : CyclicObject (C := C)) where
  /-- The realized first-quadrant bicomplex. -/
  bicomplex : FirstQuadrantDoubleComplex C
  /-- Every bidegree `(p,q)` is a copy of `A_q`. -/
  degreeIso : ∀ (p q : ℕ), (bicomplex.X p).X q ≅ A.obj.obj (op ⦋q⦌)
  /-- Even columns carry the Hochschild differential `b`. -/
  vertical_even : ∀ (r q : ℕ),
    (degreeIso (2 * r) (q + 1)).hom ≫
        (cyclicHochschildComplex A).d (q + 1) q =
      (bicomplex.X (2 * r)).d (q + 1) q ≫ (degreeIso (2 * r) q).hom
  /-- Odd columns carry the companion differential `b'`. -/
  vertical_odd : ∀ (r q : ℕ),
    (degreeIso (2 * r + 1) (q + 1)).hom ≫
        cyclicCompanionDifferential A q =
      (bicomplex.X (2 * r + 1)).d (q + 1) q ≫
        (degreeIso (2 * r + 1) q).hom
  /-- From an odd column to the preceding even column, the horizontal map is
  `1-(-1)^q t_q`. -/
  horizontal_difference : ∀ (r q : ℕ),
    (degreeIso (2 * r + 1) q).hom ≫ cyclicSignedDifference A q =
      (bicomplex.d (2 * r + 1) (2 * r)).f q ≫
        (degreeIso (2 * r) q).hom
  /-- From a positive even column to the preceding odd column, the horizontal
  map is the norm `N_q`. -/
  horizontal_norm : ∀ (r q : ℕ),
    (degreeIso (2 * r + 2) q).hom ≫ cyclicNorm A q =
      (bicomplex.d (2 * r + 2) (2 * r + 1)).f q ≫
        (degreeIso (2 * r + 1) q).hom

/-- The direct-sum total complex defining cyclic homology. -/
def tsyganTotalComplex (A : CyclicObject (C := C))
    (T : TsyganBicomplexRealization A)
    [HomologicalComplex₂.HasTotal T.bicomplex (ComplexShape.down ℕ)] :
    ChainComplex C ℕ :=
  HomologicalComplex₂.total T.bicomplex (ComplexShape.down ℕ)

/-- Weibel's cyclic homology `HC_n(A)=H_n Tot(CC_{**}(A))`. -/
def cyclicHomology (A : CyclicObject (C := C))
    (T : TsyganBicomplexRealization A)
    [HomologicalComplex₂.HasTotal T.bicomplex (ComplexShape.down ℕ)]
    (n : ℕ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).obj
    (tsyganTotalComplex A T)

end LeanCategories.Homological
