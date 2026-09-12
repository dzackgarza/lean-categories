/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.TsyganBicomplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Periodic and negative cyclic homology

Weibel, *An Introduction to Homological Algebra* (1994), §9.6.1,
Definition/construction 9.6.17, pp. 337--338 (FC05-C09-U099).

Weibel extends Tsygan's first-quadrant bicomplex two-periodically to the left,
forming an upper-half-plane bicomplex.  Periodic cyclic homology is the
homology of its **product** total complex.  The nonpositive-column subcomplex
is a second-quadrant bicomplex; the homology of its product total complex is
negative cyclic homology.  Translation by two columns gives the period-two
isomorphism on periodic cyclic homology.

The structures below record exactly these definition-layer realizations.  In
particular, they use products rather than the coproduct totalization used for
ordinary cyclic homology.  The inverse-limit exact sequence and the SBI exact
sequence for `HN → HP` following 9.6.17 are result-level statements and are
not asserted here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A source-faithful realization of the two-sided periodic extension of
Tsygan's bicomplex.  Columns are indexed by `ℤ`, while rows remain indexed by
`ℕ`; every column is a copy of the corresponding Hochschild degree, with the
same alternating `b/b'` and `1-(-1)^q t/N` pattern as in Weibel 9.6.6. -/
structure PeriodicTsyganBicomplexRealization (A : CyclicObject (C := C)) where
  /-- The upper-half-plane bicomplex, extended indefinitely to the left. -/
  bicomplex : ChainComplex (ChainComplex C ℕ) ℤ
  /-- Every bidegree `(p,q)` is a copy of `A_q`. -/
  degreeIso : ∀ (p : ℤ) (q : ℕ), (bicomplex.X p).X q ≅ A.obj.obj (op ⦋q⦌)
  /-- Even columns carry the Hochschild differential `b`. -/
  vertical_even : ∀ (r : ℤ) (q : ℕ),
    (degreeIso (2 * r) (q + 1)).hom ≫
        (cyclicHochschildComplex A).d (q + 1) q =
      (bicomplex.X (2 * r)).d (q + 1) q ≫ (degreeIso (2 * r) q).hom
  /-- Odd columns carry the companion differential `b'`. -/
  vertical_odd : ∀ (r : ℤ) (q : ℕ),
    (degreeIso (2 * r + 1) (q + 1)).hom ≫
        cyclicCompanionDifferential A q =
      (bicomplex.X (2 * r + 1)).d (q + 1) q ≫
        (degreeIso (2 * r + 1) q).hom
  /-- From an odd column to the preceding even column the horizontal map is
  `1-(-1)^q t_q`. -/
  horizontal_difference : ∀ (r : ℤ) (q : ℕ),
    (degreeIso (2 * r + 1) q).hom ≫ cyclicSignedDifference A q =
      (bicomplex.d (2 * r + 1) (2 * r)).f q ≫
        (degreeIso (2 * r) q).hom
  /-- From an even column to the preceding odd column the horizontal map is
  the norm `N_q`. -/
  horizontal_norm : ∀ (r : ℤ) (q : ℕ),
    (degreeIso (2 * r + 2) q).hom ≫ cyclicNorm A q =
      (bicomplex.d (2 * r + 2) (2 * r + 1)).f q ≫
        (degreeIso (2 * r + 1) q).hom

/-- Bidegrees contributing to total degree `n` in Weibel's product
totalization of the periodic upper-half-plane bicomplex. -/
abbrev PeriodicCyclicTotalIndex (n : ℤ) :=
  {pq : ℤ × ℕ // pq.1 + (pq.2 : ℤ) = n}

/-- Bidegrees contributing to total degree `n` in the nonpositive-column
subcomplex defining negative cyclic homology. -/
abbrev NegativeCyclicTotalIndex (n : ℤ) :=
  {pq : ℤ × ℕ // pq.1 ≤ 0 ∧ pq.1 + (pq.2 : ℤ) = n}

/-- The horizontal source bidegree contributing to the differential into a
fixed bidegree of total degree `n-1`. -/
def periodicCyclicHorizontalSource {n : ℤ}
    (i : PeriodicCyclicTotalIndex (n - 1)) : PeriodicCyclicTotalIndex n :=
  ⟨(i.1.1 + 1, i.1.2), by omega⟩

/-- The vertical source bidegree contributing to the differential into a
fixed bidegree of total degree `n-1`. -/
def periodicCyclicVerticalSource {n : ℤ}
    (i : PeriodicCyclicTotalIndex (n - 1)) : PeriodicCyclicTotalIndex n :=
  ⟨(i.1.1, i.1.2 + 1), by omega⟩

/-- Regard a periodic-total bidegree in a nonpositive column as a negative-
cyclic-total bidegree. -/
def negativeCyclicIndexOfPeriodic {n : ℤ}
    (i : PeriodicCyclicTotalIndex n) (h : i.1.1 ≤ 0) :
    NegativeCyclicTotalIndex n :=
  ⟨i.1, ⟨h, i.2⟩⟩

/-- The usual total-complex sign on the vertical differential in column `p`.
For negative columns `(-1)^p=(-1)^{|p|}`, so `natAbs` gives the same parity
without requiring an integer-power operation on `ℤ`. -/
def periodicTotalVerticalSign (p : ℤ) : ℤ :=
  (-1 : ℤ) ^ p.natAbs

/-- The degree-`n` product object for the periodic total complex. -/
def periodicCyclicProductDegree
    [HasProducts.{0} C]
    {A : CyclicObject (C := C)}
    (P : PeriodicTsyganBicomplexRealization A) (n : ℤ) : C :=
  ∏ᶜ fun i : PeriodicCyclicTotalIndex n =>
    (P.bicomplex.X i.1.1).X i.1.2

/-- The degree-`n` product object for the negative cyclic total complex. -/
def negativeCyclicProductDegree
    [HasProducts.{0} C]
    {A : CyclicObject (C := C)}
    (P : PeriodicTsyganBicomplexRealization A) (n : ℤ) : C :=
  ∏ᶜ fun i : NegativeCyclicTotalIndex n =>
    (P.bicomplex.X i.1.1).X i.1.2

/-- A realization of Weibel's product totalizations defining periodic and
negative cyclic homology.  The degree isomorphisms record the product, rather
than coproduct, convention explicitly. -/
structure PeriodicCyclicRealization
    [HasProducts.{0} C]
    (A : CyclicObject (C := C)) where
  /-- The two-sided periodic extension of Tsygan's bicomplex. -/
  periodicBicomplex : PeriodicTsyganBicomplexRealization A
  /-- The product total complex of the periodic upper-half-plane bicomplex. -/
  periodicTotal : ChainComplex C ℤ
  /-- Its degree `n` is the product over all bidegrees of total degree `n`. -/
  periodicDegreeIso : ∀ n : ℤ,
    periodicTotal.X n ≅ periodicCyclicProductDegree periodicBicomplex n
  /-- The product-total differential is the sum of the horizontal differential
  and the signed vertical differential on every target projection. -/
  periodicDifferential : ∀ (n : ℤ)
      (i : PeriodicCyclicTotalIndex (n - 1)),
    periodicTotal.d n (n - 1) ≫ (periodicDegreeIso (n - 1)).hom ≫
        Limits.Pi.π
          (fun j : PeriodicCyclicTotalIndex (n - 1) =>
            (periodicBicomplex.bicomplex.X j.1.1).X j.1.2) i =
      (periodicDegreeIso n).hom ≫
          Limits.Pi.π
            (fun j : PeriodicCyclicTotalIndex n =>
              (periodicBicomplex.bicomplex.X j.1.1).X j.1.2)
            (periodicCyclicHorizontalSource i) ≫
          (periodicBicomplex.bicomplex.d (i.1.1 + 1) i.1.1).f i.1.2 +
        periodicTotalVerticalSign i.1.1 •
          ((periodicDegreeIso n).hom ≫
            Limits.Pi.π
              (fun j : PeriodicCyclicTotalIndex n =>
                (periodicBicomplex.bicomplex.X j.1.1).X j.1.2)
              (periodicCyclicVerticalSource i) ≫
            (periodicBicomplex.bicomplex.X i.1.1).d (i.1.2 + 1) i.1.2)
  /-- The product total complex of the nonpositive-column subcomplex. -/
  negativeTotal : ChainComplex C ℤ
  /-- Its degree `n` is the product over bidegrees with column index `p ≤ 0`. -/
  negativeDegreeIso : ∀ n : ℤ,
    negativeTotal.X n ≅ negativeCyclicProductDegree periodicBicomplex n
  /-- Inclusion of the nonpositive-column product total complex into the
  periodic product total complex. -/
  negativeToPeriodic : negativeTotal ⟶ periodicTotal
  /-- On product coordinates, `negativeToPeriodic` is the evident inclusion:
  retain nonpositive columns and use zero on positive columns. -/
  negativeToPeriodic_projection : ∀ (n : ℤ)
      (i : PeriodicCyclicTotalIndex n),
    negativeToPeriodic.f n ≫ (periodicDegreeIso n).hom ≫
        Limits.Pi.π
          (fun j : PeriodicCyclicTotalIndex n =>
            (periodicBicomplex.bicomplex.X j.1.1).X j.1.2) i =
      if h : i.1.1 ≤ 0 then
        (negativeDegreeIso n).hom ≫
          Limits.Pi.π
            (fun j : NegativeCyclicTotalIndex n =>
              (periodicBicomplex.bicomplex.X j.1.1).X j.1.2)
            (negativeCyclicIndexOfPeriodic i h)
      else 0
  /-- Translation by two columns induces Weibel's period-two `S`
  isomorphism on homology. -/
  periodicity : ∀ n : ℤ,
    (HomologicalComplex.homologyFunctor C (ComplexShape.down ℤ) (n + 2)).obj
        periodicTotal ≅
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℤ) n).obj
        periodicTotal

/-- Periodic cyclic homology `HP_n(A)`, defined from the product total complex
of the two-sided periodic extension. -/
def periodicCyclicHomology
    [HasProducts.{0} C]
    {A : CyclicObject (C := C)}
    (P : PeriodicCyclicRealization A) (n : ℤ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.down ℤ) n).obj
    P.periodicTotal

/-- Negative cyclic homology `HN_n(A)`, defined from the product total complex
of the nonpositive-column subcomplex. -/
def negativeCyclicHomology
    [HasProducts.{0} C]
    {A : CyclicObject (C := C)}
    (P : PeriodicCyclicRealization A) (n : ℤ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.down ℤ) n).obj
    P.negativeTotal

end LeanCategories.Homological
