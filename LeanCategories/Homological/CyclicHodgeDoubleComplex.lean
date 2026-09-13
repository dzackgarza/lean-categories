/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.ConnesDoubleComplex
public import LeanCategories.Homological.DoubleComplexFiltrations
public import LeanCategories.Homological.HochschildHodgeDecomposition

/-!
# Hodge pieces of Connes' double complex

Weibel, *An Introduction to Homological Algebra* (1994), §9.8, pp. 344--353
(FC05-C09-U130).

For a commutative `ℚ`-algebra `R`, the Eulerian Hodge idempotents split
Connes' double complex into Hodge sub-double-complexes.  In the subcomplex of
Hodge weight `i`, bidegree `(p,q)` is

`C^h_{q-p}(R)^(i-p)`

when `p ≤ q` and `p ≤ i`, and is zero otherwise.  The identity
`e_{n+1}^{(j+1)} B = B e_n^j` is what makes the horizontal Connes operator
preserve this indexing; that compatibility is theorem-layer content.  The
structure below records the resulting definition-layer realization without
asserting that theorem.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe u


variable (R : Type u) [CommRing R] [Algebra ℚ R]

/-- A realization of the `i`th Hodge sub-double-complex of Connes' double
complex.

Source: Weibel, §9.8 immediately before Definition 9.8.14
(FC05-C09-U130). -/
structure HodgeConnesDoubleComplexRealization (i : ℕ) where
  /-- The realized first-quadrant Hodge sub-double-complex. -/
  bicomplex : FirstQuadrantDoubleComplex (ModuleCat ℚ)
  /-- In bidegree `(p,q)` with `p ≤ q` and `p ≤ i`, the term is the
  `(i-p)`th Hodge summand of Hochschild degree `q-p`. -/
  nonzeroIso : ∀ (p q : ℕ), p ≤ q → p ≤ i →
    CategoryTheory.Iso ((bicomplex.X p).X q)
      (ModuleCat.of ℚ ↥(hochschildHodgeDegree R (q - p) (i - p)))
  /-- Entries above the diagonal vanish. -/
  zeroAbove : ∀ (p q : ℕ), q < p → IsZero ((bicomplex.X p).X q)
  /-- Columns strictly to the right of the Hodge weight vanish. -/
  zeroPastWeight : ∀ (p q : ℕ), i < p → IsZero ((bicomplex.X p).X q)

/-- The total complex of the `i`th Hodge sub-double-complex.

Source: Weibel, Definition 9.8.14, pp. 344--353 (FC05-C09-U131). -/
def hodgeConnesTotalComplex {i : ℕ}
    (H : HodgeConnesDoubleComplexRealization R i)
    [HomologicalComplex₂.HasTotal H.bicomplex (ComplexShape.down ℕ)] :
    ChainComplex (ModuleCat ℚ) ℕ :=
  HomologicalComplex₂.total H.bicomplex (ComplexShape.down ℕ)

/-- Weibel's `i`th Hodge summand of cyclic homology,
`HC_n^(i)(R)`, defined as the homology of the total complex of the `i`th
Hodge sub-double-complex.

The direct-sum decomposition of ordinary cyclic homology into these summands
is theorem-layer content following the source definition.

Source: Weibel, Definition 9.8.14, pp. 344--353 (FC05-C09-U131). -/
def cyclicHodgeHomology {i : ℕ}
    (H : HodgeConnesDoubleComplexRealization R i)
    [HomologicalComplex₂.HasTotal H.bicomplex (ComplexShape.down ℕ)]
    (n : ℕ) : ModuleCat ℚ :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).obj
    (hodgeConnesTotalComplex R H)

end LeanCategories.Homological
