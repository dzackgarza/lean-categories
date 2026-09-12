/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.ExactCouple

/-!
# Convergence data of a bigraded exact couple

Weibel, *An Introduction to Homological Algebra* (1994), Definition 5.9.5,
pp. 153--159 (FC05-C05-U073), and the following bounded-below definition
(FC05-C05-U074).

For each total degree `n`, the `i`-maps of a suitably bigraded exact couple
form the directed system `p ↦ D_{p,n-p}`.  Its colimit is the abutment `H_n`,
and the image of `D_{p,n-p} → H_n` is the filtration term `F_p H_n`.

Exhaustiveness, the comparison from `E∞` to the associated graded object, the
`Z∞` weak-convergence criterion, and the classical convergence theorem are
result-level content and are deliberately excluded here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Definition-layer realization of the total-degree directed systems of a
bigraded exact couple.

The functor `diagonal n` is the system obtained by restricting the exact
couple's `i`-maps to bidegrees `(p,n-p)`.  The `iDiagonal` and compatibility
field make that restriction explicit without rebuilding the earlier ungraded
exact-couple structure. -/
structure ExactCoupleConvergenceData where
  /-- The bigraded `D`-terms. -/
  D : ℤ → ℤ → C
  /-- The `i`-map restricted to total degree `n`. -/
  iDiagonal : ∀ (n p : ℤ), D p (n - p) ⟶ D (p + 1) (n - (p + 1))
  /-- The directed system along `i` in each total degree. -/
  diagonal : ℤ → (ℤ ⥤ C)
  /-- Identification of the system objects with the bigraded `D`-terms. -/
  diagonalIso : ∀ (n p : ℤ), (diagonal n).obj p ≅ D p (n - p)
  /-- The successor map of the directed system is the corresponding `i`-map. -/
  diagonal_succ : ∀ (n p : ℤ),
    (diagonalIso n p).inv ≫
        (diagonal n).map (homOfLE (by omega : p ≤ p + 1)) ≫
          (diagonalIso n (p + 1)).hom =
      iDiagonal n p

/-- Weibel's abutment `H_n = colim_p D_{p,n-p}`. -/
noncomputable def exactCoupleAbutment (X : ExactCoupleConvergenceData (C := C))
    (n : ℤ) [HasColimit (X.diagonal n)] : C :=
  colimit (X.diagonal n)

/-- The canonical map `D_{p,n-p} → H_n`. -/
noncomputable def exactCoupleFiltrationMap (X : ExactCoupleConvergenceData (C := C))
    (n p : ℤ) [HasColimit (X.diagonal n)] :
    X.D p (n - p) ⟶ exactCoupleAbutment X n :=
  (X.diagonalIso n p).inv ≫ colimit.ι (X.diagonal n) p

/-- Weibel's filtration object `F_p H_n`, defined as the image of
`D_{p,n-p} → H_n`. -/
noncomputable def exactCoupleFiltrationObject
    (X : ExactCoupleConvergenceData (C := C)) (n p : ℤ)
    [HasColimit (X.diagonal n)] : C :=
  image (exactCoupleFiltrationMap X n p)

/-- Inclusion `F_p H_n ↪ H_n`. -/
noncomputable def exactCoupleFiltrationInclusion
    (X : ExactCoupleConvergenceData (C := C)) (n p : ℤ)
    [HasColimit (X.diagonal n)] :
    exactCoupleFiltrationObject X n p ⟶ exactCoupleAbutment X n :=
  image.ι (exactCoupleFiltrationMap X n p)

/-- Weibel's bounded-below condition: in each total degree `n`, all
`D_{p,n-p}` vanish for sufficiently small `p`. -/
def IsBoundedBelowExactCouple (X : ExactCoupleConvergenceData (C := C)) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, p < b → IsZero (X.D p (n - p))

end LeanCategories.Homological
