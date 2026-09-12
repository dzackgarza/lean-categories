/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.MixedComplex
public import LeanCategories.Homological.DoubleComplexFirstPages

/-!
# Connes' double complex of a mixed complex

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.8.2,
pp. 344--353 (FC05-C09-U115).

For a mixed complex `(M,b,B)`, Connes' first-quadrant double complex has
entry `M_{q-p}` in bidegree `(p,q)` when `p≤q`, and zero otherwise.  Its
vertical differential is `b` and its horizontal differential is `B`.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Definition-layer realization of Connes' double complex attached to a
mixed complex. -/
structure ConnesDoubleComplexRealization (M : MixedComplex C) where
  /-- The first-quadrant bicomplex. -/
  bicomplex : FirstQuadrantDoubleComplex C
  /-- On and below the diagonal, bidegree `(p,q)` is `M_{q-p}`. -/
  nonzeroIso : ∀ (p q : ℕ), p ≤ q →
    CategoryTheory.Iso ((bicomplex.X p).X q) (M.chain.X (q - p))
  /-- Above the diagonal the entries vanish. -/
  zeroAbove : ∀ (p q : ℕ), q < p → IsZero ((bicomplex.X p).X q)
  /-- The vertical differential is `b`. -/
  vertical : ∀ (p q : ℕ) (hpq : p ≤ q),
    (nonzeroIso p (q + 1) (by omega)).hom ≫
        M.chain.d (q + 1 - p) (q - p) =
      (bicomplex.X p).d (q + 1) q ≫ (nonzeroIso p q hpq).hom
  /-- The horizontal differential is `B`. -/
  horizontal : ∀ (p q : ℕ) (hpq : p + 1 ≤ q),
    (nonzeroIso (p + 1) q hpq).hom ≫ M.B (q - (p + 1)) ≫
        eqToHom (congrArg M.chain.X (show q - (p + 1) + 1 = q - p by omega)) =
      (bicomplex.d (p + 1) p).f q ≫
        (nonzeroIso p q (by omega)).hom

end LeanCategories.Homological
