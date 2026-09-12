/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DoubleComplexFirstPages

/-!
# Homotopies of maps of double complexes

Weibel, *An Introduction to Homological Algebra* (1994), Definition 5.7.3,
pp. 145--149 (FC05-C05-U053).

For maps `f,g : K → L` of first-quadrant homological double complexes, a
double-complex homotopy consists of a horizontal degree-raising component and
a vertical degree-raising component.  Their same-direction terms sum to
`g-f`, while each component anticommutes with the differential in the other
direction.

The theorem that the signed sum of the two components induces an ordinary
chain homotopy on total complexes is result-level and is not asserted here.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Horizontal contribution `d^h s^h + s^h d^h` in bidegree `(p,q)`. -/
def horizontalHomotopyContribution
    {K L : ChainComplex (ChainComplex C ℕ) ℕ}
    (h : ∀ p q : ℕ, (K.X p).X q ⟶ (L.X (p + 1)).X q) :
    ∀ p q : ℕ, (K.X p).X q ⟶ (L.X p).X q
  | 0, q => h 0 q ≫ (L.d 1 0).f q
  | p + 1, q =>
      (K.d (p + 1) p).f q ≫ h p q +
        h (p + 1) q ≫ (L.d (p + 2) (p + 1)).f q

/-- Vertical contribution `d^v s^v + s^v d^v` in bidegree `(p,q)`. -/
def verticalHomotopyContribution
    {K L : ChainComplex (ChainComplex C ℕ) ℕ}
    (h : ∀ p q : ℕ, (K.X p).X q ⟶ (L.X p).X (q + 1)) :
    ∀ p q : ℕ, (K.X p).X q ⟶ (L.X p).X q
  | p, 0 => h p 0 ≫ (L.X p).d 1 0
  | p, q + 1 =>
      (K.X p).d (q + 1) q ≫ h p q +
        h p (q + 1) ≫ (L.X p).d (q + 2) (q + 1)

/-- Weibel's chain homotopy between two maps of first-quadrant double
complexes. -/
structure DoubleComplexHomotopy
    {K L : ChainComplex (ChainComplex C ℕ) ℕ} (f g : K ⟶ L) where
  /-- Horizontal degree-raising component `K_{p,q} → L_{p+1,q}`. -/
  horizontal : ∀ p q : ℕ, (K.X p).X q ⟶ (L.X (p + 1)).X q
  /-- Vertical degree-raising component `K_{p,q} → L_{p,q+1}`. -/
  vertical : ∀ p q : ℕ, (K.X p).X q ⟶ (L.X p).X (q + 1)
  /-- The horizontal and vertical homotopy contributions sum to `g-f`. -/
  homotopy_eq : ∀ p q : ℕ,
    (g.f p).f q - (f.f p).f q =
      horizontalHomotopyContribution horizontal p q +
        verticalHomotopyContribution vertical p q
  /-- The horizontal homotopy component anticommutes with the vertical
  differential. -/
  horizontal_vertical : ∀ p q : ℕ,
    horizontal p (q + 1) ≫ (L.X (p + 1)).d (q + 1) q +
      (K.X p).d (q + 1) q ≫ horizontal p q = 0
  /-- The vertical homotopy component anticommutes with the horizontal
  differential. -/
  vertical_horizontal : ∀ p q : ℕ,
    vertical (p + 1) q ≫ (L.d (p + 1) p).f (q + 1) +
      (K.d (p + 1) p).f q ≫ vertical p q = 0

end LeanCategories.Homological
