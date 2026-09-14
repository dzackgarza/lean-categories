/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.ExactCouple
public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Spectral sequences from bigraded exact couples

Weibel, *An Introduction to Homological Algebra* (1994), Proposition 5.9.2,
pp. 153--159 (FC05-C05-U070).

This file supplies the construction layer of Proposition 5.9.2.  A bigraded
exact couple has degree-shifting maps `i`, `j`, and `k`, with exactness imposed
at every bidegree.  The composite `k ≫ j` constructs a homological-complex
page.  Given a genuine repeated-derivation operation, the successive exact
couples therefore construct a Mathlib `SpectralSequence`; the next-page
isomorphism is the defining identification of the derived `E` object with the
homology of the preceding page.

The source's formulas for the bidegrees of the successive differentials, and
functoriality with respect to morphisms of exact couples, are proposition-level
claims and remain in Sweep IV.  In particular, this file does not assume a
spectral sequence as realization data.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v, u} C] [Abelian C]

/-- The bidegree index used by Weibel's exact couples. -/
abbrev ExactCoupleBidegree := ℤ × ℤ

/-- A degree-`s` family of maps, rewritten so that its target is exactly the
specified bidegree.  If `f_p : X_p ⟶ Y_{p+s}`, then
`bigradedIncoming s f p : X_{p-s} ⟶ Y_p`. -/
def bigradedIncoming {X Y : ExactCoupleBidegree → C} (s : ExactCoupleBidegree)
    (f : ∀ p, X p ⟶ Y (p + s)) (p : ExactCoupleBidegree) :
    X (p - s) ⟶ Y p :=
  f (p - s) ≫ eqToHom (congrArg Y (sub_add_cancel p s))

/-- A bigraded exact couple.  The three exactness fields are written at the
middle bidegree, so each short complex has literally matching source and target
objects even though `i`, `j`, and `k` shift degree.

Source: Weibel, §5.9 and Proposition 5.9.2 (FC05-C05-U068/U070). -/
structure BigradedExactCouple where
  /-- The `D` terms. -/
  D : ExactCoupleBidegree → C
  /-- The `E` terms. -/
  E : ExactCoupleBidegree → C
  /-- Bidegree of `i`. -/
  iDeg : ExactCoupleBidegree
  /-- Bidegree of `j`. -/
  jDeg : ExactCoupleBidegree
  /-- Bidegree of `k`. -/
  kDeg : ExactCoupleBidegree
  /-- The map `i`. -/
  i : ∀ p, D p ⟶ D (p + iDeg)
  /-- The map `j`. -/
  j : ∀ p, D p ⟶ E (p + jDeg)
  /-- The map `k`. -/
  k : ∀ p, E p ⟶ D (p + kDeg)
  /-- Consecutive maps `i,j` compose to zero at every middle bidegree. -/
  i_j : ∀ p, bigradedIncoming iDeg i p ≫ j p = 0
  /-- Consecutive maps `j,k` compose to zero at every middle bidegree. -/
  j_k : ∀ p, bigradedIncoming jDeg j p ≫ k p = 0
  /-- Consecutive maps `k,i` compose to zero at every middle bidegree. -/
  k_i : ∀ p, bigradedIncoming kDeg k p ≫ i p = 0
  /-- Exactness at every `D` term between `i` and `j`. -/
  exact_ij : ∀ p,
    (ShortComplex.mk (bigradedIncoming iDeg i p) (j p) (i_j p)).Exact
  /-- Exactness at every `E` term between `j` and `k`. -/
  exact_jk : ∀ p,
    (ShortComplex.mk (bigradedIncoming jDeg j p) (k p) (j_k p)).Exact
  /-- Exactness at every `D` term between `k` and `i`. -/
  exact_ki : ∀ p,
    (ShortComplex.mk (bigradedIncoming kDeg k p) (i p) (k_i p)).Exact

namespace BigradedExactCouple

variable (X : BigradedExactCouple (C := C))

/-- The incoming `i` map at a fixed middle bidegree. -/
abbrev incomingI (p : ExactCoupleBidegree) : X.D (p - X.iDeg) ⟶ X.D p :=
  bigradedIncoming X.iDeg X.i p

/-- The incoming `j` map at a fixed middle bidegree. -/
abbrev incomingJ (p : ExactCoupleBidegree) : X.D (p - X.jDeg) ⟶ X.E p :=
  bigradedIncoming X.jDeg X.j p

/-- The incoming `k` map at a fixed middle bidegree. -/
abbrev incomingK (p : ExactCoupleBidegree) : X.E (p - X.kDeg) ⟶ X.D p :=
  bigradedIncoming X.kDeg X.k p

/-- The degree step of the page differential `k ≫ j`, without yet identifying
it with Weibel's closed formula `(-r,r-1)`. -/
def pageStep : ExactCoupleBidegree := X.kDeg + X.jDeg

/-- The complex shape determined directly by the composite `k ≫ j`.
Its relation is written with the same parenthesization as the actual composite,
which keeps the construction free of artificial transport morphisms. -/
def pageShape : ComplexShape ExactCoupleBidegree where
  Rel p q := (p + X.kDeg) + X.jDeg = q
  next_eq h h' := h.symm.trans h'
  prev_eq h h' := by
    have hk : _ + X.kDeg = _ + X.kDeg := add_right_cancel (h.trans h'.symm)
    exact add_right_cancel hk

/-- The exact-couple differential on the `E` terms, in categorical composition
order: `E_p ⟶ D_{p+k} ⟶ E_{p+k+j}`. -/
def pageDifferential (p : ExactCoupleBidegree) :
    X.E p ⟶ X.E ((p + X.kDeg) + X.jDeg) :=
  X.k p ≫ X.j (p + X.kDeg)

/-- The direct `j`--`k` composite is zero. -/
theorem j_comp_k (p : ExactCoupleBidegree) :
    X.j p ≫ X.k (p + X.jDeg) = 0 := by
  have h := X.j_k (p + X.jDeg)
  simpa [bigradedIncoming] using h

/-- Consecutive exact-couple page differentials compose to zero. -/
theorem pageDifferential_sq (p : ExactCoupleBidegree) :
    X.pageDifferential p ≫
      X.pageDifferential ((p + X.kDeg) + X.jDeg) = 0 := by
  unfold pageDifferential
  slice_lhs 2 3 => rw [X.j_comp_k (p + X.kDeg)]
  simp

/-- The page homological complex intrinsically constructed from a bigraded
exact couple. -/
def page : HomologicalComplex C X.pageShape where
  X := X.E
  d p q :=
    if h : (p + X.kDeg) + X.jDeg = q then
      X.pageDifferential p ≫ eqToHom (congrArg X.E h)
    else 0
  shape p q h := by
    change ¬((p + X.kDeg) + X.jDeg = q) at h
    simp [h]
  d_comp_d' p q r hpq hqr := by
    change (p + X.kDeg) + X.jDeg = q at hpq
    change (q + X.kDeg) + X.jDeg = r at hqr
    simp only [dif_pos hpq, dif_pos hqr]
    subst q
    subst r
    simpa using X.pageDifferential_sq p

/-- Definition-layer data saying that `Y` is obtained from `X` by one exact-
couple derivation.  The two object formulas are the constructional content
needed by Proposition 5.9.2: `D' = im(i)` and `E' = H(E,kj)`.

The induced-map comparison formulas are already owned in the ungraded U069
interface `DerivedCoupleData`; their bigraded degree formulas are theorem-layer
content and are deliberately not duplicated as assumptions here. -/
structure DerivedData where
  /-- The next exact couple. -/
  couple : BigradedExactCouple (C := C)
  /-- The next `D` term is the image of the incoming `i` map. -/
  D_iso : ∀ p, couple.D p ≅ Abelian.image (X.incomingI p)
  /-- The next `E` term is the homology of the current exact-couple page. -/
  E_iso : ∀ p, couple.E p ≅ X.page.homology p

variable (derive : ∀ Y : BigradedExactCouple (C := C), Y.DerivedData)

/-- Repeatedly derive a bigraded exact couple.  This is the exact-couple tower
which supplies the pages of Proposition 5.9.2. -/
def iterate : ℕ → BigradedExactCouple (C := C)
  | 0 => X
  | n + 1 => (derive (iterate n)).couple

@[simp]
theorem iterate_zero : iterate X derive 0 = X := rfl

@[simp]
theorem iterate_succ (n : ℕ) :
    iterate X derive (n + 1) = (derive (iterate X derive n)).couple := rfl

/-- The complex shape on spectral-sequence page `r`, obtained from the
`(r-a)`th derived exact couple.  Below the starting page the value is harmless;
Mathlib only asks for pages under a proof `a ≤ r`. -/
def spectralShape (a r : ℤ) : ComplexShape ExactCoupleBidegree :=
  (iterate X derive (r - a).toNat).pageShape

/-- The `r`th page obtained from the `(r-a)`th derived exact couple. -/
def spectralPage (a r : ℤ) :
    HomologicalComplex C (spectralShape X derive a r) :=
  (iterate X derive (r - a).toNat).page

/-- The homology of page `r` is the `E` object on page `r+1`, by the defining
object formula of one exact-couple derivation. -/
def spectralPageIso (a r r' : ℤ) (p : ExactCoupleBidegree)
    (hrr' : r + 1 = r') (hr : a ≤ r) :
    (spectralPage X derive a r).homology p ≅
      (spectralPage X derive a r').X p := by
  have hnat : (r' - a).toNat = (r - a).toNat + 1 := by
    omega
  change (iterate X derive (r - a).toNat).page.homology p ≅
    (iterate X derive (r' - a).toNat).E p
  have hobj : (derive (iterate X derive (r - a).toNat)).couple.E p =
      (iterate X derive (r' - a).toNat).E p := by
    change (iterate X derive ((r - a).toNat + 1)).E p =
      (iterate X derive (r' - a).toNat).E p
    exact congrArg (fun Y : BigradedExactCouple (C := C) => Y.E p)
      (congrArg (iterate X derive) (Eq.symm hnat))
  exact ((derive (iterate X derive (r - a).toNat)).E_iso p).symm ≪≫ eqToIso hobj

/-- The spectral sequence constructed by repeated derivation of a bigraded
exact couple.  No spectral-sequence page or differential is supplied as input:
each page is the `k ≫ j` complex of the corresponding derived exact couple. -/
def spectralSequence (a : ℤ) :
    SpectralSequence C (spectralShape X derive a) a where
  page r _ := spectralPage X derive a r
  iso r r' p hrr' hr := spectralPageIso X derive a r r' p hrr' hr

end BigradedExactCouple

end LeanCategories.Homological
