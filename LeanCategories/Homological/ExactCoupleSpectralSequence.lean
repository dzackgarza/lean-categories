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

/-- A homogeneous family of maps rewritten as an incoming map at a specified
bidegree.  The degree shift is represented by an actual automorphism of the
indexing set; this is the construction-level datum needed below, while closed
integer formulas for those shifts belong to Proposition 5.9.2's theorem layer.

If `f_p : X_p ⟶ Y_{s(p)}`, then `bigradedIncoming s f p` is
`X_{s⁻¹(p)} ⟶ Y_p`. -/
def bigradedIncoming {X Y : ExactCoupleBidegree → C}
    (s : ExactCoupleBidegree ≃ ExactCoupleBidegree)
    (f : ∀ p, X p ⟶ Y (s p)) (p : ExactCoupleBidegree) :
    X (s.symm p) ⟶ Y p :=
  f (s.symm p) ≫ eqToHom (congrArg Y (s.apply_symm_apply p))

/-- A bigraded exact couple.  The three exactness fields are written at the
middle bidegree, so each short complex has literally matching source and target
objects even though `i`, `j`, and `k` shift degree.

Source: Weibel, §5.9 and Proposition 5.9.2 (FC05-C05-U068/U070). -/
structure BigradedExactCouple where
  /-- The `D` terms. -/
  D : ExactCoupleBidegree → C
  /-- The `E` terms. -/
  E : ExactCoupleBidegree → C
  /-- Index shift of `i`. -/
  iShift : ExactCoupleBidegree ≃ ExactCoupleBidegree
  /-- Index shift of `j`. -/
  jShift : ExactCoupleBidegree ≃ ExactCoupleBidegree
  /-- Index shift of `k`. -/
  kShift : ExactCoupleBidegree ≃ ExactCoupleBidegree
  /-- The map `i`. -/
  i : ∀ p, D p ⟶ D (iShift p)
  /-- The map `j`. -/
  j : ∀ p, D p ⟶ E (jShift p)
  /-- The map `k`. -/
  k : ∀ p, E p ⟶ D (kShift p)
  /-- Consecutive homogeneous maps `i,j` compose to zero. -/
  i_j : ∀ p, i p ≫ j (iShift p) = 0
  /-- Consecutive homogeneous maps `j,k` compose to zero. -/
  j_k : ∀ p, j p ≫ k (jShift p) = 0
  /-- Consecutive homogeneous maps `k,i` compose to zero. -/
  k_i : ∀ p, k p ≫ i (kShift p) = 0
  /-- Exactness of each consecutive `i,j` pair. -/
  exact_ij : ∀ p,
    (ShortComplex.mk (i p) (j (iShift p)) (i_j p)).Exact
  /-- Exactness of each consecutive `j,k` pair. -/
  exact_jk : ∀ p,
    (ShortComplex.mk (j p) (k (jShift p)) (j_k p)).Exact
  /-- Exactness of each consecutive `k,i` pair. -/
  exact_ki : ∀ p,
    (ShortComplex.mk (k p) (i (kShift p)) (k_i p)).Exact

namespace BigradedExactCouple

variable (X : BigradedExactCouple (C := C))

/-- The incoming `i` map at a fixed middle bidegree. -/
abbrev incomingI (p : ExactCoupleBidegree) : X.D (X.iShift.symm p) ⟶ X.D p :=
  bigradedIncoming X.iShift X.i p

/-- The incoming `j` map at a fixed middle bidegree. -/
abbrev incomingJ (p : ExactCoupleBidegree) : X.D (X.jShift.symm p) ⟶ X.E p :=
  bigradedIncoming X.jShift X.j p

/-- The incoming `k` map at a fixed middle bidegree. -/
abbrev incomingK (p : ExactCoupleBidegree) : X.E (X.kShift.symm p) ⟶ X.D p :=
  bigradedIncoming X.kShift X.k p

/-- The index shift of the page differential `k ≫ j`, without yet identifying
it with Weibel's closed formula `(-r,r-1)`. -/
def pageShift : ExactCoupleBidegree ≃ ExactCoupleBidegree :=
  X.kShift.trans X.jShift

/-- The complex shape determined directly by the composite `k ≫ j`.
Its relation is written with the same parenthesization as the actual composite,
which keeps the construction free of artificial transport morphisms. -/
def pageShape : ComplexShape ExactCoupleBidegree where
  Rel p q := X.pageShift p = q
  next_eq h h' := h.symm.trans h'
  prev_eq h h' := X.pageShift.injective (h.trans h'.symm)

/-- The exact-couple differential on the `E` terms, in categorical composition
order: `E_p ⟶ D_{p+k} ⟶ E_{p+k+j}`. -/
def pageDifferential (p : ExactCoupleBidegree) :
    X.E p ⟶ X.E (X.pageShift p) :=
  X.k p ≫ X.j (X.kShift p)

/-- The direct `j`--`k` composite is zero. -/
theorem j_comp_k (p : ExactCoupleBidegree) :
    X.j p ≫ X.k (X.jShift p) = 0 := by
  exact X.j_k p

/-- Consecutive exact-couple page differentials compose to zero. -/
theorem pageDifferential_sq (p : ExactCoupleBidegree) :
    X.pageDifferential p ≫
      X.pageDifferential (X.pageShift p) = 0 := by
  unfold pageDifferential pageShift
  simp only [Equiv.trans_apply]
  slice_lhs 2 3 =>
    exact X.j_comp_k (X.kShift p)
  simp
  all_goals rfl

/-- The page homological complex intrinsically constructed from a bigraded
exact couple. -/
def page : HomologicalComplex C X.pageShape where
  X := X.E
  d p q :=
    if h : X.pageShift p = q then
      X.pageDifferential p ≫ eqToHom (congrArg X.E h)
    else 0
  shape p q h := by
    change ¬(X.pageShift p = q) at h
    simp [h]
  d_comp_d' p q r hpq hqr := by
    change X.pageShift p = q at hpq
    change X.pageShift q = r at hqr
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
  dIso : ∀ p, couple.D p ≅ Abelian.image (X.incomingI p)
  /-- The next `E` term is the homology of the current exact-couple page. -/
  eIso : ∀ p, couple.E p ≅ X.page.homology p

/-- A recursively derived exact-couple tower rooted at `X`.

This is the source-faithful input to the associated spectral-sequence
construction: one supplies the actual sequence of exact couples together with
the fact that each successor is the derived couple of its predecessor.  No
global choice of a derived couple for unrelated exact couples is required. -/
structure DerivedTower where
  /-- The `n`th exact couple in the tower. -/
  couple : ℕ → BigradedExactCouple (C := C)
  /-- The tower starts at `X`. -/
  zero_eq : couple 0 = X
  /-- One-step derived-couple data at every stage. -/
  step : ∀ n, (couple n).DerivedData
  /-- The derived couple supplied by `step n` is the next tower term. -/
  succ_eq : ∀ n, (step n).couple = couple (n + 1)

namespace DerivedTower

variable (T : X.DerivedTower)

/-- The complex shape on page `r` of a spectral sequence starting at page `a`. -/
def spectralShape (a r : ℤ) : ComplexShape ExactCoupleBidegree :=
  (T.couple (r - a).toNat).pageShape

/-- The `r`th page of the spectral sequence attached to the tower. -/
def spectralPage (a r : ℤ) : HomologicalComplex C (spectralShape X T a r) :=
  (T.couple (r - a).toNat).page

/-- Successive pages are related by the homology identification in the
derived-couple step. -/
def spectralPageIso (a r r' : ℤ) (p : ExactCoupleBidegree)
    (hrr' : r + 1 = r') (hr : a ≤ r) :
    (spectralPage X T a r).homology p ≅ (spectralPage X T a r').X p := by
  have hnat : (r' - a).toNat = (r - a).toNat + 1 := by omega
  let n := (r - a).toNat
  have hnext : (T.step n).couple.E p = (T.couple (r' - a).toNat).E p := by
    rw [T.succ_eq n]
    exact congrArg (fun m : ℕ => (T.couple m).E p) hnat.symm
  exact ((T.step n).eIso p).symm ≪≫ eqToIso hnext

/-- The spectral sequence intrinsically constructed from a rooted derived
exact-couple tower. -/
def spectralSequence (a : ℤ) :
    SpectralSequence C (spectralShape X T a) a where
  page r _ := spectralPage X T a r
  iso r r' p hrr' hr := spectralPageIso X T a r r' p hrr' hr

end DerivedTower

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
  exact ((derive (iterate X derive (r - a).toNat)).eIso p).symm ≪≫ eqToIso hobj

/-- The spectral sequence constructed by repeated derivation of a bigraded
exact couple.  No spectral-sequence page or differential is supplied as input:
each page is the `k ≫ j` complex of the corresponding derived exact couple. -/
def spectralSequence (a : ℤ) :
    SpectralSequence C (spectralShape X derive a) a where
  page r _ := spectralPage X derive a r
  iso r r' p hrr' hr := spectralPageIso X derive a r r' p hrr' hr

end BigradedExactCouple

end LeanCategories.Homological
