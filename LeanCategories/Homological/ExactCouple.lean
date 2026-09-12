/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exact couples

Weibel, *An Introduction to Homological Algebra*, §5.9, p. 153
(FC05-C05-U068).

An exact couple is the cyclic diagram `D ⟶ D ⟶ E ⟶ D` which is exact at every vertex.  Weibel
works in modules, or more generally in an AB5 abelian category.  The definition itself only uses
abelian exactness; the stronger AB5 hypothesis enters the convergence arguments later in §5.9.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v, u} C] [Abelian C]

/-- An exact couple `D --i→ D --j→ E --k→ D`: the three consecutive pairs are exact.

Source: Weibel, *An Introduction to Homological Algebra*, §5.9, p. 153.  This is the
Mathlib-compatible port of the definition recorded in
`cmu-phil/Spectral@3b078f5f1de251637decf04bd3fc8aa01930a6b3::algebra/exact_couple.hlean`.
-/
structure ExactCouple where
  /-- The `D` object of the exact couple. -/
  D : C
  /-- The `E` object of the exact couple. -/
  E : C
  /-- The self-map `i : D ⟶ D`. -/
  i : D ⟶ D
  /-- The map `j : D ⟶ E`. -/
  j : D ⟶ E
  /-- The map `k : E ⟶ D`. -/
  k : E ⟶ D
  /-- Consecutive maps `i` and `j` compose to zero. -/
  i_j : i ≫ j = 0
  /-- Consecutive maps `j` and `k` compose to zero. -/
  j_k : j ≫ k = 0
  /-- Consecutive maps `k` and `i` compose to zero. -/
  k_i : k ≫ i = 0
  /-- Exactness at the second copy of `D`: `im(i) = ker(j)`. -/
  exact_ij : (ShortComplex.mk i j i_j).Exact
  /-- Exactness at `E`: `im(j) = ker(k)`. -/
  exact_jk : (ShortComplex.mk j k j_k).Exact
  /-- Exactness at the first copy of `D`: `im(k) = ker(i)`. -/
  exact_ki : (ShortComplex.mk k i k_i).Exact

namespace ExactCouple

variable (𝓔 : ExactCouple (C := C))

/-- The short complex `D --i→ D --j→ E`. -/
abbrev shortComplexIJ : ShortComplex C :=
  ShortComplex.mk 𝓔.i 𝓔.j 𝓔.i_j

/-- The short complex `D --j→ E --k→ D`. -/
abbrev shortComplexJK : ShortComplex C :=
  ShortComplex.mk 𝓔.j 𝓔.k 𝓔.j_k

/-- The short complex `E --k→ D --i→ D`. -/
abbrev shortComplexKI : ShortComplex C :=
  ShortComplex.mk 𝓔.k 𝓔.i 𝓔.k_i

end ExactCouple

namespace ExactCouple

variable (𝓔 : ExactCouple (C := C))

/-- The endomorphism `d = jk` of `E` in Weibel Definition 5.9.1; in categorical
composition order this is `k ≫ j`. -/
def differential : 𝓔.E ⟶ 𝓔.E :=
  𝓔.k ≫ 𝓔.j

/-- The self short complex on `E` used to form `H(E,d)`, once the square-zero condition from
Weibel Definition 5.9.1 has been supplied. -/
def differentialComplex (h : 𝓔.differential ≫ 𝓔.differential = 0) : ShortComplex C :=
  ShortComplex.mk 𝓔.differential 𝓔.differential h

/-- The canonical class map `d ↦ [j(d)]` into `H(E,d)` appearing in Weibel Definition 5.9.1,
p. 153--154. -/
noncomputable def jClass (h : 𝓔.differential ≫ 𝓔.differential = 0) :
    𝓔.D ⟶ (𝓔.differentialComplex h).homology := by
  change 𝓔.D ⟶ (ShortComplex.mk 𝓔.differential 𝓔.differential h).homology
  exact
    (ShortComplex.mk 𝓔.differential 𝓔.differential h).liftCycles 𝓔.j (by
        dsimp [differential]
        rw [← Category.assoc, 𝓔.j_k, zero_comp]) ≫
      (ShortComplex.mk 𝓔.differential 𝓔.differential h).homologyπ

end ExactCouple

/-- Definition-layer data identifying a candidate exact couple with the derived couple of `𝓔`.
The fields are exactly Weibel, *An Introduction to Homological Algebra*, Definition 5.9.1,
pp. 153--154: `D' = i(D)`, `E' = H(E,jk)`, `i'` is the restriction of `i`,
`j'(i(d)) = [j(d)]`, and `k'([e]) = k(e)`.

The source separately establishes square-zero, well-definedness, exactness of the resulting triangle,
and iterability.  Those are not asserted as standalone theorems here: `differential_sq_zero` and the
fact that `couple` is already an `ExactCouple` are hypotheses of this definition-layer relation.
-/
structure DerivedCoupleData (𝓔 : ExactCouple (C := C)) where
  /-- The square-zero datum needed to form `H(E,jk)`. -/
  differential_sq_zero : 𝓔.differential ≫ 𝓔.differential = 0
  /-- The candidate derived exact couple. -/
  couple : ExactCouple (C := C)
  /-- Identification `D' ≅ i(D)`. -/
  D_iso : couple.D ≅ Abelian.image 𝓔.i
  /-- Identification `E' ≅ H(E,jk)`. -/
  E_iso : couple.E ≅ (𝓔.differentialComplex differential_sq_zero).homology
  /-- `i'` is the restriction of `i` to its image. -/
  i_restriction :
    D_iso.hom ≫ Abelian.image.ι 𝓔.i ≫ 𝓔.i =
      couple.i ≫ D_iso.hom ≫ Abelian.image.ι 𝓔.i
  /-- Under the chosen identifications, `j'(i(d)) = [j(d)]`. -/
  j_induced :
    Abelian.factorThruImage 𝓔.i ≫ D_iso.inv ≫ couple.j ≫ E_iso.hom =
      𝓔.jClass differential_sq_zero
  /-- Under the chosen identifications, `k'([e]) = k(e)` on cycles. -/
  k_induced :
    (𝓔.differentialComplex differential_sq_zero).homologyπ ≫ E_iso.inv ≫ couple.k ≫
        D_iso.hom ≫ Abelian.image.ι 𝓔.i =
      (𝓔.differentialComplex differential_sq_zero).iCycles ≫ 𝓔.k

end LeanCategories.Homological
