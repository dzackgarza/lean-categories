/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.FilteredComplexSpectralSequence
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Explicit pages of the spectral sequence of a filtered complex

Weibel, *An Introduction to Homological Algebra*, Construction 5.4.6, pp. 133--134
(FC05-C05-U031).

For an increasing filtered chain complex, Weibel defines approximate cycles
`A_p^r = {c ∈ F_p C : dc ∈ F_{p-r} C}`, their images `Z_p^r` in `E_p^0`, and the boundary
subobjects `B_p^r = η_p(d A_{p+r-1}^{r-1})`.  The `r`th page is `E_p^r=Z_p^r/B_p^r`.  The well-defined differential induced on these
quotients, and the proof that the resulting pages form the spectral sequence of 5.4.1, are
result-layer assertions and remain for the theorem sweep.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ChainComplexFiltration

variable {A : Type u} [Category.{v, u} A] [Abelian A] {K : ChainComplex A ℤ}

/-- The degree-`n` filtration subobject `F_p C_n ⊆ C_n`.

Source: Weibel, Construction 5.4.6 (FC05-C05-U031). -/
noncomputable def degreeSubobject (F : ChainComplexFiltration A (ComplexShape.down ℤ) K)
    (p n : ℤ) : Subobject (K.X n) :=
  Subobject.mk ((F.obj p).arrow.f n)

/-- The canonical isomorphism from the chosen representative of `F_p C_n` as a subobject back to
the degree-`n` object of the filtered subcomplex. -/
noncomputable def degreeSubobjectIso
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p n : ℤ) :
    (F.degreeSubobject p n : A) ≅ (Subobject.underlying.obj (F.obj p)).X n := by
  rw [degreeSubobject]
  exact Subobject.underlyingIso ((F.obj p).arrow.f n)


/-- Degreewise filtration subobjects are monotone in the filtration index. -/
theorem degreeSubobject_mono
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) {p q : ℤ} (h : p ≤ q) (n : ℤ) :
    F.degreeSubobject p n ≤ F.degreeSubobject q n := by
  let m := (Subobject.ofLE (F.obj p) (F.obj q) (F.monotone h)).f n
  apply Subobject.mk_le_mk_of_comm m
  change m ≫ (F.obj q).arrow.f n = (F.obj p).arrow.f n
  have hh := congrArg (fun k => k.f n) (Subobject.ofLE_arrow (F.monotone h))
  exact hh

/-- Weibel's approximate cycles
`A_p^r(n) = {c ∈ F_p C_n : dc ∈ F_{p-r} C_{n-1}}`.

Categorically this is the intersection of `F_p C_n` with the inverse image of
`F_{p-r} C_{n-1}` under the differential.

Source: Weibel, Construction 5.4.6 (FC05-C05-U031). -/
noncomputable def approximateCycles
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    Subobject (K.X n) :=
  F.degreeSubobject p n ⊓
    (Subobject.pullback (K.d n n.pred)).obj
      (F.degreeSubobject (p - (r : ℤ)) n.pred)

/-- Every approximate cycle lies in the `p`th filtration term. -/
theorem approximateCycles_le_degree
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    F.approximateCycles p r n ≤ F.degreeSubobject p n := by
  rw [approximateCycles]
  exact inf_le_left


/-- The differential of an approximate cycle lands in the prescribed lower filtration term. -/
theorem approximateCycles_d_factors
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    (F.degreeSubobject (p - (r : ℤ)) n.pred).Factors
      ((F.approximateCycles p r n).arrow ≫ K.d n n.pred) := by
  rw [approximateCycles]
  apply (pullback_factors_iff (K.d n n.pred)
    (F.degreeSubobject (p - (r : ℤ)) n.pred)
    (F.approximateCycles p r n).arrow).mp
  exact Subobject.inf_arrow_factors_right _ _

/-- Raising both the filtration and approximation indices by one gives an inclusion
`A_{p-1}^r ⊆ A_p^{r+1}`. -/
theorem approximateCycles_previous_le
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    F.approximateCycles (p - 1) r n ≤ F.approximateCycles p (r + 1) n := by
  rw [approximateCycles]
  apply le_inf
  · exact (F.approximateCycles_le_degree (p - 1) r n).trans
      (F.degreeSubobject_mono (by omega) n)
  · apply Subobject.le_of_factors
    apply (pullback_factors_iff (K.d n n.pred)
      (F.degreeSubobject (p - ((r + 1 : ℕ) : ℤ)) n.pred)
      (F.approximateCycles (p - 1) r n).arrow).mpr
    have h := F.approximateCycles_d_factors (p - 1) r n
    have hidx : p - 1 - (r : ℤ) = p - ((r + 1 : ℕ) : ℤ) := by
      push_cast
      omega
    rw [hidx] at h
    exact h

/-- The quotient map `η_p : F_p C ⟶ F_p C/F_{p-1}C = E_p^0`. -/
noncomputable def associatedGradedProjection
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) :
    Subobject.underlying.obj (F.obj p) ⟶ F.associatedGradedComplex p :=
  cokernel.π (Subobject.ofLE (F.obj (p - 1)) (F.obj p) (F.monotone (by omega)))

/-- The map from `A_p^r(n)` to `E_p^0(n)` whose image is `Z_p^r(n)`. -/
noncomputable def approximateCycleToE0
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    (F.approximateCycles p r n : A) ⟶ (F.associatedGradedComplex p).X n :=
  Subobject.ofLE (F.approximateCycles p r n) (F.degreeSubobject p n)
      (F.approximateCycles_le_degree p r n) ≫
    (F.degreeSubobjectIso p n).hom ≫
    (F.associatedGradedProjection p).f n

/-- The approximate-cycle subobject `Z_p^r ⊆ E_p^0`.
For `r=0` Weibel sets `Z_p^0=E_p^0`; for positive `r` it is the image of `A_p^r`.

Source: Weibel, Construction 5.4.6 (FC05-C05-U031). -/
noncomputable def cycleSubobject
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    Subobject ((F.associatedGradedComplex p).X n) :=
  match r with
  | 0 => ⊤
  | r + 1 => imageSubobject (F.approximateCycleToE0 p (r + 1) n)

/-- The subobject `A_{p+r}^r(n+1)`, written with the arithmetically simplified target
`F_p C_n` so that its differential factorization is definitionally visible.

Source: Weibel, Construction 5.4.6 (FC05-C05-U031). -/
noncomputable def boundaryApproximateCycles
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    Subobject (K.X n.succ) :=
  F.degreeSubobject (p + (r : ℤ)) n.succ ⊓
    (Subobject.pullback (K.d n.succ n)).obj (F.degreeSubobject p n)

/-- The differential of an element of `A_{p+r}^r(n+1)`, viewed as a map into `C_n`. -/
noncomputable def boundaryDifferential
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    (F.boundaryApproximateCycles p r n : A) ⟶ K.X n :=
  (F.boundaryApproximateCycles p r n).arrow ≫ K.d n.succ n

/-- By construction of `A_{p+r}^r`, its differential factors through `F_p C_n`. -/
theorem boundaryDifferential_factors_degree
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    (F.degreeSubobject p n).Factors (F.boundaryDifferential p r n) := by
  apply (pullback_factors_iff (K.d n.succ n) (F.degreeSubobject p n)
    (F.boundaryApproximateCycles p r n).arrow).mp
  exact Subobject.inf_arrow_factors_right _ _

/-- A boundary `dc` with `c ∈ A_{p+r}^r` is an approximate cycle in `A_p^{r+1}`:
it lies in `F_p` by definition of the source pullback and its own differential is zero.

Source: Weibel, Construction 5.4.6 (FC05-C05-U031). -/
theorem boundaryDifferential_factors_approximateCycles
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    (F.approximateCycles p (r + 1) n).Factors (F.boundaryDifferential p r n) := by
  rw [approximateCycles, Subobject.inf_factors]
  constructor
  · exact F.boundaryDifferential_factors_degree p r n
  · apply (pullback_factors_iff (K.d n n.pred)
      (F.degreeSubobject (p - ((r + 1 : ℕ) : ℤ)) n.pred)
      (F.boundaryDifferential p r n)).mpr
    rw [boundaryDifferential, Category.assoc, K.d_comp_d, comp_zero]
    exact Subobject.factors_zero (P :=
      F.degreeSubobject (p - ((r + 1 : ℕ) : ℤ)) n.pred)

/-- The map whose image is `B_p^{r+1}(n)=η_p(d A_{p+r}^r(n+1))`.

Source: Weibel, Construction 5.4.6 (FC05-C05-U031). -/
noncomputable def boundaryToE0
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    (F.boundaryApproximateCycles p r n : A) ⟶
      (F.associatedGradedComplex p).X n :=
  (F.degreeSubobject p n).factorThru (F.boundaryDifferential p r n)
      (Subobject.factors_of_le (F.boundaryDifferential p r n)
        (F.approximateCycles_le_degree p (r + 1) n)
        (F.boundaryDifferential_factors_approximateCycles p r n)) ≫
    (F.degreeSubobjectIso p n).hom ≫
    (F.associatedGradedProjection p).f n

/-- The canonical factorization `d A_{p+r}^r ⟶ A_p^{r+1}`. -/
noncomputable def boundaryToApproximateCycles
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    (F.boundaryApproximateCycles p r n : A) ⟶ (F.approximateCycles p (r + 1) n : A) :=
  (F.approximateCycles p (r + 1) n).factorThru (F.boundaryDifferential p r n)
    (F.boundaryDifferential_factors_approximateCycles p r n)

/-- The two descriptions of a boundary in `E_p^0` agree: first factor through
`A_p^{r+1}` and then map to `E_p^0`, or first factor through `F_p` and then quotient. -/
theorem boundaryToApproximateCycles_comp_toE0
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    F.boundaryToApproximateCycles p r n ≫ F.approximateCycleToE0 p (r + 1) n =
      F.boundaryToE0 p r n := by
  rw [boundaryToApproximateCycles, approximateCycleToE0, boundaryToE0]
  rw [Subobject.factorThru_ofLE (F.approximateCycles_le_degree p (r + 1) n)
    (F.boundaryDifferential_factors_approximateCycles p r n)]
  simp only [Category.assoc]

/-- The boundary subobject `B_p^r ⊆ E_p^0`; `B_p^0=0` and
`B_p^{r+1}=η_p(d A_{p+r}^r)`.

Source: Weibel, Construction 5.4.6 (FC05-C05-U031). -/
noncomputable def boundarySubobject
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    Subobject ((F.associatedGradedComplex p).X n) :=
  match r with
  | 0 => ⊥
  | r + 1 => imageSubobject (F.boundaryToE0 p r n)


/-- Every `r`-boundary is an `r`-cycle, `B_p^r ⊆ Z_p^r`.

This is the intrinsic containment needed to form Weibel's quotient `E_p^r=Z_p^r/B_p^r`.
Source: Weibel, Construction 5.4.6 (FC05-C05-U031). -/
theorem boundarySubobject_le_cycleSubobject
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    F.boundarySubobject p r n ≤ F.cycleSubobject p r n := by
  cases r with
  | zero =>
      simp [boundarySubobject, cycleSubobject]
  | succ r =>
      change imageSubobject (F.boundaryToE0 p r n) ≤
        imageSubobject (F.approximateCycleToE0 p (r + 1) n)
      rw [← F.boundaryToApproximateCycles_comp_toE0 p r n]
      exact imageSubobject_comp_le _ _

/-- The image `d(A_{p+r}^r) ⊆ C_n` appearing in the alternate quotient presentation
of the `(r+1)`st page.

Source: Weibel, Construction 5.4.6 (FC05-C05-U031). -/
noncomputable def boundaryImageInComplex
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    Subobject (K.X n) :=
  imageSubobject (F.boundaryDifferential p r n)

/-- The image `d(A_{p+r}^r)` is contained in `A_p^{r+1}`. -/
theorem boundaryImageInComplex_le_approximateCycles
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    F.boundaryImageInComplex p r n ≤ F.approximateCycles p (r + 1) n := by
  apply imageSubobject_le (F.boundaryDifferential p r n)
    (F.boundaryToApproximateCycles p r n)
  exact Subobject.factorThru_arrow _ _ _

/-- The denominator in Weibel's alternate presentation
`E_p^{r+1} ≅ A_p^{r+1}/(d(A_{p+r}^r)+A_{p-1}^r)`. -/
noncomputable def pageDenominator
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    Subobject (K.X n) :=
  F.boundaryImageInComplex p r n ⊔ F.approximateCycles (p - 1) r n

/-- The alternate-page denominator is contained in its numerator `A_p^{r+1}`. -/
theorem pageDenominator_le_approximateCycles
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    F.pageDenominator p r n ≤ F.approximateCycles p (r + 1) n := by
  rw [pageDenominator]
  apply sup_le
  · exact F.boundaryImageInComplex_le_approximateCycles p r n
  · exact F.approximateCycles_previous_le p r n

/-- The ambient differential of an approximate cycle. -/
noncomputable def approximateCycleDifferentialAmbient
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    (F.approximateCycles p r n : A) ⟶ K.X n.pred :=
  (F.approximateCycles p r n).arrow ≫ K.d n n.pred

/-- The differential sends `A_p^r(n)` into `A_{p-r}^r(n-1)`. -/
theorem approximateCycleDifferential_factors
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    (F.approximateCycles (p - (r : ℤ)) r n.pred).Factors
      (F.approximateCycleDifferentialAmbient p r n) := by
  change (F.degreeSubobject (p - (r : ℤ)) n.pred ⊓
    (Subobject.pullback (K.d n.pred (n.pred.pred))).obj
      (F.degreeSubobject (p - (r : ℤ) - (r : ℤ)) (n.pred.pred))).Factors
        (F.approximateCycleDifferentialAmbient p r n)
  rw [Subobject.inf_factors]
  constructor
  · exact F.approximateCycles_d_factors p r n
  · apply (pullback_factors_iff (K.d n.pred (n.pred.pred))
      (F.degreeSubobject (p - (r : ℤ) - (r : ℤ)) (n.pred.pred))
      (F.approximateCycleDifferentialAmbient p r n)).mpr
    rw [approximateCycleDifferentialAmbient, Category.assoc, K.d_comp_d, comp_zero]
    exact Subobject.factors_zero

/-- The differential restricted to approximate cycles,
`A_p^r(n) ⟶ A_{p-r}^r(n-1)`. -/
noncomputable def approximateCycleDifferential
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) :
    (F.approximateCycles p r n : A) ⟶
      (F.approximateCycles (p - (r : ℤ)) r n.pred : A) :=
  (F.approximateCycles (p - (r : ℤ)) r n.pred).factorThru
    (F.approximateCycleDifferentialAmbient p r n)
    (F.approximateCycleDifferential_factors p r n)

/-- Weibel's `r`th spectral-sequence page object
`E_p^r(n)=Z_p^r(n)/B_p^r(n)`.

Source: Weibel, Construction 5.4.6 (FC05-C05-U031). -/
noncomputable def pageObject
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (p : ℤ) (r : ℕ) (n : ℤ) : A :=
  cokernel (Subobject.ofLE (F.boundarySubobject p r n) (F.cycleSubobject p r n)
    (F.boundarySubobject_le_cycleSubobject p r n))

/-- Bigraded notation for the page object: `E^r_{p,q}=E_p^r(p+q)`. -/
abbrev spectralSequenceEr
    (F : ChainComplexFiltration A (ComplexShape.down ℤ) K) (r : ℕ) (p q : ℤ) : A :=
  F.pageObject p r (p + q)

end ChainComplexFiltration

end LeanCategories.Homological
