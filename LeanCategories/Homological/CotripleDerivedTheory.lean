/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DeltaFunctor
public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Theories of cotriple-left derived functors

Weibel, *An Introduction to Homological Algebra*, Definition 8.7.3, p. 288
(FC05-C08-U079).

The definition is relative to a fixed cotriple `T` on `A`.  A short exact sequence of coefficient
functors is admissible when it remains short exact after precomposition by `T`.  The theory assigns
a natural family `L_n E`, an augmentation `L_0 E ⟶ E`, vanishes in positive degrees on coefficient
functors of the form `E T`, and carries admissible short exact sequences to the stated long exact
sequence.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace LeanCategories.Homological

universe vA uA vM uM

variable {A : Type uA} [Category.{vA} A]
variable (M : Type uM) [Category.{vM} M] [Abelian M]

/-- Precomposition of coefficient functors by the endofunctor underlying a cotriple.
Thus `cotriplePrecompose T M` sends `E` to Weibel's `E T`.

Source: Weibel, Definition 8.7.3 (FC05-C08-U079). -/
def cotriplePrecompose (T : Comonad A) : (A ⥤ M) ⥤ (A ⥤ M) :=
  (Functor.whiskeringLeft A A M).obj T.toFunctor

/-- The admissibility condition on a short complex of coefficient functors: it is short exact, and
its evaluation after precomposition by the cotriple is short exact at every object of `A`.

Source: Weibel, Definition 8.7.3(2) (FC05-C08-U079). -/
def CotripleExact (T : Comonad A) (S : ShortComplex (A ⥤ M)) : Prop :=
  S.ShortExact ∧ ∀ a : A, (S.map ((evaluation A M).obj (T.obj a))).ShortExact

/-- The category of cotriple-exact short exact sequences of coefficient functors.

Source: Weibel, Definition 8.7.3(2) (FC05-C08-U079). -/
abbrev CotripleExactCat (T : Comonad A) : Type _ :=
  ObjectProperty.FullSubcategory (CotripleExact M T)

/-- Left coefficient functor in a cotriple-exact short exact sequence. -/
abbrev cotripleExactLeft (T : Comonad A) : CotripleExactCat M T ⥤ (A ⥤ M) :=
  ObjectProperty.ι _ ⋙ ShortComplex.π₁

/-- Middle coefficient functor in a cotriple-exact short exact sequence. -/
abbrev cotripleExactMiddle (T : Comonad A) : CotripleExactCat M T ⥤ (A ⥤ M) :=
  ObjectProperty.ι _ ⋙ ShortComplex.π₂

/-- Right coefficient functor in a cotriple-exact short exact sequence. -/
abbrev cotripleExactRight (T : Comonad A) : CotripleExactCat M T ⥤ (A ⥤ M) :=
  ObjectProperty.ι _ ⋙ ShortComplex.π₃

namespace CotripleLeftDerivedTheory

variable (T : Comonad A)

/-- Consecutive degree-`n` maps attached to an admissible short exact sequence. -/
def degreeShortComplex (L : ℕ → (A ⥤ M) ⥤ (A ⥤ M)) (n : ℕ)
    (S : CotripleExactCat M T)
    (h : (L n).map S.obj.f ≫ (L n).map S.obj.g = 0) : ShortComplex (A ⥤ M) :=
  ShortComplex.mk ((L n).map S.obj.f) ((L n).map S.obj.g) h

/-- Consecutive maps `L_{n+1}E ⟶ L_{n+1}E'' ⟶ L_nE'`. -/
def rightBoundaryShortComplex (L : ℕ → (A ⥤ M) ⥤ (A ⥤ M))
    (δ : ∀ n, cotripleExactRight M T ⋙ L (n + 1) ⟶ cotripleExactLeft M T ⋙ L n)
    (n : ℕ) (S : CotripleExactCat M T)
    (h : (L (n + 1)).map S.obj.g ≫ (δ n).app S = 0) : ShortComplex (A ⥤ M) :=
  ShortComplex.mk ((L (n + 1)).map S.obj.g) ((δ n).app S) h

/-- Consecutive maps `L_{n+1}E'' ⟶ L_nE' ⟶ L_nE`. -/
def leftBoundaryShortComplex (L : ℕ → (A ⥤ M) ⥤ (A ⥤ M))
    (δ : ∀ n, cotripleExactRight M T ⋙ L (n + 1) ⟶ cotripleExactLeft M T ⋙ L n)
    (n : ℕ) (S : CotripleExactCat M T)
    (h : (δ n).app S ≫ (L n).map S.obj.f = 0) : ShortComplex (A ⥤ M) :=
  ShortComplex.mk ((δ n).app S) ((L n).map S.obj.f) h

/-- The terminal pair `L₀E ⟶ L₀E'' ⟶ 0` in the relative long exact sequence. -/
def degreeZeroRightShortComplex (L : ℕ → (A ⥤ M) ⥤ (A ⥤ M))
    (S : CotripleExactCat M T) : ShortComplex (A ⥤ M) :=
  ShortComplex.mk ((L 0).map S.obj.g) (0 : (L 0).obj S.obj.X₃ ⟶ (0 : A ⥤ M)) (by simp)

end CotripleLeftDerivedTheory

/-- A theory of cotriple-left derived functors in the sense of Barr--Beck.

`L n` is natural in the coefficient functor `E`; `augmentation` is Weibel's `λ : L₀E ⟶ E`.
The first two axiom fields encode `λ : L₀(E T) ≅ E T` and `L_n(E T)=0` for `n>0`.  The remaining
fields encode the natural connecting maps and exactness of every consecutive position of the long
exact sequence for cotriple-exact coefficient sequences.

Source: Weibel, Definition 8.7.3, p. 288 (FC05-C08-U079). -/
structure CotripleLeftDerivedTheory (T : Comonad A) where
  L : ℕ → (A ⥤ M) ⥤ (A ⥤ M)
  augmentation : L 0 ⟶ 𝟭 (A ⥤ M)
  augmentation_isIso : ∀ E : A ⥤ M, IsIso (augmentation.app ((cotriplePrecompose M T).obj E))
  positive_isZero : ∀ (n : ℕ), n ≠ 0 → ∀ E : A ⥤ M,
    IsZero ((L n).obj ((cotriplePrecompose M T).obj E))
  delta : ∀ n, cotripleExactRight M T ⋙ L (n + 1) ⟶ cotripleExactLeft M T ⋙ L n
  degree_zero : ∀ n (S : CotripleExactCat M T),
    (L n).map S.obj.f ≫ (L n).map S.obj.g = 0
  g_delta_zero : ∀ n (S : CotripleExactCat M T),
    (L (n + 1)).map S.obj.g ≫ (delta n).app S = 0
  delta_f_zero : ∀ n (S : CotripleExactCat M T),
    (delta n).app S ≫ (L n).map S.obj.f = 0
  exact_degree : ∀ n (S : CotripleExactCat M T),
    (CotripleLeftDerivedTheory.degreeShortComplex M T L n S (degree_zero n S)).Exact
  exact_g_delta : ∀ n (S : CotripleExactCat M T),
    (CotripleLeftDerivedTheory.rightBoundaryShortComplex M T L delta n S
      (g_delta_zero n S)).Exact
  exact_delta_f : ∀ n (S : CotripleExactCat M T),
    (CotripleLeftDerivedTheory.leftBoundaryShortComplex M T L delta n S
      (delta_f_zero n S)).Exact
  exact_degree_zero_right : ∀ S : CotripleExactCat M T,
    (CotripleLeftDerivedTheory.degreeZeroRightShortComplex M T L S).Exact

end LeanCategories.Homological
