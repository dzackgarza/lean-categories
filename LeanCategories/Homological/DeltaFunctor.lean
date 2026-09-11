/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.ExactSequenceCategories
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Homological and cohomological δ-functors

Weibel, *An Introduction to Homological Algebra* (1994), Definition 2.1.1,
§2.1, pp. 30--31, FC05-C02-U001.

A δ-functor is a nonnegatively graded family of additive functors together
with natural connecting morphisms attached to short exact sequences.  The
connecting maps extend each short exact sequence to a long exact sequence.
The source convention that negative-degree functors vanish is represented by
indexing the family by `ℕ`; the terminal/initial degree-zero exactness fields
record the corresponding zero terms explicitly.

Naturality is built into the connecting maps by making them natural
transformations on the category of short exact sequences.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits
open scoped ZeroObject

universe v₁ u₁ v₂ u₂

section ShortExactCategory

variable (A : Type u₁) [Category.{v₁} A] [HasZeroMorphisms A]

/-- The category whose objects are short exact sequences in `A` and whose morphisms are
commutative diagrams of short exact sequences. -/
abbrev ShortExactCat : Type (max u₁ v₁) :=
  ObjectProperty.FullSubcategory (fun S : ShortComplex A => S.ShortExact)

/-- Forget that a short complex is short exact. -/
abbrev shortExactForget : ShortExactCat A ⥤ ShortComplex A :=
  ObjectProperty.ι _

/-- Left object of a short exact sequence. -/
abbrev shortExactLeft : ShortExactCat A ⥤ A :=
  shortExactForget A ⋙ ShortComplex.π₁

/-- Middle object of a short exact sequence. -/
abbrev shortExactMiddle : ShortExactCat A ⥤ A :=
  shortExactForget A ⋙ ShortComplex.π₂

/-- Right object of a short exact sequence. -/
abbrev shortExactRight : ShortExactCat A ⥤ A :=
  shortExactForget A ⋙ ShortComplex.π₃

end ShortExactCategory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable (B : Type u₂) [Category.{v₂} B] [Abelian B]

namespace HomologicalDeltaFunctor

/-- The consecutive pair `Tₙ(A) ⟶ Tₙ(B) ⟶ Tₙ(C)` associated to a short exact sequence. -/
noncomputable def degreeShortComplex (T : ℕ → A ⥤+ B) (n : ℕ) (S : ShortExactCat A) :
    ShortComplex B := by
  letI : (T n).obj.Additive := (T n).property
  letI : (T n).obj.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive (T n).obj
  exact S.obj.map (T n).obj

/-- The consecutive pair `Tₙ₊₁(B) ⟶ Tₙ₊₁(C) ⟶ Tₙ(A)`. -/
noncomputable def rightBoundaryShortComplex (T : ℕ → A ⥤+ B)
    (δ : ∀ n, shortExactRight A ⋙ (T (n + 1)).obj ⟶ shortExactLeft A ⋙ (T n).obj)
    (n : ℕ) (S : ShortExactCat A)
    (h : (T (n + 1)).obj.map S.obj.g ≫ (δ n).app S = 0) : ShortComplex B :=
  ShortComplex.mk ((T (n + 1)).obj.map S.obj.g) ((δ n).app S) h

/-- The consecutive pair `Tₙ₊₁(C) ⟶ Tₙ(A) ⟶ Tₙ(B)`. -/
noncomputable def leftBoundaryShortComplex (T : ℕ → A ⥤+ B)
    (δ : ∀ n, shortExactRight A ⋙ (T (n + 1)).obj ⟶ shortExactLeft A ⋙ (T n).obj)
    (n : ℕ) (S : ShortExactCat A)
    (h : (δ n).app S ≫ (T n).obj.map S.obj.f = 0) : ShortComplex B :=
  ShortComplex.mk ((δ n).app S) ((T n).obj.map S.obj.f) h

/-- The terminal degree-zero pair `T₀(B) ⟶ T₀(C) ⟶ 0`. -/
noncomputable def degreeZeroRightShortComplex (T : ℕ → A ⥤+ B) (S : ShortExactCat A) :
    ShortComplex B :=
  ShortComplex.mk ((T 0).obj.map S.obj.g)
    (0 : (T 0).obj.obj S.obj.X₃ ⟶ (0 : B)) (by simp)

end HomologicalDeltaFunctor

/-- Weibel's homological δ-functor (Definition 2.1.1).

The family is indexed by `ℕ`; this is the source convention that negative-degree functors are zero.
The connecting transformation indexed by `n` is `δ_{n+1} : T_{n+1}(C) ⟶ T_n(A)`.
Its naturality as a transformation on `ShortExactCat A` is exactly Weibel's second axiom.
The four exactness fields are the four kinds of consecutive positions in the associated long exact
sequence, including the terminal `T₀(C) ⟶ 0` position. -/
structure HomologicalDeltaFunctor (A : Type u₁) [Category.{v₁} A] [Abelian A]
    (B : Type u₂) [Category.{v₂} B] [Abelian B] where
  T : ℕ → A ⥤+ B
  delta : ∀ n, shortExactRight A ⋙ (T (n + 1)).obj ⟶ shortExactLeft A ⋙ (T n).obj
  g_delta_zero : ∀ n (S : ShortExactCat A),
    (T (n + 1)).obj.map S.obj.g ≫ (delta n).app S = 0
  delta_f_zero : ∀ n (S : ShortExactCat A),
    (delta n).app S ≫ (T n).obj.map S.obj.f = 0
  exact_degree : ∀ n (S : ShortExactCat A),
    (HomologicalDeltaFunctor.degreeShortComplex B T n S).Exact
  exact_g_delta : ∀ n (S : ShortExactCat A),
    (HomologicalDeltaFunctor.rightBoundaryShortComplex B T delta n S (g_delta_zero n S)).Exact
  exact_delta_f : ∀ n (S : ShortExactCat A),
    (HomologicalDeltaFunctor.leftBoundaryShortComplex B T delta n S (delta_f_zero n S)).Exact
  exact_degree_zero_right : ∀ S : ShortExactCat A,
    (HomologicalDeltaFunctor.degreeZeroRightShortComplex B T S).Exact

namespace HomologicalDeltaFunctor

variable (T : HomologicalDeltaFunctor A B)

/-- Naturality of the homological connecting morphism under a morphism of short exact sequences.
This is Weibel's second axiom in component form. -/
@[reassoc]
theorem delta_naturality (n : ℕ) {S S' : ShortExactCat A} (φ : S ⟶ S') :
    (T.T (n + 1)).obj.map φ.hom.τ₃ ≫ (T.delta n).app S' =
      (T.delta n).app S ≫ (T.T n).obj.map φ.hom.τ₁ := by
  exact (T.delta n).naturality φ

end HomologicalDeltaFunctor

namespace CohomologicalDeltaFunctor

/-- The consecutive pair `Tⁿ(A) ⟶ Tⁿ(B) ⟶ Tⁿ(C)`. -/
noncomputable def degreeShortComplex (T : ℕ → A ⥤+ B) (n : ℕ) (S : ShortExactCat A) :
    ShortComplex B := by
  letI : (T n).obj.Additive := (T n).property
  letI : (T n).obj.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive (T n).obj
  exact S.obj.map (T n).obj

/-- The initial degree-zero pair `0 ⟶ T⁰(A) ⟶ T⁰(B)`. -/
noncomputable def degreeZeroLeftShortComplex (T : ℕ → A ⥤+ B) (S : ShortExactCat A) :
    ShortComplex B :=
  ShortComplex.mk (0 : (0 : B) ⟶ (T 0).obj.obj S.obj.X₁)
    ((T 0).obj.map S.obj.f) (by simp)

/-- The consecutive pair `Tⁿ(B) ⟶ Tⁿ(C) ⟶ Tⁿ⁺¹(A)`. -/
noncomputable def rightBoundaryShortComplex (T : ℕ → A ⥤+ B)
    (δ : ∀ n, shortExactRight A ⋙ (T n).obj ⟶ shortExactLeft A ⋙ (T (n + 1)).obj)
    (n : ℕ) (S : ShortExactCat A)
    (h : (T n).obj.map S.obj.g ≫ (δ n).app S = 0) : ShortComplex B :=
  ShortComplex.mk ((T n).obj.map S.obj.g) ((δ n).app S) h

/-- The consecutive pair `Tⁿ(C) ⟶ Tⁿ⁺¹(A) ⟶ Tⁿ⁺¹(B)`. -/
noncomputable def leftBoundaryShortComplex (T : ℕ → A ⥤+ B)
    (δ : ∀ n, shortExactRight A ⋙ (T n).obj ⟶ shortExactLeft A ⋙ (T (n + 1)).obj)
    (n : ℕ) (S : ShortExactCat A)
    (h : (δ n).app S ≫ (T (n + 1)).obj.map S.obj.f = 0) : ShortComplex B :=
  ShortComplex.mk ((δ n).app S) ((T (n + 1)).obj.map S.obj.f) h

end CohomologicalDeltaFunctor

/-- Weibel's cohomological δ-functor (Definition 2.1.1).

The connecting transformation is `δⁿ : Tⁿ(C) ⟶ Tⁿ⁺¹(A)`. Naturality on short exact sequences
is built into the natural transformation. The exactness fields encode every consecutive position
of the source long exact sequence, including the initial `0 ⟶ T⁰(A)` position. -/
structure CohomologicalDeltaFunctor (A : Type u₁) [Category.{v₁} A] [Abelian A]
    (B : Type u₂) [Category.{v₂} B] [Abelian B] where
  T : ℕ → A ⥤+ B
  delta : ∀ n, shortExactRight A ⋙ (T n).obj ⟶ shortExactLeft A ⋙ (T (n + 1)).obj
  g_delta_zero : ∀ n (S : ShortExactCat A),
    (T n).obj.map S.obj.g ≫ (delta n).app S = 0
  delta_f_zero : ∀ n (S : ShortExactCat A),
    (delta n).app S ≫ (T (n + 1)).obj.map S.obj.f = 0
  exact_degree_zero_left : ∀ S : ShortExactCat A,
    (CohomologicalDeltaFunctor.degreeZeroLeftShortComplex B T S).Exact
  exact_degree : ∀ n (S : ShortExactCat A),
    (CohomologicalDeltaFunctor.degreeShortComplex B T n S).Exact
  exact_g_delta : ∀ n (S : ShortExactCat A),
    (CohomologicalDeltaFunctor.rightBoundaryShortComplex B T delta n S (g_delta_zero n S)).Exact
  exact_delta_f : ∀ n (S : ShortExactCat A),
    (CohomologicalDeltaFunctor.leftBoundaryShortComplex B T delta n S (delta_f_zero n S)).Exact

namespace CohomologicalDeltaFunctor

variable (T : CohomologicalDeltaFunctor A B)

/-- Naturality of the cohomological connecting morphism under a morphism of short exact sequences.
This is Weibel's second axiom in component form. -/
@[reassoc]
theorem delta_naturality (n : ℕ) {S S' : ShortExactCat A} (φ : S ⟶ S') :
    (T.T n).obj.map φ.hom.τ₃ ≫ (T.delta n).app S' =
      (T.delta n).app S ≫ (T.T (n + 1)).obj.map φ.hom.τ₁ := by
  exact (T.delta n).naturality φ

end CohomologicalDeltaFunctor

end LeanCategories.Homological
