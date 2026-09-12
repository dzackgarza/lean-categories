/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Basic

/-!
# Balanced multivariable functors

Weibel, *An Introduction to Homological Algebra* (1994), Definition 2.7.7
and its left-balanced dual, §2.7, pp. 58--65, FC05-C02-U080--U081.

A multivariable functor is represented as a functor out of the dependent
product of its input categories.  Variance is encoded by orienting each
input category: a contravariant variable uses the opposite category.
One-variable restrictions are obtained by varying a single coordinate and
holding every other coordinate fixed.

With this convention Weibel's two right-balanced clauses become one.  An
injective object in a covariant input is injective in its oriented category;
a projective object `P` in a contravariant input becomes `op P`, which
Mathlib infers to be injective in the opposite category.  Right balancedness
therefore says that after fixing any oriented injective input, every
remaining one-variable restriction is exact.
-/
@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

universe w v u vD uD

namespace MultivariableFunctor

variable {I : Type w} (C : I → Type u) [∀ i, Category.{v} (C i)]

/-- The coordinate functor used to vary slot `i`: identity up to the equality-induced equivalence
in slot `i`, and constant in every other slot. -/
noncomputable def coordinate (X : ∀ i, C i) (i j : I) : C i ⥤ C j := by
  classical
  by_cases h : j = i
  · exact (Pi.eqToEquivalence C h).inverse
  · exact (Functor.const (C i)).obj (X j)

/-- Vary only coordinate `i`, keeping all other entries of `X` fixed. -/
noncomputable def insert (X : ∀ i, C i) (i : I) : C i ⥤ (∀ i, C i) :=
  Functor.pi' (fun j => coordinate C X i j)

/-- The one-variable restriction obtained by fixing all coordinates except `i`. -/
noncomputable def restrictVariable {D : Type uD} [Category.{vD} D] (T : (∀ i, C i) ⥤ D)
    (X : ∀ i, C i) (i : I) : C i ⥤ D :=
  insert C X i ⋙ T

end MultivariableFunctor

variable {I : Type w} {C : I → Type u} [∀ i, Category.{v} (C i)]
variable {D : Type uD} [Category.{vD} D]

/-- A multivariable functor is left exact when every one-variable restriction is left exact. -/
def IsMultivariableLeftExact (T : (∀ i, C i) ⥤ D) : Prop :=
  ∀ (X : ∀ i, C i) (i : I),
    PreservesFiniteLimits (MultivariableFunctor.restrictVariable C T X i)

/-- A multivariable functor is right exact when every one-variable restriction is right exact. -/
def IsMultivariableRightExact (T : (∀ i, C i) ⥤ D) : Prop :=
  ∀ (X : ∀ i, C i) (i : I),
    PreservesFiniteColimits (MultivariableFunctor.restrictVariable C T X i)

/-- A multivariable functor is exact in variable `j` with all other entries fixed at `X`. -/
def IsExactInVariable (T : (∀ i, C i) ⥤ D) (X : ∀ i, C i) (j : I) : Prop :=
  PreservesFiniteLimits (MultivariableFunctor.restrictVariable C T X j) ∧
    PreservesFiniteColimits (MultivariableFunctor.restrictVariable C T X j)

variable [∀ i, Abelian (C i)] [Abelian D]

/-- Weibel's right-balanced condition for a multivariable left-exact functor.

The family `C` is the family of *oriented* input categories: a contravariant variable is represented
by an opposite category. Thus an injective object in an oriented contravariant slot is exactly a
projective object in the original category. -/
def IsRightBalanced (T : (∀ i, C i) ⥤ D) : Prop :=
  IsMultivariableLeftExact T ∧
    ∀ (X : ∀ i, C i) (i : I), Injective (X i) →
      ∀ j : I, j ≠ i → IsExactInVariable T X j

/-- Weibel's left-balanced condition for a multivariable right-exact functor.

As for `IsRightBalanced`, the family `C` consists of the *oriented* input categories.  Thus a
projective object in an oriented covariant slot is a projective object of the original category,
whereas in an oriented contravariant slot it represents an injective object of the original
category.  Left balancedness says that fixing such an oriented projective input makes every
remaining one-variable restriction exact. -/
def IsLeftBalanced (T : (∀ i, C i) ⥤ D) : Prop :=
  IsMultivariableRightExact T ∧
    ∀ (X : ∀ i, C i) (i : I), Projective (X i) →
      ∀ j : I, j ≠ i → IsExactInVariable T X j

end LeanCategories.Homological
