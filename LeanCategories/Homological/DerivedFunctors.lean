/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

@[expose] public section

/-!
# Derived-functor routes

This module exposes the pinned Mathlib constructions without local aliases.

* `CategoryTheory.Tor` is the left-derived tensor product.
* `Functor.totalLeftDerived` and `Functor.totalRightDerived` provide derived
  functors by localization.
* `ihom` and `Functor.sheafPushforwardContinuous` are the source functors for
  derived internal Hom and derived pushforward.
* `Limits.FormalCoproduct.cechComplexFunctor` and derived-category homology
  provide the available Cech and hypercohomology ingredients.

Mathlib has no named derived internal-Hom, derived-pushforward, or
hypercohomology functor in the pinned version. This route does not invent one.
-/
