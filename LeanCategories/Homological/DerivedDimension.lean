/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Data.ENat.Lattice

/-!
# Acyclic objects and the dimension of derived functors

Weibel, *An Introduction to Homological Algebra*.

## Main definitions

We define three concepts from the Weibel catalogue:

1. **Acyclic object for a functor** (§5.8, Def. 5.8.2): an object `X` is
   *acyclic* for a left exact functor `F` if `R^i F(X) = 0` for all `i > 0`.

2. **Cohomological dimension of a functor** (§10.5, Def. 10.5.10): for a
   left exact functor `F : C → D`, the cohomological dimension at an object
   `X` is `sup { n | R^n F(X) ≠ 0 }`. The global cohomological dimension
   is the supremum over all objects.

3. **Homological dimension of a functor** (§10.5, Def. 10.5.10): for a
   right exact functor `F : C → D`, the homological dimension at an object
   `X` is `sup { n | L_n F(X) ≠ 0 }`. The global homological dimension
   is the supremum over all objects.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

/-!
## Acyclic objects for a functor
-/

/-- An object `X` is **acyclic** for the functor `F` if all higher right
    derived functors vanish at `X` (Weibel, Def. 5.8.2).

    Explicitly, `IsAcyclicFor F X` holds when `R^i F(X) ≅ 0` for every
    `i > 0`. -/
def IsAcyclicFor {C D : Type*} [Category C] [Category D] [Abelian C]
    [HasInjectiveResolutions C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (X : C) : Prop :=
  ∀ n > 0, IsZero ((F.rightDerived n).obj X)

/-- An object `X` is **coacyclic** for the functor `F` if all higher left
    derived functors vanish at `X` (dual to Weibel, Def. 5.8.2).

    Explicitly, `IsCoacyclicFor F X` holds when `L^i F(X) ≅ 0` for every
    `i > 0`. -/
def IsCoacyclicFor {C D : Type*} [Category C] [Category D] [Abelian C]
    [HasProjectiveResolutions C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (X : C) : Prop :=
  ∀ n > 0, IsZero ((F.leftDerived n).obj X)

/-!
## Cohomological dimension of a functor
-/

/-- The **cohomological dimension** of a left exact functor `F` at an
    object `X` (Weibel, Def. 10.5.10).

    This is the supremum of all `n` such that `R^n F(X)` is nonzero.
    The result takes values in `WithBot ℕ∞`; it is `⊥` precisely when
    `R^0 F(X) ≅ 0` (i.e., `F(X) ≅ 0`).

    Since `projectiveDimension` and related invariants in Mathlib use
    `WithBot ℕ∞`, we follow the same convention. -/
noncomputable def cohomologicalDimensionAt {C D : Type*} [Category C]
    [Category D] [Abelian C] [HasInjectiveResolutions C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (X : C) : WithBot ℕ∞ :=
  sSup (Set.image (Nat.cast (R := WithBot ℕ∞)) {n : ℕ | ¬ IsZero ((F.rightDerived n).obj X)})

/-- The **(right) global cohomological dimension** of a left exact functor
    `F : C → D` is the supremum of `cohomologicalDimensionAt F X` over all
    objects `X` of `C` (Weibel, Def. 10.5.10). -/
noncomputable def cohomologicalDimension {C D : Type*} [Category C]
    [Category D] [Abelian C] [HasInjectiveResolutions C] [Abelian D]
    [HasZeroObject C] (F : C ⥤ D) [F.Additive] : WithBot ℕ∞ :=
  sSup (Set.range fun (X : C) => cohomologicalDimensionAt F X)

/-!
## Homological dimension of a functor
-/

/-- The **homological dimension** of a right exact functor `F` at an
    object `X` (Weibel, Def. 10.5.10).

    This is the supremum of all `n` such that `L_n F(X)` is nonzero.
    The result takes values in `WithBot ℕ∞`. -/
noncomputable def homologicalDimensionAt {C D : Type*} [Category C]
    [Category D] [Abelian C] [HasProjectiveResolutions C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (X : C) : WithBot ℕ∞ :=
  sSup (Set.image (Nat.cast (R := WithBot ℕ∞)) {n : ℕ | ¬ IsZero ((F.leftDerived n).obj X)})

/-- The **(right) global homological dimension** of a right exact functor
    `F : C → D` is the supremum of `homologicalDimensionAt F X` over all
    objects `X` of `C` (Weibel, Def. 10.5.10). -/
noncomputable def homologicalDimension {C D : Type*} [Category C]
    [Category D] [Abelian C] [HasProjectiveResolutions C] [Abelian D]
    [HasZeroObject C] (F : C ⥤ D) [F.Additive] : WithBot ℕ∞ :=
  sSup (Set.range fun (X : C) => homologicalDimensionAt F X)

end LeanCategories.Homological
