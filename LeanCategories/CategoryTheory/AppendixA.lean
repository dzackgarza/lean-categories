/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Abelian.Basic

@[expose] public section

/-!
# Weibel Appendix A: categorical language

These names route the Appendix A vocabulary to Mathlib's definitions. They
are aliases, not parallel category-theory structures.

Reference search:

* Mathlib `CategoryTheory.Category`, `Functor`, `NatTrans`, `Limits.LimitCone`,
  `Limits.ColimitCocone`, `Adjunction`, and `Abelian`.
* `facebookresearch/atlas-lean`, `leanprover-community/LeanProject`, and
  `google-deepmind/formal-conjectures` contain no more general Lean 4
  replacement for these pinned Mathlib definitions.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ u v

namespace LeanCategories.CategoryTheory

/-! ### Categories, functors, and natural transformations -/

abbrev CategoryStruct := CategoryTheory.CategoryStruct

abbrev Category := CategoryTheory.Category

abbrev Functor := CategoryTheory.Functor

abbrev NaturalTransformation := CategoryTheory.NatTrans

/-! ### Abelian categories -/

abbrev AbelianCategory := CategoryTheory.Abelian

/-! ### Limits and colimits -/

abbrev Cone {J : Type u₁} [CategoryTheory.Category.{v₁} J]
    {C : Type u₂} [CategoryTheory.Category.{v₂} C] (F : J ⥤ C) :=
  CategoryTheory.Limits.Cone F

abbrev LimitCone {J : Type u₁} [CategoryTheory.Category.{v₁} J]
    {C : Type u₂} [CategoryTheory.Category.{v₂} C] (F : J ⥤ C) :=
  CategoryTheory.Limits.LimitCone F

abbrev HasLimit {J : Type u₁} [CategoryTheory.Category.{v₁} J]
    {C : Type u₂} [CategoryTheory.Category.{v₂} C] (F : J ⥤ C) :=
  CategoryTheory.Limits.HasLimit F

abbrev Cocone {J : Type u₁} [CategoryTheory.Category.{v₁} J]
    {C : Type u₂} [CategoryTheory.Category.{v₂} C] (F : J ⥤ C) :=
  CategoryTheory.Limits.Cocone F

abbrev ColimitCocone {J : Type u₁} [CategoryTheory.Category.{v₁} J]
    {C : Type u₂} [CategoryTheory.Category.{v₂} C] (F : J ⥤ C) :=
  CategoryTheory.Limits.ColimitCocone F

abbrev HasColimit {J : Type u₁} [CategoryTheory.Category.{v₁} J]
    {C : Type u₂} [CategoryTheory.Category.{v₂} C] (F : J ⥤ C) :=
  CategoryTheory.Limits.HasColimit F

/-! ### Adjunctions -/

abbrev Adjunction {C : Type u₁} [CategoryTheory.Category.{v₁} C]
    {D : Type u₂} [CategoryTheory.Category.{v₂} D]
    (F : C ⥤ D) (G : D ⥤ C) :=
  CategoryTheory.Adjunction F G

end LeanCategories.CategoryTheory

