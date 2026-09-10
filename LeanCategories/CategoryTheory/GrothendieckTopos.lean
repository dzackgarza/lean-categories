/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

open CategoryTheory

namespace LeanCategories.CategoryTheory

universe v u w

/-- Riehl Appendix E.4 (FC03-CE-U007): a category is a Grothendieck topos if it is
 equivalent to the category of set-valued sheaves on some small site. This is the source's
 equivalent site-theoretic characterization. -/
def IsGrothendieckTopos (E : Type u) [Category.{v} E] : Prop :=
  ∃ (C : Type w) (_ : SmallCategory C) (J : GrothendieckTopology C),
    Nonempty (E ≌ Sheaf J (Type w))

end LeanCategories.CategoryTheory
