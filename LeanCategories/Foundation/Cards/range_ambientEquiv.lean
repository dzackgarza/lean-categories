/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Foundation.Subsets

/-! # Card: `LeanCategories.Foundation.Subsets.range_ambientEquiv`

source: Riehl, *Category Theory in Context*, chapter 2 (the category of elements and the subobject ordering of a comma category), realized as Mathlib's `CategoryTheory.Elements` and `CategoryTheory.Comma.Arrow` at the pinned revision: a subset of `X` is a monomorphism `A ↪ X`, i.e. an object of `Subobjects(Set)`.

Published copy of a result of `LeanCategories.Foundation.Subsets`. The definition module keeps the original declaration; this file states it and delegates the proof, and the platform submission replaces that proof term with `by sorry`.
-/

namespace LeanCategories.Cards

open LeanCategories.Foundation

open CategoryTheory
universe u v w

/-- For a morphism `f : S ⟶ T` in the core of subsets, the image of the range of `S` under the induced equivalence on ambient sets is the range of `T`. -/
theorem LeanCategories_Foundation_Subsets_range_ambientEquiv : ∀ {S T : Core Subsets.{u}} (f : S ⟶ T),
    (Subsets.ambientEquiv f) '' S.of.range = T.of.range :=
  LeanCategories.Foundation.Subsets.range_ambientEquiv

end LeanCategories.Cards
