/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Foundation.Subsets

/-!
# Card: `LeanCategories.Foundation.Subsets.range_ambientEquiv`

Published copy of a result from `LeanCategories.Foundation.Subsets`, whose definition module
keeps the original declaration. The statement and binders are copied from the source; the proof
is delegated to the original, and the platform submission replaces that right-hand side with
`by sorry`.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Foundation

/-- For a morphism `f : S ⟶ T` in the core of subsets — where `S` and `T` are subobjects of sets,
carried by `Subsets` as `Core`-objects with an underlying subset `S.of ⊆ ambient` — the image of
the range of `S` under the induced equivalence `Subsets.ambientEquiv f` on ambient sets is exactly
the range of `T`. In symbols: `(Subsets.ambientEquiv f) '' S.of.range = T.of.range`, where
`''` is image of a set under a function and `·.range` is the range of the underlying subset
inclusion. -/
theorem LeanCategories_Foundation_Subsets_range_ambientEquiv
    {S T : Core Subsets.{u}} (f : S ⟶ T) :
    (Subsets.ambientEquiv f) '' S.of.range = T.of.range :=
  Subsets.range_ambientEquiv f

end LeanCategories.Foundation
