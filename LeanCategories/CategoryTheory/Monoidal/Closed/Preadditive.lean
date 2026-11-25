/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Biclosed preadditive categories are monoidal preadditive

## Provenance (lean-categories#22)

Ported from `TauCeti/CategoryTheory/Monoidal/Closed/Preadditive.lean` (The Tau Ceti contributors, Apache 2.0), commit
`ca32605ff53921fa0689dd312618b7cfaafa7e43`, namespaces renamed `TauCeti` →
`LeanCategories`. The unit's provenance and search record is in
`LeanCategories/AlgebraicGeometry/RelativeSpec/Basic.lean`.


If tensoring on either side with a fixed object is a left adjoint (for instance in a closed braided
monoidal category), it preserves binary coproducts. In a preadditive category, binary coproducts
are binary biproducts, and a functor preserving them is additive. Hence the tensor product of
morphisms is additive in each variable: the category is `MonoidalPreadditive`.

This applies to categories such as sheaves of modules, whose monoidal structure is constructed
abstractly (for instance by localization) rather than from a bilinear formula on morphisms.

## Main declaration

* `LeanCategories.monoidalPreadditive_of_isLeftAdjoint`.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace LeanCategories

/-- A preadditive monoidal category with binary coproducts, in which tensoring on either side with
a fixed object is a left adjoint, is monoidal preadditive: whiskering on either side is additive.
This applies to closed braided monoidal categories. -/
theorem monoidalPreadditive_of_isLeftAdjoint (C : Type*) [Category* C] [Preadditive C]
    [HasBinaryCoproducts C] [MonoidalCategory C] [∀ X : C, (tensorLeft X).IsLeftAdjoint]
    [∀ X : C, (tensorRight X).IsLeftAdjoint] :
    MonoidalPreadditive C := by
  have : HasBinaryBiproducts C := .of_hasBinaryCoproducts
  have (X : C) : (tensorLeft X).Additive :=
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft X)
    Functor.additive_of_preservesBinaryBiproducts _
  have (X : C) : (tensorRight X).Additive :=
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight X)
    Functor.additive_of_preservesBinaryBiproducts _
  exact
    { whiskerLeft_zero := (tensorLeft _).map_zero _ _
      zero_whiskerRight := (tensorRight _).map_zero _ _
      whiskerLeft_add _ _ := (tensorLeft _).map_add
      add_whiskerRight _ _ := (tensorRight _).map_add }

end LeanCategories
