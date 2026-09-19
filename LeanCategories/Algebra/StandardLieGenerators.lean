/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Set.Basic

/-!
# Standard Lie-generator sets

Humphreys FC14-C04-U004. The source has already chosen compatible simple-root
vectors `x_alpha`, `y_alpha` and Cartan elements `h_alpha`; this file records
only the two sets that are then named standard sets of generators.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v

/-- The standard generator set `{x_alpha,y_alpha}` after compatible choices. -/
def standardLieGeneratorSet {I : Type u} {L : Type v} (x y : I → L) : Set L :=
  Set.range x ∪ Set.range y

/-- The extended standard generator set `{x_alpha,y_alpha,h_alpha}`. -/
def standardLieGeneratorSetWithCartan {I : Type u} {L : Type v}
    (x y h : I → L) : Set L :=
  Set.range x ∪ Set.range y ∪ Set.range h

end LeanCategories.Algebra
