/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Ring.Defs

/-!
# Von Neumann regular rings

Weibel, *An Introduction to Homological Algebra*, §4.2 (FC05-C04-U022).
-/

@[expose] public section

namespace LeanCategories.Homological

/-- A ring `R` is von Neumann regular when every `a : R` has an inner inverse:
there is `x : R` with `a * x * a = a`. -/
def IsVonNeumannRegular (R : Type*) [Ring R] : Prop :=
  ∀ a : R, ∃ x : R, a * x * a = a

end LeanCategories.Homological
