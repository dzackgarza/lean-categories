/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Integral Chevalley-form carrier

Definition-level realization of Humphreys FC14-C07-U008.  Once U005 has
supplied the Chevalley-basis carrier, its integral form is the
`ℤ`-submodule spanned by that carrier.

Freeness, closure under the Lie bracket, spanning the ambient Lie algebra
over the ground field, and independence of the chosen base/Chevalley basis
are result content and are not included here.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

/-- The underlying `ℤ`-span `L(ℤ)` of a supplied Chevalley-basis carrier. -/
def integralChevalleySpan {L : Type u} [AddCommGroup L] (B : Set L) :
    Submodule ℤ L :=
  Submodule.span ℤ B

end LeanCategories.Algebra
