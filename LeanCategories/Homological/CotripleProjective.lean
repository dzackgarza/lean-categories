/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monad.Basic

/-!
# Projective objects for a cotriple

Weibel, *An Introduction to Homological Algebra*, Definition 8.6.5, pp. 278--285
(FC05-C08-U062).

Weibel's cotriple is Mathlib's `CategoryTheory.Comonad`.  An object is cotriple-projective exactly
when the component of the counit admits a section.  The source's following assertion that objects
in the image of the left adjoint are cotriple-projective is result-level and is deliberately not
included here.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Comonad

universe u v

variable {C : Type u} [Category.{v} C]

/-- An object `P` is projective relative to the cotriple `T` when the counit
`ε_P : T(P) ⟶ P` admits a section.

Source: Weibel, Definition 8.6.5, pp. 278--285 (FC05-C08-U062). -/
def IsCotripleProjective (T : Comonad C) (P : C) : Prop :=
  ∃ s : P ⟶ T.obj P, s ≫ T.ε.app P = 𝟙 P

end CategoryTheory.Comonad
