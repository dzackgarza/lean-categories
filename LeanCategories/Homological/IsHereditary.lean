/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Field.Opposite
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Hereditary rings

Weibel, *An Introduction to Homological Algebra*, Definition 4.2.10 (p. 95):

> A ring `R` is called *(right) hereditary* if every right ideal is projective.

Following Mathlib's convention for noncommutative rings, a right ideal of `R` is
a left ideal of the opposite ring `Rᵐᵒᵖ`, i.e. an element of `Ideal Rᵐᵒᵖ`.
Projectivity of such an ideal is therefore projectivity as a right `R`-module,
`Module.Projective Rᵐᵒᵖ I`.
-/

@[expose] public section

namespace LeanCategories.Homological

/-- A ring `R` is *right hereditary* if every right ideal of `R` is a projective
right `R`-module (Weibel, Definition 4.2.10). -/
def IsRightHereditary (R : Type*) [Ring R] : Prop :=
  ∀ I : Ideal Rᵐᵒᵖ, Module.Projective Rᵐᵒᵖ I

namespace IsRightHereditary

/-- Every module over a division ring has a basis, hence is projective, so every
division ring is right hereditary (Weibel p. 95: "any principal ideal domain ...
is hereditary, as is any commutative Dedekind domain", and a fortiori any
division ring). -/
theorem of_divisionRing (R : Type*) [DivisionRing R] : IsRightHereditary R := by
  intro I
  exact Module.Projective.of_basis (Module.Basis.ofVectorSpace Rᵐᵒᵖ I)

end IsRightHereditary

end LeanCategories.Homological
