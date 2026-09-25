/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.AssociatedGraded
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Normal-flatness definition data

Definition-level realization of Matsumura FC13-C08-U041.

For an ideal `I` of a commutative ring `A` and an `A`-module `M`, the source
uses

`gr_I(M) = ⨁ n, I^n M / I^(n+1) M`

as a module over `A/I`, and defines normal flatness by flatness of this graded
module over `A/I`.

To expose the quotient-ring scalar action without proving a scalar-descent
theorem, each homogeneous piece is presented as

`(I^n M) / I • (I^n M)`.

This is the source's successive quotient presentation, with the lower term
written as multiplication by `I` on the degree-`n` term. Mathlib's existing
quotient-module constructor then supplies the `A/I`-module structure directly,
and the direct sum inherits it componentwise.

The local-ring equivalence with freeness of every homogeneous piece is result
content and is not asserted here.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace LeanCategories.Algebra

universe u v

variable {A : Type u} {M : Type v}
variable [CommRing A] [AddCommGroup M] [Module A M]

/-- The degree-`n` piece used for normal flatness:
`I^n M / I(I^n M)`, carrying its native `A/I`-module structure. -/
abbrev IAdicNormalFlatnessPieceData (I : Ideal A) (n : ℕ) :=
  let N : Submodule A M := I ^ n • ⊤
  N ⧸ I • (⊤ : Submodule A N)

/-- The associated graded carrier with the quotient-ring scalar structure
visible degreewise. -/
abbrev IAdicNormalFlatnessGradedModuleData (I : Ideal A) :=
  ⨁ n : ℕ, IAdicNormalFlatnessPieceData (M := M) I n

/-- Matsumura's normal-flatness predicate from FC13-C08-U041:
the `I`-adic associated graded module is flat over `A/I`. -/
def IsNormallyFlatAlongData (I : Ideal A) : Prop :=
  Module.Flat (A ⧸ I) (IAdicNormalFlatnessGradedModuleData (M := M) I)

end LeanCategories.Algebra
