/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Loop

/-!
# Current Lie algebras

Weibel, *An Introduction to Homological Algebra* (1994), §7.9, pp. 248--253
(FC05-C07-U073).

The current Lie algebra is `g[t,t⁻¹] = g ⊗ₖ k[t,t⁻¹]`.  Mathlib's loop algebra
is precisely this Laurent-polynomial base change (implemented as an
`AddMonoidAlgebra` tensor product), with a supplied equivalence to Laurent
polynomials.

The base-change comparison for Chevalley--Eilenberg homology, perfectness, and
the claims about `H₁` and `H₂` are theorem-layer statements and are not asserted
here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open scoped TensorProduct

universe u v

variable (k : Type u) [CommRing k]
variable (L : Type v) [LieRing L] [LieAlgebra k L]

/-- Weibel's current Lie algebra `L[t,t⁻¹]`. -/
abbrev CurrentLieAlgebra := LieAlgebra.loopAlgebra k ℤ L

/-- Identification of the current algebra with the Laurent-polynomial tensor
product model used in the source. -/
def currentLieAlgebraEquivLaurent :
    CurrentLieAlgebra k L ≃ₗ⁅k⁆ LaurentPolynomial k ⊗[k] L :=
  LieAlgebra.loopAlgebraEquivLaurent k L

end LeanCategories.Homological
