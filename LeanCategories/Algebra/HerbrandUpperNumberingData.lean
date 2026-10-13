/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.LowerRamificationData

/-!
# Herbrand inverse and upper-numbering data

Definition-level realization of Neukirch FC09-C02-U133.

The source enters this construction with the Herbrand function
`η_{L/K}` already named.  It defines its inverse `ψ_{L/K}` and then
reindexes the lower ramification filtration by

`G^t = G_{ψ(t)}`.

The checked ClassFieldTheory reference uses exactly `Function.invFun` for
the inverse Herbrand function and defines upper ramification by evaluation of
the lower filtration at that inverse.  Sweep III ports precisely those two
definitions.

The source restricts the displayed inverse to `[-1,∞)`; as in the checked
reference and the local lower-filtration owner, the definitions below are
total on `ℝ`.  The facts that the Herbrand function is strictly increasing
and surjective, that the two functions are mutual inverses, and that the
inverse preserves `[-1,∞)` are result-layer statements.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe uK uL

/-- Neukirch's inverse Herbrand function `ψ = η⁻¹`, at the raw
definition level.

Using `Function.invFun` does not require the injectivity or surjectivity
proofs.  Those theorems later establish that this selected inverse has the
source's intended two-sided inverse behavior. -/
def inverseHerbrandFunctionData (η : ℝ → ℝ) : ℝ → ℝ :=
  Function.invFun η

variable
  (K : Type uK) {L : Type uL}
  [Field K] [Field L] [Algebra K L]

/-- Neukirch's upper numbering `G^t = G_{ψ(t)}`, using the raw lower
ramification carrier already realized in FC09-C02-U125.

No inverse law or filtration property is required to form this set. -/
def upperRamificationSetData
    (v : AddValuation L (WithTop ℤ))
    (G : Subgroup (L ≃ₐ[K] L))
    (η : ℝ → ℝ) (t : ℝ) : Set G :=
  lowerRamificationSet K v G (inverseHerbrandFunctionData η t)

end LeanCategories.Algebra
