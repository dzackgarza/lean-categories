/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Torsion
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Dyadic doubling data

Peters--Sterk FC11-C09-U023.

Sweep III records the native quotient carrier `G/G[2]` and the displayed
representative value `b(x,x)`. Descent to a function on the quotient, the
quadratic-map laws, the polar-form identity, and nonsingularity are result
content.
-/

@[expose] public section

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable {W : Type u} [AddCommGroup W] [Module ℤ W]

/-- The order-two torsion subgroup `G₁ = G[2]` in the dyadic doubling
construction (FC11-C09-U023). -/
def dyadicDoublingKernelData (A : BilinModuleCat ℤ W) :
    Submodule ℤ A.carrier :=
  Submodule.torsionBy ℤ A.carrier (2 : ℤ)

/-- The raw doubling carrier `2G = G/G₁` (FC11-C09-U023). -/
abbrev dyadicDoublingCarrierData (A : BilinModuleCat ℤ W) :=
  A.carrier ⧸ dyadicDoublingKernelData A

/-- The representative-level diagonal value `b(x,x)` used to define
`q([x])` in the doubling construction (FC11-C09-U023).

Well-definedness on `G/G₁` and the quadratic laws are intentionally not
bundled into this Sweep-III datum. -/
def dyadicDoublingRepresentativeValueData (A : BilinModuleCat ℤ W)
    (x : A.carrier) : W :=
  A.pairing x x

end LeanCategories.Modules.Bilinear.Valued
