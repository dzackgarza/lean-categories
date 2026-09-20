/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Torsion

/-!
# Residue-form representative data

Peters--Sterk FC11-C09-U017.

The source defines the residue form on a quotient of the `p^k`-torsion
layer. Sweep III records the layer and the displayed representative formula
only. Representative-independence, descent to the quotient, the finite-field
target identification, and bilinearity are result-layer obligations.
-/

@[expose] public section

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable {W : Type u} [AddCommGroup W] [Module ℤ W]

/-- The `p^k`-torsion layer `G_k` used in Peters--Sterk FC11-C09-U017. -/
def residueTorsionLayerData (A : BilinModuleCat ℤ W) (p k : ℕ) :
    Submodule ℤ A.carrier :=
  Submodule.torsionBy ℤ A.carrier ((p : ℤ) ^ k)

/-- Peters--Sterk's representative formula
`p^(k-1) b(x,y)` for the residue form `rho_k(b)` (FC11-C09-U017).

This is intentionally a function on representatives in `G_k`; no quotient
descent or form laws are bundled into the declaration. -/
def residueFormRepresentativeData (A : BilinModuleCat ℤ W) (p k : ℕ)
    (x y : residueTorsionLayerData A p k) : W :=
  ((p : ℤ) ^ (k - 1)) • A.pairing x.1 y.1

end LeanCategories.Modules.Bilinear.Valued
