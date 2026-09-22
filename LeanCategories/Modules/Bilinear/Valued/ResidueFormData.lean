/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Torsion

/-!
# Residue-form representative data

Peters--Sterk FC11-C09-U017.

The source defines the residue form on the quotient

`G_k / (G_{k-1} + p G_{k+1})`

of the `p^k`-torsion filtration. Sweep III records that quotient carrier and
the displayed representative formula. Representative-independence, descent
of the formula to the quotient, the finite-field target identification, and
bilinearity are result-layer obligations.
-/

@[expose] public section

namespace LeanCategories.Modules.Bilinear.Valued

variable {W : Type} [AddCommGroup W] [Module ℤ W]

/-- The `p^k`-torsion layer `G_k` used in Peters--Sterk FC11-C09-U017. -/
def residueTorsionLayerData (A : BilinModuleCat ℤ W) (p k : ℕ) :
    Submodule ℤ A.carrier :=
  Submodule.torsionBy ℤ A.carrier ((p : ℤ) ^ k)

-- Keep the native submodule action when forming the denominator and quotient.
-- The additive-group-derived integer module is not definitionally the same
-- instance as the one used by the native submodule inclusion.
local instance residueTorsionLayerModule (A : BilinModuleCat ℤ W) (p k : ℕ) :
    Module ℤ (residueTorsionLayerData A p k) :=
  (residueTorsionLayerData A p k).module

/-- The denominator `G_{k-1} + p G_{k+1}`, regarded as a submodule of
`G_k`.

The `comap` presentation records the source denominator without requiring a
separate containment proof in the constructor: it consists of exactly those
elements of `G_k` whose ambient values lie in the displayed sum. -/
def residueTorsionDenominatorData (A : BilinModuleCat ℤ W) (p k : ℕ) :
    Submodule ℤ (residueTorsionLayerData A p k) :=
  ((residueTorsionLayerData A p (k - 1)) ⊔
      (residueTorsionLayerData A p (k + 1)).map
        ((p : ℤ) • LinearMap.id)).comap
    (residueTorsionLayerData A p k).subtype

/-- Peters--Sterk's residue module
`rho_k(G) = G_k / (G_{k-1} + p G_{k+1})`. -/
abbrev residueTorsionQuotientData (A : BilinModuleCat ℤ W) (p k : ℕ) :=
  (residueTorsionLayerData A p k) ⧸
    residueTorsionDenominatorData A p k

/-- The coset `[x]` of a representative `x ∈ G_k` in `rho_k(G)`. -/
def residueTorsionClassData (A : BilinModuleCat ℤ W) (p k : ℕ)
    (x : residueTorsionLayerData A p k) :
    residueTorsionQuotientData A p k :=
  Submodule.Quotient.mk x

/-- Peters--Sterk's representative formula
`p^(k-1) b(x,y)` for the residue form `rho_k(b)` (FC11-C09-U017).

This is intentionally a function on representatives in `G_k`; no quotient
descent or form laws are bundled into the declaration. -/
def residueFormRepresentativeData (A : BilinModuleCat ℤ W) (p k : ℕ)
    (x y : residueTorsionLayerData A p k) : W :=
  ((p : ℤ) ^ (k - 1)) • A.pairing x.1 y.1

/-- The representative-defined graph of Peters--Sterk's residue form
`rho_k(b)([x],[y]) = p^(k-1) b(x,y)` (FC11-C09-U017).

The first two coordinates are actual classes in `rho_k(G)`, not supplied
representatives of an unspecified quotient. The graph is the range of the
displayed formula on all representative pairs. Its single-valuedness,
identification of the value subgroup with `F_p`, and bilinearity are not
assumed or proved here. In particular, this construction makes no arbitrary
choice of representatives and asks for no quotient-descent witness. -/
def residueFormGraphData (A : BilinModuleCat ℤ W) (p k : ℕ) :
    Set ((residueTorsionQuotientData A p k ×
      residueTorsionQuotientData A p k) × W) :=
  Set.range fun xy : residueTorsionLayerData A p k ×
      residueTorsionLayerData A p k ↦
    ((residueTorsionClassData A p k xy.1,
      residueTorsionClassData A p k xy.2),
      residueFormRepresentativeData A p k xy.1 xy.2)

end LeanCategories.Modules.Bilinear.Valued
