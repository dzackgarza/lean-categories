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

of the `p^k`-torsion filtration. Sweep III records that quotient carrier,
the displayed representative formula, and its graph with values in the
`p`-torsion subgroup of the value module. For the source value module `ℚ/ℤ`,
this is the target `p⁻¹ℤ/ℤ` displayed on printed page 188 of the June 2024
version. The source uses prime `p` and positive layer indices.
Representative-independence, totality and single-valuedness of the graph,
the finite-field target identification, and bilinearity are result-layer
obligations.
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

/-- The native `p`-torsion value subgroup used by the residue form.

For Peters--Sterk's value module `ℚ/ℤ`, this records the target
`p⁻¹ℤ/ℤ` in the paragraph preceding the formula on printed page 189.
The identification with the finite field, when `p` is prime, is not
part of this declaration. -/
def residueFormValueSubmoduleData (p : ℕ) : Submodule ℤ W :=
  Submodule.torsionBy ℤ W (p : ℤ)

/-- The graph of the residue-form formula with its specified torsion target.

This is the inverse image of `residueFormGraphData` under the inclusion
of the native `p`-torsion value subgroup. It keeps the actual quotient
classes and the complete representative equation, without choosing a
representative or requiring a proof that its value is killed by `p`.
Totality under the source hypotheses and single-valuedness remain results. -/
def residueFormTorsionGraphData (A : BilinModuleCat ℤ W) (p k : ℕ) :
    Set ((residueTorsionQuotientData A p k ×
      residueTorsionQuotientData A p k) ×
      residueFormValueSubmoduleData (W := W) p) :=
  {z | (z.1, (z.2 : W)) ∈ residueFormGraphData A p k}

end LeanCategories.Modules.Bilinear.Valued
