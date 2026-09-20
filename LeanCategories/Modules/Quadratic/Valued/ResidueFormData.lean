/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Torsion

/-!
# Quadratic residue-form representative data

Peters--Sterk FC11-C09-U021.

Only the native `p^k`-torsion layer and the displayed representative formula
are recorded here. Quotient descent, the `p^-1 Z/Z` target identification,
quadratic-form laws, and nonsingularity are result-layer obligations.
-/

@[expose] public section

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable {W : Type u} [AddCommGroup W] [Module ℤ W]

/-- The `p^k`-torsion layer used for the quadratic residue construction (FC11-C09-U021). -/
def quadraticResidueTorsionLayerData (Q : QuadModuleCat ℤ W) (p k : ℕ) :
    Submodule ℤ Q.carrier :=
  Submodule.torsionBy ℤ Q.carrier ((p : ℤ) ^ k)

/-- Peters--Sterk's representative formula `p^(k-1) q(x)` for the odd-prime quadratic residue form (FC11-C09-U021).

This is intentionally defined on representatives in the torsion layer; no
quotient descent or quadratic laws are bundled into Sweep III. -/
def quadraticResidueRepresentativeData (Q : QuadModuleCat ℤ W) (p k : ℕ)
    (x : quadraticResidueTorsionLayerData Q p k) : W :=
  ((p : ℤ) ^ (k - 1)) • Q.form x.1

end LeanCategories.Modules.Quadratic.Valued
