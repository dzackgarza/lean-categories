/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingTdpHsubFails

/-!
# Probe: `hsub` fails for the `T_dP` folding

The two halves are already proved separately; this decides the assembled statement, which is what
AEGS assert as `div(α^I) ≠ 2` (**printed p. 12**). The probe needs no hypothesis: the projectivity
instance for the fixed sublattice is supplied in the module by a `show` transport across the
bundled carrier — direct instance search fails there because `Module.IsTorsionFree` does not
synthesize at that type.

The second probe is the general projectivity fact itself, stated over a plain carrier where it does
synthesize.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The general fact: a submodule of a finite free `ℤ`-module is projective. -/
example (P : Submodule ℤ (Fin 3 → ℤ)) : Module.Projective ℤ ↥P :=
  submodule_projective P

/-- `hsub` fails for the `T_dP` folding. -/
example :
    ¬ ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry),
        invariantCarrierToAmbient (L := tdpFiniteLattice) tdpIsometry ρ ∈
          negativeReflectiveRoots tdpFiniteLattice :=
  tdp_hsub_fails

end LeanCategories.Lattices.Valued
