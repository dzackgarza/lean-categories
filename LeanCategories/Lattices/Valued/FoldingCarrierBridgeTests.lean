/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingCarrierBridge
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for the carrier bridge

The bridge exists because the coercion does not: writing `(ρ : L.obj.obj.carrier)` for `ρ` at
`M^σ`'s carrier fails to elaborate. So what decides the bridge is that it *computes* — at the
hyperbolic plane's identity involution it must send the fixed root vector to the ambient root
vector, and it must commute with the integer multiple. A bridge that only type-checked would not
decide that.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The bridge sends the plane's fixed root vector to the ambient root vector. -/
example : invariantToAmbient (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRootFixed = uRoot := rfl

/-- The bridge commutes with `2 •` on that vector — the `ℤ`-linearity the transfer uses. -/
example : invariantToAmbient (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)
    ((2 : ℤ) • (show (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.carrier from uRootFixed))
      = (2 : ℤ) • uRoot := by
  rw [invariantToAmbient_zsmul]
  rfl

/-- The bridge sends the folded wall family to the folded vectors — the law the ambient-sign
composition needs to phrase an expansion of `M^σ`'s roots in `L`. -/
example : invariantToAmbient (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)
    (foldedWallFamily (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1)
      (fun _ : Fin 1 => uRoot) 0)
      = foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot := rfl

end LeanCategories.Lattices.Valued
