/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingNegativeFourRoots
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for the `(−4)` criterion

The criterion says a `(−4)`-vector is a root exactly when all its pairings are even, so what decides
it is a vector of square `−4` whose pairing with a specific vector is *computed* to be odd:
`(1, −2)` in the hyperbolic plane, where the pairing is `x₀y₁ + x₁y₀`, has square `−4` and odd
pairing with `(0, 1)`. That is exactly the type (3) situation — square `−4`, divisibility not `2` —
and the criterion must refuse to call it a root.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- `(1, -2)` has square `-4` and odd pairing with `(0, 1)`, so it is not a root — the type (3)
situation. -/
example : ¬ IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj
    (show hyperbolicPlaneFiniteLattice.obj.obj.carrier from (![1, -2] : Fin 2 → ℤ)) := by
  rw [isReflectiveRoot_iff_two_dvd_pairing (L := hyperbolicPlaneFiniteLattice)
    (x := (show hyperbolicPlaneFiniteLattice.obj.obj.carrier
      from (![1, -2] : Fin 2 → ℤ))) ?_]
  · intro h
    have h1 := h (show hyperbolicPlaneFiniteLattice.obj.obj.carrier
      from (![0, 1] : Fin 2 → ℤ))
    rw [u_pairing_eq'] at h1
    norm_num at h1
  · rw [u_pairing_eq']
    norm_num

end LeanCategories.Lattices.Valued
