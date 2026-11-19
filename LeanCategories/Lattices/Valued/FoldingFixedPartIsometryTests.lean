/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingFixedPartIsometry
public import LeanCategories.Lattices.Valued.FoldingWitness
public import LeanCategories.Lattices.Valued.FoldingDiagram

/-!
# Probes for `FoldingFixedPartIsometry`, on the smallest input that decides it

The two lemmas say the bridge is form-preserving on pure tensors. They are decided on the worked
involution of the hyperbolic plane at the root `e - f`: `1 ⊗ (e - f)` has quadratic value `-2` and
`2 ⊗ (e - f)` has `4 · (-2) = -8`, which also shows the scalars are not lost.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The quadratic form of the bridge at `1 ⊗ (e - f)` is the root's square. -/
example : realFormQuadratic hyperbolicPlaneFiniteLattice
    (invariantToAmbient (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) ((1 : ℝ) ⊗ₜ[ℤ] uRootFixed))
      = -2 := by
  rw [invariantToAmbient_qf_tmul]
  have hsq : hyperbolicPlaneFiniteLattice.obj.obj.pairing
      (uRootFixed : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
      (uRootFixed : hyperbolicPlaneFiniteLattice.obj.obj.carrier) = -2 := uRoot_square
  rw [hsq]
  norm_num

/-- At `2 ⊗ (e - f)` the scalar appears squared. -/
example : realFormQuadratic hyperbolicPlaneFiniteLattice
    (invariantToAmbient (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) ((2 : ℝ) ⊗ₜ[ℤ] uRootFixed))
      = -8 := by
  rw [invariantToAmbient_qf_tmul]
  have hsq : hyperbolicPlaneFiniteLattice.obj.obj.pairing
      (uRootFixed : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
      (uRootFixed : hyperbolicPlaneFiniteLattice.obj.obj.carrier) = -2 := uRoot_square
  rw [hsq]
  norm_num

#print axioms invariantToAmbient_pairing_tmul
#print axioms invariantToAmbient_qf_tmul

end LeanCategories.Lattices.Valued
