/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingFixedPartBridge
public import LeanCategories.Lattices.Valued.FoldingWitness

/-!
# Probes for the fixed-part bridge, on the smallest input that decides it

`FoldingFixedPartBridge` identifies the invariant part of the real form, `M^σ ⊗ ℝ`, with the tensor
of the fixed lattice over `ℝ`. Three things decide it, on the hyperbolic plane at the identity
involution, where every carrier is the whole lattice:

* a fixed point of the real form is a real combination of fixed lattice vectors
  (`realFormFixedPart_eq_span`), so the fixed part is not smaller than that span;
* the tensor-level map lands in the fixed part and computes on a pure tensor
  (`invariantToAmbient_tmul`);
* its range is the fixed part (`invariantToAmbient_range`), which is the half that needs the
  averaging argument.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- A pure tensor computes as the scalar times the image of the lattice vector. -/
example [Module.Projective ℤ (involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry)]
    (r : ℝ) (v : involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry) :
    invariantToAmbient tdpIsometry ((r : ℝ) ⊗ₜ[ℤ] v)
      = r • toRealForm tdpFiniteLattice (v : tdpFiniteLattice.obj.obj.carrier) :=
  invariantToAmbient_tmul tdpIsometry r v

/-- The range of the tensor-level map is the invariant part of the real form. -/
example [Module.Projective ℤ (involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry)] :
    LinearMap.range (invariantToAmbient tdpIsometry) = realFormFixedPart tdpIsometry :=
  invariantToAmbient_range tdpIsometry tdpIsometry_mul_self

#print axioms invariantToAmbient_tmul
#print axioms invariantToAmbient_range

end LeanCategories.Lattices.Valued
