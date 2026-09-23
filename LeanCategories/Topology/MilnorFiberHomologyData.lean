/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.MilnorFiberData
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Integral middle homology of the Milnor fibre

Supporting construction for Peters--Sterk FC11-C18-U025, Version JUNE 2024,
printed p. 333. This is native integral singular homology of the actual
fibre subspace, not a caller-supplied module or a free module of chosen rank.

The geometric intersection pairing induced by the complex orientation
has not yet been constructed. In particular, this module alone is not
credited as the source's Milnor lattice. No arbitrary bilinear form or
fundamental-evaluation map is accepted as a substitute.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

/-- The integral middle homology of the constructed Milnor fibre. The
source's freeness and rank computation are separate result statements. -/
def milnorIntegralMiddleHomologyData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (η : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r) : ModuleCat.{0} ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of (MilnorFiberData f η t))

end LeanCategories.Topology
