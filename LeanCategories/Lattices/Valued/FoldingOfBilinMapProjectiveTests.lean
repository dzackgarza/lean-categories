/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingOfBilinMapProjective
public import LeanCategories.Lattices.Valued.Standard

/-!
# Probe for `ofBilinMap_projective`, on the smallest input that decides it

The lemma is about instances, so what decides it is that the transfer actually goes through
where the formed-sublattice route times out: the restricted hyperbolic form on `⊤`, whose carrier
is the model `Fin 2 → ℤ` with its own instances.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- A lattice built by `ofBilinMap` keeps its carrier's projectivity — here from the hyperbolic
plane's Gram matrix on the model carrier `Fin 2 → ℤ`, which is free. -/
example : Module.Projective ℤ
    (BilinModuleCat.ofBilinMap (Matrix.toBilin' hyperbolicPlaneGramMatrix)).carrier :=
  ofBilinMap_projective _ inferInstance


end LeanCategories.Lattices.Valued
