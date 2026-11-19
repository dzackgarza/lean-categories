/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.Sublattice

/-!
# A lattice built by `ofBilinMap` keeps its carrier's instances (`#116`)

The obstruction recorded in `results/issue-116-report.md` is that the carrier of a **formed
sublattice** carries its group and module structure as fields of the bundled category
(`isAddCommGroup`, `isModule`), while a submodule's are type-class instances — so facts about one
cannot be transported to the other, and `inferInstance` on the formed side times out.

`BilinModuleCat.ofBilinMap` does *not* have that defect: it is built on the domain type of a
bilinear map, so its carrier *is* that type with its own instances. This file records that, as
the presentation the signature and the fixed-part bridge should use.

* `ofBilinMap_projective` — projectivity of the carrier of `ofBilinMap f` from projectivity of the
  ambient type, with no instance search: the two types are the same;

No source to cite: instance bookkeeping about `BilinModuleCat` (`Fixed.lean`), not a statement
of the paper.

## LC-09 record

`rg "ofBilinMap"` gives `Fixed.lean` (the constructor), `Standard.lean` (`hyperbolicPlane`,
`e8Lattice` built that way) and `FoldingEnriques.lean` (`tdpLattice`) — all on model carriers.
The formed-sublattice route (`Sublattice.lean:245`) is the one that loses the instances. Nothing
ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- **A lattice built by `ofBilinMap` has its domain's carrier**, so its projectivity is the
domain's, with no instance search. -/
theorem ofBilinMap_projective {M : Type} [AddCommGroup M] [Module ℤ M]
    (f : LinearMap.BilinMap ℤ M ℤ) (hM : Module.Projective ℤ M) :
    Module.Projective ℤ (BilinModuleCat.ofBilinMap f).carrier :=
  hM

end LeanCategories.Lattices.Valued
