/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantAction
public import LeanCategories.Lattices.Valued.CuspDescent

/-!
# The isotropic subgroup `J_N = (N_ℚ ∩ L^∨)/N` of the discriminant form (#113 item 3)

For a primitive isotropic sublattice `N ⊆ L`, the subgroup of `A_L` carried by `N` is
`J_N = (N_ℚ ∩ L^∨)/N`: the rational span of `N` intersected with the dual lattice, modulo `N`. It is
not the dual of `N` — `N` is isotropic, so everything in `N_ℚ` pairs to zero with `N` and that dual
is all of `N_ℚ`.

The construction here avoids fraction-field scalars. Everything is an `R`-module: the dual lattice is
`metricDual R L`, the image `N'` of `N` is `N.toSubmodule.map (toMetricDual R L)`, and the rational
span intersected with `L^∨` is the *saturation* of `N'`,

`{x ∈ L^∨ | ∃ r ≠ 0, r • x ∈ N'}`,

which is `Sublattice.saturation N'` — the same construction that gives primitive closure in
`Sublattice.lean`, and its membership lemma `mem_saturation_iff` is what the isotropy argument
consumes. `metricDualToDiscriminant` then carries the saturation into `A_L = L.obj.defect`, and the
image is `J_N`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R] {L : IntegralLatticeCat R}

/-- The image of the primitive isotropic sublattice `N` in the dual lattice `L^∨`. -/
noncomputable abbrev metricDualImage {k : ℕ} (N : PrimitiveIsotropic L k) :
    Submodule R ↥(metricDual R L) :=
  N.toSubmodule.map (toMetricDual R L)

/-- `N_ℚ ∩ L^∨`: the saturation of the image of `N` in the dual lattice, i.e. the elements killed
into that image by a nonzero scalar. -/
noncomputable abbrev metricDualSaturation {k : ℕ} (N : PrimitiveIsotropic L k) :
    Submodule R ↥(metricDual R L) :=
  saturation (M := ↥(metricDual R L)) (metricDualImage N)

/-- `J_N = (N_ℚ ∩ L^∨)/N`, as a subgroup of the discriminant module `A_L`. -/
noncomputable abbrev isotropicSubgroup {k : ℕ} (N : PrimitiveIsotropic L k) :
    Submodule R L.obj.defect :=
  (metricDualSaturation N).map (metricDualToDiscriminant R L)

end LeanCategories.Lattices.Valued
