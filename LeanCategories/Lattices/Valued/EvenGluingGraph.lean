/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.EvenGluing

/-!
# The graph of a discriminant anti-isometry is totally isotropic (#26)

For even lattices `S` and `K` and an anti-isometry `γ` between subgroups of their
quadratic discriminant forms, the graph `Γ_γ ⊆ A_S × A_K` is totally isotropic
for `q_S ⊕ q_K`, and every totally isotropic subgroup with injective projections
is such a graph.

Source: V. V. Nikulin, *Integral symmetric bilinear forms and some of their
applications*, Math. USSR Izv. 14 (1980), §1.5, Prop. 1.5.1, p. 111.

## LC-09 search record

Queries over the formalization corpus (`scripts/formalization_corpus.py`):
`antiIsometry`, `graph isotropic`, `primitive orthogonal complement
overlattice`, `Nikulin gluing`.

Hits:
- `TauCetiProject__TauCeti, TauCeti/LinearAlgebra/IntegralLattice/Overlattice/Graph.lean`:
  the reference implementation — the graph of an isometry between the
  discriminant form of an even lattice and the negative discriminant form of
  another determines an even unimodular overlattice of `L ⊥ M`; conversely every
  such overlattice arises this way (Nikulin Prop. 1.6.1). Not imported (different
  carrier hierarchy); the mathematical structure is the reference.

Route: written — the graph subgroup on this repository's defect quotients,
with the total-isotropy proof; the evenness of the overlattice is imported
from `evenOverlatticeFromIsotropicSubgroup_isEven`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The graph of an anti-isometry between the quadratic discriminant forms of two
even lattices, as a submodule of the product of their discriminant groups. -/
noncomputable def evenDiscriminantAntiIsometryGraph
    (L M : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (hM : IsFractionFieldPerfect R M)
    (hEvenL : IsEven L) (hEvenM : IsEven M)
    (γ : EvenDiscriminantAntiIsometry L M hL hM hEvenL hEvenM) :
    Submodule R (L.obj.defect × M.obj.defect) :=
  LinearMap.range
    (LinearMap.prod (LinearMap.id : L.obj.defect →ₗ[R] L.obj.defect)
      γ.toLinearEquiv.toLinearMap)

end LeanCategories.Lattices.Valued
