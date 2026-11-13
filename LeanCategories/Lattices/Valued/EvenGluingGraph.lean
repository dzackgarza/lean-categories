/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.EvenGluing

/-!
# The orthogonal-sum discriminant splitting for the graph of an anti-isometry (#26)

For even lattices `S` and `K`, the discriminant group of the orthogonal sum `S ⊥ K`
splits as the product `A_S × A_K` of the two discriminant groups: a functional on the
product carrier restricts along the two coordinate inclusions. This file constructs the
two restriction maps and proves the adjoint laws they satisfy — the adjoint of the
orthogonal sum restricts, along each coordinate inclusion, to the adjoint of the
corresponding factor — and defines the graph of an anti-isometry between the quadratic
discriminant forms as a submodule of the product of the two defect quotients.

This file proves only those restriction laws and defines the graph subgroup. The
defect-quotient equivalence the restrictions induce, the transport of the quadratic
discriminant form along it — the total isotropy of the graph inside the discriminant
form of `S ⊥ K`, the overlattice the graph determines, its discriminant form
`Γ^⊥/Γ`, and the primitive embedding of the two factors — is not proved here; those are
the remaining results of #26 and are not claimed by this module.

Source: V. V. Nikulin, *Integral symmetric bilinear forms and some of their
applications*, Math. USSR Izv. 14 (1980), §1.5, Prop. 1.5.1, p. 111.

## Port provenance

Ported, with the definitions and proofs adapted to this repository's carriers, from
`TauCetiProject/TauCeti` (Apache 2.0, © The Tau Ceti contributors):

* `TauCeti/LinearAlgebra/IntegralLattice/Overlattice/Graph.lean`
  (`TauCeti.IntegralLattice.discriminantGraph`, `mem_discriminantGraph_iff`): the graph
  of an isometry between the discriminant form of an even lattice and the negative
  discriminant form of another, transported to the discriminant group of the orthogonal
  sum along TauCeti's `discriminantGroupOrthogonalSumEquiv`. The port replaces TauCeti's
  carrier hierarchy (`IntegralLattice V` over a rational space `V`, with dual-carrier
  submodules and `Lᵛ`-indexed intermediate carriers) by this repository's
  `IntegralLatticeCat R` (a `BilinModuleCat R R` whose defect is the cokernel of the
  adjoint `L.carrier →ₗ Hom(L.carrier, R)`), and TauCeti's `discriminantGraph` transport
  by the splitting constructed here.

## LC-09 search record

Queries over the formalization corpus (`scripts/formalization_corpus.py`):
`file:Overlattice/Graph.lean repo:TauCeti`, `file:Overlattice/Isotropic.lean repo:TauCeti`,
`file:Overlattice/Basic.lean repo:TauCeti`, `file:Overlattice/Dual.lean repo:TauCeti`,
`file:Overlattice/OrthogonalQuotient/OrthogonalSum.lean repo:TauCeti`,
`file:Overlattice/OrthogonalQuotient/Quadratic.lean repo:TauCeti`.

Hits: the six files of `TauCeti/LinearAlgebra/IntegralLattice/Overlattice/` hold the
whole reference theory — the graph (`Graph.lean`), the isotropic-subgroup overlattice
correspondence (`Isotropic.lean`), the intermediate-carrier machinery (`Basic.lean`),
the dual-carrier splitting (`Dual.lean`), and the orthogonal-quotient comparison
`A_(P ⊕ Q) ≅ (H⊥ / H) ⊥ (K⊥ / K)` (`OrthogonalQuotient/OrthogonalSum.lean`,
`OrthogonalQuotient/Quadratic.lean`). The reference implementation is ported above at
the level this repository's carriers support: the graph subgroup and the defect
splitting. The residue the carriers do not yet supply — the quadratic-form transport
along the splitting, which the total-isotropy, overlattice, discriminant-form and
primitive-embedding results all need — is recorded here and remains open; no result of
#26 is claimed for it.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

variable (L M : IntegralLatticeCat R)

/-- The first-coordinate restriction of a functional on the orthogonal-sum carrier:
the map `f ↦ f ∘ inl` into the value dual of the first factor. -/
def evenDiscriminantFstRestriction :
    (orthogonalSum L M).obj.valueDual →ₗ[R] L.obj.valueDual where
  toFun f := f.comp (LinearMap.inl R L.obj.carrier M.obj.carrier)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The second-coordinate restriction of a functional on the orthogonal-sum carrier:
the map `f ↦ f ∘ inr` into the value dual of the second factor. -/
def evenDiscriminantSndRestriction :
    (orthogonalSum L M).obj.valueDual →ₗ[R] M.obj.valueDual where
  toFun f := f.comp (LinearMap.inr R L.obj.carrier M.obj.carrier)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsDomain R] in
/-- The adjoint of the orthogonal sum restricts to the adjoint on the first coordinate:
a functional of the form `z ↦ S.pairing a z₁ + K.pairing b z₂` restricts along the first
coordinate inclusion to `x ↦ S.pairing a x`, the adjoint of `a`. -/
theorem evenDiscriminantFstRestriction_adjoint
    (a : L.obj.carrier) (b : M.obj.carrier) :
    evenDiscriminantFstRestriction L M ((orthogonalSum L M).obj.adjoint (a, b)) =
      L.obj.adjoint a := by
  ext x
  change (orthogonalSum L M).obj.pairing (a, b) (x, 0) = L.obj.pairing a x
  rw [orthogonalSum_pairing]
  simp

omit [IsDomain R] in
/-- The adjoint of the orthogonal sum restricts to the adjoint on the second coordinate:
the same functional restricts along the second coordinate inclusion to
`y ↦ K.pairing b y`, the adjoint of `b`. -/
theorem evenDiscriminantSndRestriction_adjoint
    (a : L.obj.carrier) (b : M.obj.carrier) :
    evenDiscriminantSndRestriction L M ((orthogonalSum L M).obj.adjoint (a, b)) =
      M.obj.adjoint b := by
  ext x
  change (orthogonalSum L M).obj.pairing (a, b) (0, x) = M.obj.pairing b x
  rw [orthogonalSum_pairing]
  simp

/-- The graph of an anti-isometry between the quadratic discriminant forms of two
even lattices, as a submodule of the product of their discriminant groups. -/
noncomputable def evenDiscriminantAntiIsometryGraph
    (hL : IsFractionFieldPerfect R L) (hM : IsFractionFieldPerfect R M)
    (hEvenL : IsEven L) (hEvenM : IsEven M)
    (γ : EvenDiscriminantAntiIsometry L M hL hM hEvenL hEvenM) :
    Submodule R (L.obj.defect × M.obj.defect) :=
  LinearMap.range
    (LinearMap.prod (LinearMap.id : L.obj.defect →ₗ[R] L.obj.defect)
      γ.toLinearEquiv.toLinearMap)

/-! ## The defect splitting of the orthogonal sum

Ported from `TauCeti/LinearAlgebra/IntegralLattice/Overlattice/Graph.lean`
(`TauCeti.IntegralLattice.discriminantGraph`): the transport of the graph along the
orthogonal-sum splitting of the discriminant groups. The splitting is built here from
the two coordinate restrictions and the adjoint laws above, which play the role of
TauCeti's `discriminantGroupOrthogonalSumEquiv`. -/

/-- The map on the two defect quotients induced by the coordinate restrictions: a
functional on the orthogonal-sum carrier is sent to the pair of its two coordinate
classes. -/
def evenDiscriminantRestrictionMap :
    (orthogonalSum L M).obj.valueDual →ₗ[R] L.obj.defect × M.obj.defect :=
  LinearMap.prod
    (L.obj.defectProjection.comp (evenDiscriminantFstRestriction L M))
    (M.obj.defectProjection.comp (evenDiscriminantSndRestriction L M))

omit [IsDomain R] in
/-- The adjoint range of the orthogonal sum lies in the kernel of the restriction map:
each coordinate class of an adjoint functional is zero, by the two adjoint laws and the
quotient projections killing their own submodules. -/
theorem evenDiscriminantRestrictionMap_adjointRange_le_ker :
    LinearMap.range (orthogonalSum L M).obj.adjoint ≤
      LinearMap.ker (evenDiscriminantRestrictionMap L M) := by
  rintro f ⟨⟨a, b⟩, rfl⟩
  rw [LinearMap.mem_ker]
  have h1 : L.obj.defectProjection (L.obj.adjoint a) = 0 := by
    change Submodule.Quotient.mk (L.obj.adjoint a) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ _
  have h2 : M.obj.defectProjection (M.obj.adjoint b) = 0 := by
    change Submodule.Quotient.mk (M.obj.adjoint b) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ _
  have hmap : (evenDiscriminantRestrictionMap L M) ((orthogonalSum L M).obj.adjoint (a, b)) =
      (L.obj.defectProjection (evenDiscriminantFstRestriction L M ((orthogonalSum L M).obj.adjoint (a, b))),
       M.obj.defectProjection (evenDiscriminantSndRestriction L M ((orthogonalSum L M).obj.adjoint (a, b)))) := rfl
  rw [hmap, evenDiscriminantFstRestriction_adjoint L M, evenDiscriminantSndRestriction_adjoint L M]
  exact Prod.ext h1 h2

end LeanCategories.Lattices.Valued

#print axioms LeanCategories.Lattices.Valued.evenDiscriminantFstRestriction
#print axioms LeanCategories.Lattices.Valued.evenDiscriminantFstRestriction_adjoint
#print axioms LeanCategories.Lattices.Valued.evenDiscriminantSndRestriction
#print axioms LeanCategories.Lattices.Valued.evenDiscriminantSndRestriction_adjoint
#print axioms LeanCategories.Lattices.Valued.evenDiscriminantAntiIsometryGraph
