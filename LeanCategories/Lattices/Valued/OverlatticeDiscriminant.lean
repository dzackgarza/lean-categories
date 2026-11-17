/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.OverlatticeLattice

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-!
# The discriminant of an overlattice, inside the discriminant of the lattice below it

Nikulin, *Integral symmetric bilinear forms and some of their applications*, Math. USSR Izv. 14
(1980), §1.5, Prop. 1.5.1, p. 111: for the overlattice `M` of `L` attached to a totally isotropic
subgroup `Γ ⊆ A_L` (`Gluing.overlatticeFromIsotropicSubgroup`), the discriminant group of `M` is
`Γ^⊥/Γ` — the quotient of the orthogonal complement of `Γ` inside `A_L` by `Γ` itself. This is
#26's third result, and it needs `A_M = M^∨/M` to exist, which is what `Overlattice.lattice`
(`OverlatticeLattice.lean`) supplies.

## What is proved here

The class map of an overlattice: a vector `x` of the metric dual `M^∨ = dualSubmodule M.carrier`
pairs integrally with all of `M`, hence in particular with `L`, so its discriminant class `[x]`
lives in `A_L`; and it pairs integrally with `M`'s preimage in `A_L`, so `[x]` lies in `Γ^⊥`.
That is `Overlattice.discMap` and `Overlattice.discMap_mem_glueOrthogonal` — the map and its
inclusion into the orthogonal complement of the gluing subgroup.

The two remaining steps are the kernel/range identification
(`ker discMap = M`, giving injectivity after quotienting, and `range discMap ⊇ Γ^⊥`, giving
surjectivity) and their assembly into `M^∨/M ≃ₗ Γ^⊥/Γ`. The mathematics of both is settled and
written out in `COMPLAINTS.md`; what is missing is Lean: the quotient `A_L ⧸ M.glueSubgroup` as the
*codomain of a linear map*, i.e. the definition

```lean
noncomputable def discPsi : ↥M.dualSubmodule →ₗ[R] (L.obj.defect ⧸ M.glueSubgroup)
```

diverges in `whnf` in a file of this size, while the same definition elaborates in a file with
three declarations. `COMPLAINTS.md` records the exact terms and the reproducible contrast. That is
the same `defeq`-at-`abbrev` divergence as the one #26 hit in `OrthogonalSumDiscriminant.lean`,
whose resolution was to prove the transport without the offending term at all; the same resolution
is what the kernel/range step needs, and it is not found yet.

## Provenance

No Mathlib or TauCeti statement is ported: `discMap` is this repository's own
`metricDualToValueDual`/`defectProjection` API, and TauCeti states the analogous fact only through
its `intermediateCarrierOfDiscriminantSubgroup` machinery, which has no counterpart here.
-/

namespace Overlattice

variable {L : IntegralLatticeCat R}
variable {M : Overlattice R L}

/-- **The discriminant class map of an overlattice**: a vector of `M^∨` defines a functional on
the ambient lattice by integral pairing, hence a class in `A_L`. -/
noncomputable def discMap : ↥M.dualSubmodule →ₗ[R] L.obj.defect :=
  (BilinModuleCat.defectProjection L.obj).comp
    ((metricDualToValueDual R L).comp (Submodule.inclusion M.dualSubmodule_le_metricDual))

/-- The class of a dual vector is the discriminant class of its metric-dual representative. -/
theorem discMap_apply (x : ↥M.dualSubmodule) :
    discMap x = metricDualToDiscriminant R L
      ⟨x.1, M.dualSubmodule_le_metricDual x.2⟩ := rfl

/-- The orthogonal complement, inside the discriminant form of `L`, of the gluing subgroup `M/L`. -/
noncomputable def glueOrthogonal (hL : IsFractionFieldPerfect R L) : Submodule R L.obj.defect :=
  (discriminantBilinObject R L hL).orthogonalSubmodule M.glueSubgroup

/-- **The class map lands in `Γ^⊥`**: a dual vector of `M` pairs integrally with every element of
`M`, so its class is orthogonal to the gluing subgroup `Γ = M/L`. This is the first half of
`A_M ≅ Γ^⊥/Γ`. -/
theorem discMap_mem_glueOrthogonal (hL : IsFractionFieldPerfect R L)
    (x : ↥M.dualSubmodule) : discMap x ∈ glueOrthogonal (M := M) hL := by
  rw [glueOrthogonal]
  show ∀ p ∈ M.glueSubgroup,
    (discriminantBilinObject R L hL).pairing p (discMap x) = 0
  rintro p ⟨m, rfl⟩
  rw [LinearMap.comp_apply, discMap_apply, discriminant_pairing_metricDualToDiscriminant]
  have hmem : rationalizedForm R L (m : RationalSpan R L) (x : RationalSpan R L) ∈
      (1 : Submodule R (FractionRing R)) := by
    rw [rationalizedForm_isSymmetric R L]
    exact x.2 m.1 m.2
  rw [Submodule.mem_one] at hmem
  obtain ⟨r, hr⟩ := hmem
  change fractionValueProjection R
    (rationalizedForm R L (m : RationalSpan R L) (x : RationalSpan R L)) = 0
  rw [← hr, fractionValueProjection_algebraMap]

end Overlattice

end LeanCategories.Lattices.Valued
