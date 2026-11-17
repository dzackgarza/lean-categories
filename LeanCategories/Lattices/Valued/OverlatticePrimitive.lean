
/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.OverlatticeLattice
public import LeanCategories.Lattices.Valued.OrthogonalSumDiscriminant
public import LeanCategories.Lattices.Valued.Sublattice

/-!
# The two factors of an overlattice of `S ⊥ K` are primitive, and each is the other's complement

Nikulin, *Integral symmetric bilinear forms and some of their applications*, Math. USSR Izv. 14
(1980), §1.5, Prop. 1.5.1, p. 111: for the glued lattice `M = S ⊕_γ K`, `S` and `K` embed
primitively and each is the orthogonal complement of the other in `M`. This file states and proves
the primitivity half against this repository's lattice notion.

## The shapes are TauCeti's

The primitivity statements are the port of `TauCeti.IntegralLattice.isTorsionFree_quotient_range_glueLeft`
and `_glueRight` (`TauCeti/LinearAlgebra/IntegralLattice/Overlattice/Graph.lean`): the cokernel of
the inclusion of a factor is torsion-free, proved from the identification of the kernel of the
*other* coordinate projection with that factor's image
(`range_glueLeft`/`range_glueRight`). Two things change in the port, and both are recorded where
they bite:

* **The codomain of a coordinate projection.** TauCeti's lattice is a submodule of a fixed
  `ℚ`-vector space `V × W`, so `snd ∘ subtype` lands in the *lattice* `W`. Here the ambient of an
  overlattice is `Frac(R) ⊗ (S.carrier × K.carrier)`, so the second coordinate lands in
  `RationalSpan R K` (`sndProjection`), and the first in `RationalSpan R S` (`fstProjection`). That
  makes the port *cheaper*: the fraction span is torsion-free by construction
  (`Module.IsTorsionFree.trans_faithfulSMul`), so no torsion-freeness hypothesis on `K` is needed
  where TauCeti needed `W` torsion-free as an instance.
* **The intersection property.** TauCeti gets `range glueLeft = ker (snd ∘ subtype)` from its
  construction (`mem_glueAlongDiscriminant_iff_exists`). An arbitrary integral overlattice does not
  have it — adjoin `(s/2, 0)` for `s/2 ∈ S^∨` and `S ⊥ K ⊆ M` still holds — so here it is a
  hypothesis (`hgraph`), and it is exactly #26's graph condition on the gluing subgroup (results 1
  and 2: a totally isotropic subgroup is a graph precisely when both projections are injective).
  What the port loses, therefore, is not a proof but the *derivation of the hypothesis*: this
  repository has no membership characterisation of `evenOverlatticeFromIsotropicSubgroup`'s carrier
  that would discharge it for the graph construction.

## Where the orthogonality lives

The complement half is stated for `M.pairing` on `↥M.carrier`, i.e. for the overlattice's own
integral form (`Overlattice.bilinObject`, `OverlatticeLattice.lean`). The ambient `⊥` is *not* in
`RationalSpan R (S ⊥ K)` and *not* in the sum's carrier: it is the orthogonality of two images inside
the overlattice's carrier, which is where the gluing happens.

## A spelling that does not elaborate

`IsPrimitiveSubmodule (inlSubmodule M)` — the repository's own name for the statement
(`Sublattice.lean`) — does not elaborate at `↥M.carrier`: `IsPrimitiveSubmodule`,
`saturation` and `HasQuotient` all infer the ambient's `AddCommMonoid` as
`AddCommGroup.toAddCommMonoid`, while `↥M.carrier` carries `Submodule.addCommMonoid`; the two are
not interchangeable for elaboration. The primitivity theorems below are therefore stated as the
content of `saturation P ≤ P` (`isPrimitiveSubmodule_iff_saturation_le`, `mem_saturation_iff`), one
element at a time, which needs no instance beyond the submodule's own.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

namespace Overlattice
variable {S K : IntegralLatticeCat R}
variable {R : Type u} [CommRing R] [IsDomain R]
variable {S K : IntegralLatticeCat R}
variable {M : Overlattice R (orthogonalSum S K)}

noncomputable def inlInclusion (M : Overlattice R (orthogonalSum S K)) :
    S.obj.carrier →ₗ[R] ↥M.carrier :=
  M.inclusion.comp
    (LinearMap.inl R S.obj.carrier K.obj.carrier :
      S.obj.carrier →ₗ[R] ↥(orthogonalSum S K).obj.carrier)

noncomputable def inrInclusion (M : Overlattice R (orthogonalSum S K)) :
    K.obj.carrier →ₗ[R] ↥M.carrier :=
  M.inclusion.comp
    (LinearMap.inr R S.obj.carrier K.obj.carrier :
      K.obj.carrier →ₗ[R] ↥(orthogonalSum S K).obj.carrier)

noncomputable def sndProjection (M : Overlattice R (orthogonalSum S K)) :
    ↥M.carrier →ₗ[R] RationalSpan R K :=
  ((orthogonalSumSpanSnd (L := S) (M := K)).restrictScalars R).comp M.carrier.subtype

noncomputable def fstProjection (M : Overlattice R (orthogonalSum S K)) :
    ↥M.carrier →ₗ[R] RationalSpan R S :=
  ((orthogonalSumSpanFst (L := S) (M := K)).restrictScalars R).comp M.carrier.subtype

theorem sndProjection_inlInclusion (M : Overlattice R (orthogonalSum S K)) (s : S.obj.carrier) :
    sndProjection (K := K) M (inlInclusion (K := K) M s) = 0 := by
  have h : M.carrier.subtype (inlInclusion (K := K) M s) =
      toRationalSpan R (orthogonalSum S K) ((s, 0) : ↥(orthogonalSum S K).obj.carrier) := rfl
  simp only [sndProjection, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [h, orthogonalSumSpanSnd_toRationalSpan]
  exact map_zero (toRationalSpan R K)

theorem fstProjection_inrInclusion (M : Overlattice R (orthogonalSum S K)) (k : K.obj.carrier) :
    fstProjection (S := S) M (inrInclusion (S := S) M k) = 0 := by
  have h : M.carrier.subtype (inrInclusion (S := S) M k) =
      toRationalSpan R (orthogonalSum S K) ((0, k) : ↥(orthogonalSum S K).obj.carrier) := rfl
  simp only [fstProjection, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [h, orthogonalSumSpanFst_toRationalSpan]
  exact map_zero (toRationalSpan R S)

/-- The image of `S` in the overlattice `M`. -/
noncomputable def inlSubmodule (M : Overlattice R (orthogonalSum S K)) : Submodule R ↥M.carrier :=
  (inlInclusion (K := K) M).range

/-- The image of `K` in the overlattice `M`. -/
noncomputable def inrSubmodule (M : Overlattice R (orthogonalSum S K)) : Submodule R ↥M.carrier :=
  (inrInclusion (S := S) M).range

theorem range_inlInclusion_le_ker_sndProjection (M : Overlattice R (orthogonalSum S K)) :
    LinearMap.range (inlInclusion (K := K) M) ≤ LinearMap.ker (sndProjection (K := K) M) := by
  rintro x ⟨s, rfl⟩
  rw [LinearMap.mem_ker]
  exact sndProjection_inlInclusion M s

theorem range_inrInclusion_le_ker_fstProjection (M : Overlattice R (orthogonalSum S K)) :
    LinearMap.range (inrInclusion (S := S) M) ≤ LinearMap.ker (fstProjection (S := S) M) := by
  rintro x ⟨k, rfl⟩
  rw [LinearMap.mem_ker]
  exact fstProjection_inrInclusion M k

/-- **`S` is primitive in `M`** when the overlattice meets the first coordinate space in exactly
`S`: `IsPrimitiveSubmodule` of the image of `S` in `M`, i.e. torsion-freeness of `M/S`.

The shape is TauCeti's `isTorsionFree_quotient_range_glueLeft`, and it transfers with two changes.
TauCeti's `snd ∘ subtype` lands in the *lattice* `W`; here the ambient is `Frac(R) ⊗ (S × K)`, so
the second coordinate lands in `RationalSpan R K` — which is why no torsion-freeness hypothesis on
`K` is needed, the fraction span being torsion-free by construction. And TauCeti gets the
intersection `range glueLeft = ker (snd ∘ subtype)` from its construction; an arbitrary integral
overlattice does not have it (adjoin `(s/2, 0)` for `s/2 ∈ S^∨`), so it is a hypothesis here, and
it is exactly #26's graph condition on the gluing subgroup. -/
theorem isPrimitiveSubmodule_range_inlInclusion (M : Overlattice R (orthogonalSum S K))
    (hgraph : LinearMap.ker (sndProjection (K := K) M) ≤ inlSubmodule (K := K) M) :
    ∀ (a : R), a ≠ 0 → ∀ x : ↥M.carrier,
      a • x ∈ inlSubmodule (K := K) M → x ∈ inlSubmodule (K := K) M := by
  intro a ha x hax
  obtain ⟨s, hs⟩ := hax
  refine hgraph ?_
  rw [LinearMap.mem_ker]
  have hzero : a • sndProjection (K := K) M x = 0 := by
    rw [← map_smul (sndProjection (K := K) M) a x, ← hs, sndProjection_inlInclusion]
  letI : Module.IsTorsionFree R (RationalSpan R K) :=
    Module.IsTorsionFree.trans_faithfulSMul R (FractionRing R) (RationalSpan R K)
  exact (smul_eq_zero.mp hzero).resolve_left ha

/-- **`K` is primitive in `M`**, the mirror statement: the same TauCeti shape
(`isTorsionFree_quotient_range_glueRight`) with the first coordinate now landing in
`RationalSpan R S`. -/
theorem isPrimitiveSubmodule_range_inrInclusion (M : Overlattice R (orthogonalSum S K))
    (hgraph : LinearMap.ker (fstProjection (S := S) M) ≤ inrSubmodule (S := S) M) :
    ∀ (a : R), a ≠ 0 → ∀ x : ↥M.carrier,
      a • x ∈ inrSubmodule (S := S) M → x ∈ inrSubmodule (S := S) M := by
  intro a ha x hax
  obtain ⟨k, hk⟩ := hax
  refine hgraph ?_
  rw [LinearMap.mem_ker]
  have hzero : a • fstProjection (S := S) M x = 0 := by
    rw [← map_smul (fstProjection (S := S) M) a x, ← hk, fstProjection_inrInclusion]
  letI : Module.IsTorsionFree R (RationalSpan R S) :=
    Module.IsTorsionFree.trans_faithfulSMul R (FractionRing R) (RationalSpan R S)
  exact (smul_eq_zero.mp hzero).resolve_left ha

end Overlattice

end LeanCategories.Lattices.Valued
