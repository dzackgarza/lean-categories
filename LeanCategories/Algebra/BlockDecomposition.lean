/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.Algebra.DirectSum.Module

/-!
# Block decomposition of modules by central idempotents

Let `A` be a ring and let `e : ι → A` be a finite family of central elements that is a complete
orthogonal family of idempotents, that is `e i * e i = e i`, `e i * e j = 0` for `i ≠ j`, and
`∑ i, e i = 1`. Mathlib's `CompleteOrthogonalIdempotents` records the last three conditions.

For every `A`-module `M` the images `e i • M` are `A`-submodules, and they decompose `M` as an
internal direct sum. Centrality is exactly what makes multiplication by `e i` an `A`-linear map,
so that the image is a submodule and not only an additive subgroup. Nothing here needs
semisimplicity, a fraction field, or any finiteness condition on `M`.

## Main declarations

* `centralSmul`: multiplication by a central element of `A`, as an `A`-linear endomorphism of `M`.
* `blockSubmodule`: the block `e i • M`, as a `Submodule A M`.
* `blockSubmodule_isInternal`: the blocks decompose `M` as an internal direct sum.

## Group rings

The statements apply verbatim to `A = MonoidAlgebra R G`, with no extra hypotheses: the block
decomposition of an `R[G]`-module is intrinsic and needs neither `Frac R` nor semisimplicity of
`R[G]`. Two facts about this case are context only; neither is proved in this file.

* By a theorem of Swan, for `R = ℤ` and `G` finite the only idempotents of `ℤ[G]` are `0` and `1`.
  So the only complete orthogonal family of central idempotents of `ℤ[G]` is the trivial one and
  the global block decomposition of a `ℤ[G]`-module carries no information.
* Genuine block decompositions appear after base change, for instance after localizing `ℤ` at a
  prime, where new central idempotents exist.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v w

variable {ι : Type u} {A : Type v} {M : Type w}
variable [Ring A] [AddCommGroup M] [Module A M]

/-- Multiplication by a central element `a` of `A`, as an `A`-linear endomorphism of `M`.
Centrality is what makes the map `A`-linear rather than merely additive. -/
def centralSmul (a : A) (ha : a ∈ Subring.center A) (M : Type w) [AddCommGroup M] [Module A M] :
    M →ₗ[A] M where
  toFun m := a • m
  map_add' := smul_add a
  map_smul' b m := by
    simp only [RingHom.id_apply, smul_smul, Subring.mem_center_iff.mp ha b]

@[simp]
theorem centralSmul_apply (a : A) (ha : a ∈ Subring.center A) (m : M) :
    centralSmul a ha M m = a • m :=
  rfl

/-- The block `e i • M` of an `A`-module `M` cut out by a central idempotent `e i`. -/
def blockSubmodule (e : ι → A) (he : ∀ i, e i ∈ Subring.center A)
    (M : Type w) [AddCommGroup M] [Module A M] (i : ι) : Submodule A M :=
  LinearMap.range (centralSmul (e i) (he i) M)

/-- An element lies in the `i`-th block exactly when `e i` acts on it as the identity. -/
theorem mem_blockSubmodule_iff {e : ι → A} {he : ∀ i, e i ∈ Subring.center A} {i : ι} {m : M}
    (hi : IsIdempotentElem (e i)) : m ∈ blockSubmodule e he M i ↔ e i • m = m := by
  constructor
  · rintro ⟨x, rfl⟩
    simp [centralSmul, smul_smul, hi.eq]
  · exact fun h ↦ ⟨m, h⟩

/-- Multiplication by `e i` kills the `j`-th block when `j ≠ i`. -/
theorem smul_eq_zero_of_mem_blockSubmodule {e : ι → A} {he : ∀ i, e i ∈ Subring.center A}
    (hortho : Pairwise (e · * e · = 0)) {i j : ι} (hij : j ≠ i) {m : M}
    (hm : m ∈ blockSubmodule e he M j) : e i • m = 0 := by
  obtain ⟨x, rfl⟩ := hm
  rw [centralSmul_apply, smul_smul, hortho hij.symm, zero_smul]

/-- Every element of `M` is the sum of its block components. -/
theorem sum_blockSubmodule_eq_top [Fintype ι] {e : ι → A} (he : ∀ i, e i ∈ Subring.center A)
    (hcomplete : ∑ i, e i = 1) : ⨆ i, blockSubmodule e he M i = ⊤ := by
  refine eq_top_iff.2 fun m _ ↦ ?_
  have hm : m = ∑ i, e i • m := by rw [← Finset.sum_smul, hcomplete, one_smul]
  rw [hm]
  exact sum_mem fun i _ ↦ Submodule.mem_iSup_of_mem i ⟨m, rfl⟩

/-- Distinct blocks are independent. -/
theorem blockSubmodule_iSupIndep {e : ι → A} (he : ∀ i, e i ∈ Subring.center A)
    (hidem : ∀ i, IsIdempotentElem (e i)) (hortho : Pairwise (e · * e · = 0)) :
    iSupIndep (blockSubmodule e he M) := by
  intro i
  rw [disjoint_iff_inf_le]
  rintro m ⟨hmi, hmj⟩
  have hker : (⨆ j, ⨆ _ : j ≠ i, blockSubmodule e he M j) ≤
      LinearMap.ker (centralSmul (e i) (he i) M) := by
    refine iSup_le fun j ↦ iSup_le fun hj ↦ fun x hx ↦ ?_
    exact smul_eq_zero_of_mem_blockSubmodule hortho hj hx
  have h0 : e i • m = 0 := hker hmj
  rw [(mem_blockSubmodule_iff (hidem i)).1 hmi] at h0
  exact h0

/-- A complete orthogonal family of central idempotents decomposes every `A`-module `M` into the
internal direct sum of its blocks `e i • M`. No semisimplicity is needed. -/
theorem blockSubmodule_isInternal [Fintype ι] [DecidableEq ι] {e : ι → A}
    (he : ∀ i, e i ∈ Subring.center A) (he' : CompleteOrthogonalIdempotents e) :
    DirectSum.IsInternal (blockSubmodule e he M) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (blockSubmodule_iSupIndep he he'.idem he'.ortho)
    (sum_blockSubmodule_eq_top he he'.complete)

end LeanCategories.Algebra
