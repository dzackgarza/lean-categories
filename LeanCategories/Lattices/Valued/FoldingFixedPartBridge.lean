/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantConverse

/-!
# The invariant part of the real form is `M^σ ⊗ ℝ` (`#116`)

`Folding.lean` states the trace and wall theorems of AEGS Lemma 3.8 inside the *fixed locus*
`realFormFixedPart g` of the real form, and `FoldingInvariantChamber.lean` states the predicate
`IsChamberWithWalls` for the invariant lattice, whose own real form `realForm (M^σ)` is a different
type. Moving between them is the bridge those two files lack. This file builds it.

* `realFormFixedPart_eq_span` — the fixed locus *is* the real span of the fixed lattice vectors
  (`realForm_mem_span_fixed` pointwise, `realFormFixedImage_subset_fixedPart` for the reverse);
* `invariantToAmbient` — the tensor-level map `ℝ ⊗_ℤ M^σ → realForm L`, `r ⊗ v ↦ r • v`, defined by
  the universal property (`TensorProduct.lift`);
* `invariantToAmbient_tmul` — it computes on pure tensors;
* `invariantToAmbient_range` — **its range is exactly the fixed locus**: the image of the pure
  tensors is the span of the fixed lattice vectors, and `≅` says that span is the fixed locus.

An equivariant linear *equivalence* `realForm M^σ ≃ realFormFixedPart g` is then
`LinearMap.range`-restricted image of this map once injectivity is added; injectivity is flatness of
`ℝ` over `ℤ` (`Module.Flat.tensorProduct_mk_injective`), and is the next step, not this one. What is
here is everything the transport of the *quadratic form* needs, since the pairing of two pure
tensors is `invariant_pairing_toRealForm` (`FoldingInvariantChamber.lean`).

## LC-09 record

Searched the repository for an identification of the real form of a formed sublattice with a
submodule of the ambient real form: `rg "tensorProduct_mk_injective"` gives
`AdelicClass.lean:284`, `MetricDual.lean:476`, `Discriminant.lean:263,628` (all flatness arguments,
none constructing such a map); `rg "TensorProduct.lift"` over `LeanCategories/Lattices/` gives the
base-change functor and `Defect` constructions, no sublattice bridge. Mathlib at the pinned head has
`LinearMap.fixedSubmodule` and the tensor universal property, and no statement identifying the fixed
locus of a base-changed endomorphism with the base change of the fixed submodule — which requires
the averaging argument this repository already carries (`realForm_mem_span_fixed`). Nothing
ported.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, arXiv:2312.03638v2, §3.7–3.8 (printed
  pp. 11–13): `C^J := C ∩ T_En ⊗ R`, the intersection the bridge makes precise.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Ch. V §1: chambers and their traces on a subspace.
-/

@[expose] public section

open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The fixed locus is the real span of the fixed lattice vectors.** `realForm_mem_span_fixed`
gives every fixed point is in that span, and the image of the fixed lattice lies in the fixed locus;
the two give the equality of submodules. -/
theorem realFormFixedPart_eq_span (g : OrthogonalGroup L.obj) (hg : g * g = 1) :
    realFormFixedPart g = Submodule.span ℝ (realFormFixedImage g) := by
  refine le_antisymm ?_ ?_
  · intro z hz
    exact realForm_mem_span_fixed g hg hz
  · refine Submodule.span_le.mpr ?_
    exact realFormFixedImage_subset_fixedPart g

/-- The bilinear map `(r, v) ↦ r • v` over `ℤ`, whose lift is the bridge. -/
noncomputable def invariantToAmbientBilin (g : OrthogonalGroup L.obj) :
    ℝ →ₗ[ℤ] involutionFixedSubmodule g →ₗ[ℤ] (realForm L).obj.carrier where
  toFun r :=
    { toFun := fun v => r • toRealForm L (v : L.obj.obj.carrier)
      map_add' := fun v w => by
        rw [Submodule.coe_add,
          toRealForm_add (L := L) (v : L.obj.obj.carrier) (w : L.obj.obj.carrier), smul_add]
      map_smul' := fun c v => by
        change r • toRealForm L (c • (v : L.obj.obj.carrier))
          = c • (r • toRealForm L (v : L.obj.obj.carrier))
        rw [toRealForm_zsmul (L := L) c (v : L.obj.obj.carrier), smul_comm,
          Int.cast_smul_eq_zsmul] }
  map_add' r r' := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk, add_smul]
  map_smul' c r := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
      smul_assoc]

/-- **The bridge**, as a `ℤ`-linear map first. -/
noncomputable def invariantToAmbientZ (g : OrthogonalGroup L.obj) :
    (TensorProduct ℤ ℝ (involutionFixedSubmodule g)) →ₗ[ℤ] (realForm L).obj.carrier :=
  TensorProduct.lift (invariantToAmbientBilin (L := L) g)

theorem invariantToAmbientZ_tmul (g : OrthogonalGroup L.obj) (r : ℝ)
    (v : involutionFixedSubmodule g) :
    invariantToAmbientZ (L := L) g ((r : ℝ) ⊗ₜ[ℤ] v)
      = r • toRealForm L (v : L.obj.obj.carrier) := by
  rw [invariantToAmbientZ]
  rfl

/-- **The bridge, as an `ℝ`-linear map**: `r ⊗ v ↦ r • v`. -/
noncomputable def invariantToAmbient (g : OrthogonalGroup L.obj) :
    (TensorProduct ℤ ℝ (involutionFixedSubmodule g)) →ₗ[ℝ] (realForm L).obj.carrier where
  toFun := invariantToAmbientZ (L := L) g
  map_add' x y := (invariantToAmbientZ (L := L) g).map_add x y
  map_smul' a x := by
    induction x using TensorProduct.inductionOn with
    | tmul r v =>
        rw [show a • ((r : ℝ) ⊗ₜ[ℤ] v) = ((a * r : ℝ) ⊗ₜ[ℤ] v) from by
          rw [TensorProduct.smul_tmul']
          simp [smul_eq_mul]]
        rw [invariantToAmbientZ_tmul (L := L) g, invariantToAmbientZ_tmul (L := L) g]
        change (a * r) • toRealForm L (v : L.obj.obj.carrier)
          = a • (r • toRealForm L (v : L.obj.obj.carrier))
        rw [mul_smul]
    | add x y hx hy =>
        rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem invariantToAmbient_tmul (g : OrthogonalGroup L.obj) (r : ℝ)
    (v : involutionFixedSubmodule g) :
    invariantToAmbient (L := L) g ((r : ℝ) ⊗ₜ[ℤ] v)
      = r • toRealForm L (v : L.obj.obj.carrier) :=
  invariantToAmbientZ_tmul (L := L) g r v

/-- **The bridge's range is exactly the invariant part of the real form.** The image of the pure
tensors is the span of the fixed lattice vectors, and the fixed locus *is* that span
(`realFormFixedPart_eq_span`). -/
theorem invariantToAmbient_range (g : OrthogonalGroup L.obj) (hg : g * g = 1) :
    LinearMap.range (invariantToAmbient (L := L) g) = realFormFixedPart g := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul r v =>
        rw [invariantToAmbient_tmul (L := L) g]
        exact (realFormFixedPart g).smul_mem r
          (realFormFixedImage_subset_fixedPart g ⟨v, rfl⟩)
    | add x y hx hy =>
        rw [map_add]
        exact (realFormFixedPart g).add_mem hx hy
  · rw [realFormFixedPart_eq_span g hg]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨(1 : ℝ) ⊗ₜ[ℤ] v, by rw [invariantToAmbient_tmul (L := L) g, one_smul]⟩

end LeanCategories.Lattices.Valued
