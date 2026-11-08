/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Flags
public import LeanCategories.Lattices.Valued.OrthogonalGroup

/-!
# The general-linear parabolic of a saturated flag in an integral lattice (#90)

This is the integral-lattice consumer of `LeanCategories.Modules.Flags`. For a lattice `L` whose
carrier is a finite free module over a PID and a strict flag of saturated submodules, the
general-linear parabolic is the flag stabilizer of `LeanCategories.Modules.Flags` applied to the
carrier's flag, and its Levi quotient is the projection to the general linear groups of the graded
pieces `F_{k+1} / F_k`. Both objects are used here directly, not through a matrix statement: the
graded pieces are built from the flag itself, and the adapted basis only *identifies* them with
coordinate blocks.

## What this theorem does not supply

Form preservation is a different condition from triangularity. The subgroup `O(L) ∩ P(F)` of
isometries that also preserve the flag is *not* computed by the general-linear theorem: an
orthogonal stabilizer needs the additional form equations, one for each block of the adapted
matrix, beyond the block-triangularity proved in `LeanCategories.Modules.Flags`. What is supplied
here is (a) the intersection, defined as the isometries whose underlying automorphism preserves the
flag, and (b) its projection to the graded pieces, which any blockwise form computation then
refines. In particular no identification of `O(L) ∩ P(F)` with a group of block-triangular
matrices is claimed, and none should be inferred from this file.

## References

* Armand Borel, *Linear Algebraic Groups*, GTM 126, 2nd ed., §§3–4 and §8, for parabolic
  subgroups of `GL` and their Levi decomposition.
* Bourbaki, *Algèbre commutative*, Ch. VII, for modules over principal ideal domains.
* J. S. Milne, *Algebraic Groups*, §§3, 7 and 23, for parabolics, their unipotent radicals and
  their Levi factors in the form used by the cusp stabilizer computations.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

/-- A strict flag of saturated submodules running from `⊥` to the whole carrier. Saturation is the
condition `Module.IsTorsionFree R (carrier ⧸ F i)`, i.e. that each stage is a direct summand-like
primitive submodule, which is what allows the adapted basis to exist. -/
def IsSaturatedFlag (L : IntegralLatticeCat R) {r : ℕ}
    (F : Fin (r + 1) → Submodule R L.obj.carrier) : Prop :=
  F 0 = ⊥ ∧ F (Fin.last r) = ⊤ ∧ StrictMono F ∧
    ∀ i, Module.IsTorsionFree R (L.obj.carrier ⧸ F i)

variable (L : IntegralLatticeCat R)

/-- The general-linear parabolic of a flag of the lattice carrier: the subgroup of the general
linear group of the carrier carrying every stage onto itself. -/
abbrev latticeFlagStabilizer {r : ℕ} (F : Fin (r + 1) → Submodule R L.obj.carrier) :
    Subgroup (LinearMap.GeneralLinearGroup R L.obj.carrier) :=
  flagStabilizer F

/-- The `k`-th graded piece of the lattice flag, `F_{k+1} / F_k`. -/
abbrev latticeGradedPiece {r : ℕ} (F : Fin (r + 1) → Submodule R L.obj.carrier) (k : Fin r) :
    Type u :=
  flagGradedPiece F k

/-- A saturated strict flag of a finite free lattice over a PID has an adapted basis. -/
theorem exists_adaptedBasis_of_isSaturatedFlag [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R L.obj.carrier] [Module.Finite R L.obj.carrier] {r : ℕ}
    {F : Fin (r + 1) → Submodule R L.obj.carrier} (h : IsSaturatedFlag L F) :
    ∃ (ι : Type u) (_ : Fintype ι) (block : ι → Fin r) (b : Module.Basis ι R L.obj.carrier),
      BlockAdapted b block F :=
  existsAdaptedBasis F h.1 h.2.1 h.2.2.1.monotone h.2.2.1 h.2.2.2

/-- In an adapted basis the parabolic is the group of invertible block-triangular matrices. -/
noncomputable def latticeFlagStabilizerEquiv {ι : Type u} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (b : Module.Basis ι R L.obj.carrier) (block : ι → Fin r)
    {F : Fin (r + 1) → Submodule R L.obj.carrier} (hadapt : BlockAdapted b block F) :
    blockTriangularSubgroup (R := R) block ≃* latticeFlagStabilizer L F :=
  flagStabilizerMatrixEquiv b block hadapt

/-- The projection of the parabolic to the general linear groups of the graded pieces. This is the
Levi quotient used by the cusp stabilizer computations. -/
noncomputable def latticeFlagGradedHom {r : ℕ} (F : Fin (r + 1) → Submodule R L.obj.carrier) :
    latticeFlagStabilizer L F →*
      ∀ k, (latticeGradedPiece L F k ≃ₗ[R] latticeGradedPiece L F k) :=
  flagGradedHom F

/-- The unipotent radical of the parabolic: the flag-preserving automorphisms acting as the identity
on every graded piece. -/
noncomputable def latticeFlagUnipotent {r : ℕ} (F : Fin (r + 1) → Submodule R L.obj.carrier) :
    Subgroup (latticeFlagStabilizer L F) :=
  flagUnipotentCore F

/-- The unipotent radical is the kernel of the projection to the graded pieces. -/
theorem latticeFlagUnipotent_eq_ker {r : ℕ} (F : Fin (r + 1) → Submodule R L.obj.carrier) :
    latticeFlagUnipotent L F = (latticeFlagGradedHom L F).ker :=
  flagUnipotentCore_eq_ker F

/-- The linear automorphism of the carrier underlying an isometry. -/
noncomputable def orthogonalToGL :
    OrthogonalGroup L →* LinearMap.GeneralLinearGroup R L.obj.carrier :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R L.obj.carrier).symm.toMonoidHom.comp
    (OrthogonalGroup L).subtype

/-- The underlying linear automorphism of an isometry is its linear equivalence. -/
@[simp] theorem orthogonalToGL_apply (g : OrthogonalGroup L) :
    ((orthogonalToGL L g : LinearMap.GeneralLinearGroup R L.obj.carrier) :
      L.obj.carrier →ₗ[R] L.obj.carrier) = (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) :=
  rfl

/-- The orthogonal part of the parabolic: the isometries whose underlying automorphism preserves the
flag. The form-preservation equations are those of `O(L)` itself; this definition adds the flag
equations on top of them and does not derive either from the other. -/
noncomputable def orthogonalFlagStabilizer {r : ℕ} (F : Fin (r + 1) → Submodule R L.obj.carrier) :
    Subgroup (OrthogonalGroup L) :=
  (latticeFlagStabilizer L F).comap (orthogonalToGL L)

/-- Membership in the orthogonal parabolic is preservation of every stage, on top of being an
isometry. -/
theorem mem_orthogonalFlagStabilizer_iff {r : ℕ} {F : Fin (r + 1) → Submodule R L.obj.carrier}
    (g : OrthogonalGroup L) :
    g ∈ orthogonalFlagStabilizer L F ↔
      ∀ k, (F k).map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = F k := by
  rw [orthogonalFlagStabilizer, latticeFlagStabilizer, Subgroup.mem_comap, mem_flagStabilizer_iff]
  exact forall_congr' (fun k => Iff.rfl)

/-- The orthogonal parabolic lands in the general-linear parabolic. -/
noncomputable def orthogonalFlagStabilizerToGL {r : ℕ}
    {F : Fin (r + 1) → Submodule R L.obj.carrier} :
    orthogonalFlagStabilizer L F →* latticeFlagStabilizer L F where
  toFun g := ⟨orthogonalToGL L g.1, g.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.1 h.1)

/-- The projection of the orthogonal parabolic to the general linear groups of the graded pieces. -/
noncomputable def orthogonalFlagGradedHom {r : ℕ}
    (F : Fin (r + 1) → Submodule R L.obj.carrier) :
    orthogonalFlagStabilizer L F →*
      ∀ k, (latticeGradedPiece L F k ≃ₗ[R] latticeGradedPiece L F k) :=
  (latticeFlagGradedHom L F).comp (orthogonalFlagStabilizerToGL L)

/-- Preservation of a single stage by an isometry is its fixed-point condition for the action of
`O(L)` on submodules of the carrier. -/
theorem mem_orthogonalFlagStabilizer_iff_submoduleStabilizer {r : ℕ}
    {F : Fin (r + 1) → Submodule R L.obj.carrier} (g : OrthogonalGroup L) :
    g ∈ orthogonalFlagStabilizer L F ↔ ∀ k, g ∈ submoduleStabilizer L (F k) := by
  rw [mem_orthogonalFlagStabilizer_iff]
  refine forall_congr' (fun k => ?_)
  rw [MulAction.mem_stabilizer_iff]
  rfl

end LeanCategories.Lattices.Valued
