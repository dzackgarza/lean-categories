/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Witt
public import LeanCategories.Modules.Bilinear.Valued.OrthogonalGroup
public import LeanCategories.Modules.Flags
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The isotropic reduction `P^⊥ / P` and its integral stabilizer action (#114)

For a formed module `L` with a symmetric form and a totally isotropic submodule `P`, the restriction
of the form to `P^⊥` has `P` in its radical, so `Q = P^⊥/P` carries an induced form
(`isotropicReduction`). When `P` *is* that radical — the closed/primitive case, hypothesis
`IsotropicReductionData.radical_le` — the induced form on `Q` is nondegenerate
(`isotropicReduction_isNondegenerate`).

An isometry carrying `P` onto itself exactly (not merely into itself) acts on `P^⊥` and on `Q`,
and the action preserves the induced form, so the exact-image stabilizer of `P` maps to the
orthogonal group of `Q` (`isotropicStabilizerToOrthogonal`), with identity and composition laws
coming from the monoid hom itself. Together with the action on `P` this gives the stabilizer
homomorphism to `GL(P) × O(Q)` (`isotropicParabolicHom`), whose kernel is the subgroup of
isometries acting trivially on `P` and on `Q` (`isotropicParabolicHom_ker`).

The exact-image stabilizer is the one of `LeanCategories.Modules.Flags` (#90): the flag
`⊥ ≤ P ≤ ⊤` with every stage carried onto itself, intersected with the isometry condition.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Izv. Akad.
  Nauk SSSR Ser. Mat. 43 (1979), §1: primitive isotropic submodules, `P^⊥/P` and the discriminant
  group of the reduction.
* A. Borel, *Linear Algebraic Groups*, GTM 126, 2nd ed., §8: stabilizers of isotropic flags and
  their action on the reduction.
* J.-P. Serre, *A Course in Arithmetic*, Ch. V: the discriminant form and its behaviour under
  reduction.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

/-- Reduction data for an isotropic submodule: the submodule is totally isotropic, and it is the
whole radical of the form restricted to its orthogonal, which is what makes the reduced form
nondegenerate. This is the primitive (closed) case of Nikulin, §1. -/
structure IsotropicReductionData (L : IntegralLatticeCat R) where
  /-- The isotropic submodule being reduced by. -/
  submodule : Submodule R L.obj.carrier
  /-- The submodule is totally isotropic. -/
  isotropic : L.obj.IsTotallyIsotropic submodule
  /-- The radical of the restriction to the orthogonal is exactly the submodule. -/
  radical_le : L.obj.orthogonalSubmodule submodule ⊓
    L.obj.orthogonalSubmodule (L.obj.orthogonalSubmodule submodule) ≤ submodule

namespace IsotropicReductionData

variable {L : IntegralLatticeCat R} (D : IsotropicReductionData L)

/-- The orthogonal `P^⊥` of the isotropic submodule. -/
def perp : Submodule R L.obj.carrier :=
  L.obj.orthogonalSubmodule D.submodule

theorem submodule_le_perp : D.submodule ≤ D.perp :=
  D.isotropic

/-- The submodule `P` as a submodule of `P^⊥`, i.e. the kernel of the quotient map onto the
reduction. -/
def kernel : Submodule R ↥D.perp :=
  Submodule.comap D.perp.subtype D.submodule

theorem mem_kernel_iff (x : ↥D.perp) : x ∈ D.kernel ↔ (x : L.obj.carrier) ∈ D.submodule :=
  Iff.rfl

/-- The form restricted to `P^⊥`. -/
noncomputable def restricted : BilinModuleCat R R :=
  L.obj.restrict D.perp

@[simp] theorem restricted_pairing (x y : ↥D.perp) :
    D.restricted.pairing x y = L.obj.pairing (x : L.obj.carrier) (y : L.obj.carrier) :=
  rfl

theorem kernel_le_leftRadical : D.kernel ≤ D.restricted.leftRadical := by
  intro x hx
  change D.restricted.bilinMap x = 0
  apply LinearMap.ext
  intro y
  obtain ⟨y, hy⟩ := y
  change L.obj.pairing (x : L.obj.carrier) y = 0
  exact (L.obj.mem_orthogonalSubmodule_iff D.submodule y).mp hy (x : L.obj.carrier) hx

theorem kernel_le_rightRadical (hL : L.obj.IsSymmetric) :
    D.kernel ≤ D.restricted.rightRadical := by
  intro x hx
  change D.restricted.bilinMap.flip x = 0
  apply LinearMap.ext
  intro y
  obtain ⟨y, hy⟩ := y
  change L.obj.pairing y (x : L.obj.carrier) = 0
  rw [show L.obj.pairing y (x : L.obj.carrier) =
    L.obj.pairing (x : L.obj.carrier) y from hL _ _]
  exact (L.obj.mem_orthogonalSubmodule_iff D.submodule y).mp hy (x : L.obj.carrier) hx

/-- The bilinear form of the reduction `Q = P^⊥/P`. -/
noncomputable def reductionBilinMap (hL : L.obj.IsSymmetric) :
    LinearMap.BilinMap R (↥D.perp ⧸ D.kernel) R :=
  D.restricted.bilinMap.liftQ₂ D.kernel D.kernel
    D.kernel_le_leftRadical (D.kernel_le_rightRadical hL)

/-- The isotropic reduction `Q = P^⊥/P` as a formed module. -/
noncomputable def reduction (hL : L.obj.IsSymmetric) : BilinModuleCat R R :=
  BilinModuleCat.ofBilinMap (D.reductionBilinMap hL)

@[simp] theorem reduction_pairing_mk (hL : L.obj.IsSymmetric) (x y : ↥D.perp) :
    (D.reduction hL).pairing (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      L.obj.pairing (x : L.obj.carrier) (y : L.obj.carrier) :=
  rfl

/-- The reduced form is symmetric. -/
theorem reduction_isSymmetric (hL : L.obj.IsSymmetric) :
    (D.reduction hL).IsSymmetric := by
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      exact hL (x : L.obj.carrier) (y : L.obj.carrier)

/-- The reduced form is nondegenerate: this is exactly the hypothesis that `P` is the radical of
the restricted form. -/
theorem reduction_isNondegenerate (hL : L.obj.IsSymmetric) :
    (D.reduction hL).IsNondegenerate := by
  refine ((D.reduction hL).isNondegenerate_iff_adjoint_injective_of_isSymmetric
    (D.reduction_isSymmetric hL)).mpr ?_
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    change (Submodule.Quotient.mk x : ↥D.perp ⧸ D.kernel) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine D.radical_le ⟨x.2, ?_⟩
    intro y hy
    have h1 : ((D.reduction hL).adjoint (Submodule.Quotient.mk x))
        (Submodule.Quotient.mk (⟨y, hy⟩ : ↥D.perp)) = 0 := by
      have h0 := LinearMap.congr_fun hq (Submodule.Quotient.mk (⟨y, hy⟩ : ↥D.perp))
      exact h0
    change L.obj.pairing y (x : L.obj.carrier) = 0
    rw [show L.obj.pairing y (x : L.obj.carrier) =
      L.obj.pairing (x : L.obj.carrier) y from hL _ _]
    exact h1

end IsotropicReductionData

section Isometries

namespace IsotropicReductionData

variable {L : IntegralLatticeCat R}

/-- The exact-image stabilizer of the isotropic submodule inside the orthogonal group: the
isometries carrying `P` onto `P`, not merely into it. -/
def isotropicStabilizer (D : IsotropicReductionData L) :
    Subgroup (BilinModuleCat.OrthogonalGroup L.obj) where
  carrier := {g | D.submodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = D.submodule}
  one_mem' := by
    show D.submodule.map
      (((1 : BilinModuleCat.OrthogonalGroup L.obj).1 : L.obj.carrier ≃ₗ[R] L.obj.carrier) :
        L.obj.carrier →ₗ[R] L.obj.carrier) = D.submodule
    rw [show (((1 : BilinModuleCat.OrthogonalGroup L.obj).1 :
        L.obj.carrier ≃ₗ[R] L.obj.carrier) : L.obj.carrier →ₗ[R] L.obj.carrier) = LinearMap.id
      from rfl, Submodule.map_id]
  mul_mem' := by
    intro g h hg hh
    show D.submodule.map ((g * h).1 : L.obj.carrier →ₗ[R] L.obj.carrier) = D.submodule
    rw [show (((g * h).1 : L.obj.carrier ≃ₗ[R] L.obj.carrier) :
        L.obj.carrier →ₗ[R] L.obj.carrier) =
        (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) ∘ₗ
          (h.1 : L.obj.carrier →ₗ[R] L.obj.carrier) from rfl,
      Submodule.map_comp, hh, hg]
  inv_mem' := by
    intro g hg
    have h := congrArg (fun N : Submodule R L.obj.carrier =>
      N.map (g⁻¹.1 : L.obj.carrier →ₗ[R] L.obj.carrier)) hg
    have hcomp : (((g⁻¹).1 : L.obj.carrier ≃ₗ[R] L.obj.carrier) :
        L.obj.carrier →ₗ[R] L.obj.carrier) ∘ₗ
        (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = LinearMap.id := by
      ext x
      exact (g.1).symm_apply_apply x
    rw [← Submodule.map_comp, hcomp, Submodule.map_id] at h
    exact h.symm

@[simp] theorem mem_isotropicStabilizer_iff (D : IsotropicReductionData L)
    (g : BilinModuleCat.OrthogonalGroup L.obj) :
    g ∈ D.isotropicStabilizer ↔
      D.submodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = D.submodule :=
  Iff.rfl

/-- A stabilizing isometry carries `P^⊥` into itself. -/
theorem perp_map_le (D : IsotropicReductionData L)
    {g : BilinModuleCat.OrthogonalGroup L.obj} (hg : g ∈ D.isotropicStabilizer) :
    D.perp.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) ≤ D.perp := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx p hp
  have hp' : p ∈ D.submodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) := by
    rw [hg]
    exact hp
  obtain ⟨m, hm, rfl⟩ := hp'
  exact (g.property m x).trans
    ((L.obj.mem_orthogonalSubmodule_iff D.submodule x).mp hx m hm)

/-- An isometry stabilizing `P` exactly carries `P^⊥` onto itself. -/
theorem perp_map_eq (D : IsotropicReductionData L)
    {g : BilinModuleCat.OrthogonalGroup L.obj} (hg : g ∈ D.isotropicStabilizer) :
    D.perp.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = D.perp := by
  apply le_antisymm (perp_map_le D hg)
  intro y hy
  exact ⟨((g⁻¹).1 : L.obj.carrier →ₗ[R] L.obj.carrier) y,
    perp_map_le D (inv_mem hg) (Submodule.mem_map_of_mem hy), by simp⟩

/-- The restriction of a stabilizing isometry to `P^⊥`. -/
noncomputable def perpEquiv (D : IsotropicReductionData L)
    {g : BilinModuleCat.OrthogonalGroup L.obj} (hg : g ∈ D.isotropicStabilizer) :
    ↥D.perp ≃ₗ[R] ↥D.perp where
  toFun x := ⟨(g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) x, by
    have h := Submodule.mem_map_of_mem (p := D.perp)
      (f := (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier)) x.2
    rwa [perp_map_eq D hg] at h⟩
  invFun x := ⟨((g⁻¹).1 : L.obj.carrier →ₗ[R] L.obj.carrier) x, by
    have h := Submodule.mem_map_of_mem (p := D.perp)
      (f := ((g⁻¹).1 : L.obj.carrier →ₗ[R] L.obj.carrier)) x.2
    rwa [perp_map_eq D (inv_mem hg)] at h⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

/-- The restriction carries the kernel `P` into itself. -/
theorem perpEquiv_mem_kernel (D : IsotropicReductionData L)
    {g : BilinModuleCat.OrthogonalGroup L.obj} (hg : g ∈ D.isotropicStabilizer)
    {x : ↥D.perp} (hx : x ∈ D.kernel) :
    perpEquiv D hg x ∈ D.kernel := by
  have hmem : ((perpEquiv D hg x : ↥D.perp) : L.obj.carrier) ∈
      D.submodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) :=
    Submodule.mem_map_of_mem hx
  rw [hg] at hmem
  exact hmem

/-- The action of a stabilizing isometry on the isotropic reduction `Q = P^⊥/P`. -/
noncomputable def quotientEquiv (D : IsotropicReductionData L) (hL : L.obj.IsSymmetric)
    {g : BilinModuleCat.OrthogonalGroup L.obj} (hg : g ∈ D.isotropicStabilizer) :
    (D.reduction hL).carrier ≃ₗ[R] (D.reduction hL).carrier := by
  have hleft : ∀ x : ↥D.perp,
      perpEquiv D (inv_mem hg) (perpEquiv D hg x) = x := fun x => (perpEquiv D _).left_inv x
  refine
    { toLinearMap := Submodule.mapQ D.kernel D.kernel (perpEquiv D hg).toLinearMap
        (fun _ hx => perpEquiv_mem_kernel D hg hx)
      invFun := Submodule.mapQ D.kernel D.kernel (perpEquiv D (inv_mem hg)).toLinearMap
        (fun _ hx => perpEquiv_mem_kernel D (inv_mem hg) hx)
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      change Submodule.Quotient.mk (perpEquiv D (inv_mem hg) (perpEquiv D hg y)) =
        Submodule.Quotient.mk y
      rw [hleft]
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      change Submodule.Quotient.mk (perpEquiv D hg (perpEquiv D (inv_mem hg) y)) =
        Submodule.Quotient.mk y
      rw [show perpEquiv D hg (perpEquiv D (inv_mem hg) y) = y from
        (perpEquiv D hg).right_inv y]

/-- On classes, the reduction action is the restricted action on representatives. -/
@[simp] theorem quotientEquiv_mk (D : IsotropicReductionData L) (hL : L.obj.IsSymmetric)
    {g : BilinModuleCat.OrthogonalGroup L.obj} (hg : g ∈ D.isotropicStabilizer)
    (x : ↥D.perp) :
    quotientEquiv D hL hg (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (perpEquiv D hg x) :=
  rfl

/-- The induced action on the reduction preserves the reduced form. -/
theorem quotientEquiv_pairing (D : IsotropicReductionData L) (hL : L.obj.IsSymmetric)
    {g : BilinModuleCat.OrthogonalGroup L.obj} (hg : g ∈ D.isotropicStabilizer)
    (x y : (D.reduction hL).carrier) :
    (D.reduction hL).pairing (quotientEquiv D hL hg x) (quotientEquiv D hL hg y) =
      (D.reduction hL).pairing x y := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    induction y using Submodule.Quotient.induction_on with
    | _ b =>
      change L.obj.pairing
          ((perpEquiv D hg a : ↥D.perp) : L.obj.carrier)
          ((perpEquiv D hg b : ↥D.perp) : L.obj.carrier) =
        L.obj.pairing (a : L.obj.carrier) (b : L.obj.carrier)
      exact g.property (a : L.obj.carrier) (b : L.obj.carrier)

/-- The action of the exact-image stabilizer on the isotropic reduction, as a homomorphism into
the orthogonal group of `Q = P^⊥/P`. -/
noncomputable def reductionIsometry (D : IsotropicReductionData L) (hL : L.obj.IsSymmetric) :
    D.isotropicStabilizer →* BilinModuleCat.OrthogonalGroup (D.reduction hL) where
  toFun g := ⟨quotientEquiv D hL g.2, fun x y => quotientEquiv_pairing D hL g.2 x y⟩
  map_one' := by
    apply Subtype.ext
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      change Submodule.Quotient.mk (perpEquiv D (one_mem _) y) = Submodule.Quotient.mk y
      rw [show perpEquiv D (one_mem _) y = y from Subtype.ext rfl]
  map_mul' g h := by
    apply Subtype.ext
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      change Submodule.Quotient.mk (perpEquiv D (mul_mem g.2 h.2) y) =
        Submodule.Quotient.mk (perpEquiv D g.2 (perpEquiv D h.2 y))
      rw [show perpEquiv D (mul_mem g.2 h.2) y =
        perpEquiv D g.2 (perpEquiv D h.2 y) from Subtype.ext rfl]

/-- The inverse of a stabilizing isometry stabilizes the submodule as well. -/
theorem submodule_map_inv (D : IsotropicReductionData L)
    {g : BilinModuleCat.OrthogonalGroup L.obj} (hg : g ∈ D.isotropicStabilizer) :
    D.submodule.map ((g⁻¹).1 : L.obj.carrier →ₗ[R] L.obj.carrier) = D.submodule := by
  have h := congrArg (fun N : Submodule R L.obj.carrier =>
    N.map (g⁻¹.1 : L.obj.carrier →ₗ[R] L.obj.carrier)) hg
  have hcomp : (((g⁻¹).1 : L.obj.carrier ≃ₗ[R] L.obj.carrier) :
      L.obj.carrier →ₗ[R] L.obj.carrier) ∘ₗ
      (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = LinearMap.id := by
    ext x
    exact (g.1).symm_apply_apply x
  rw [← Submodule.map_comp, hcomp, Submodule.map_id] at h
  exact h.symm

/-- The action of the stabilizer on the isotropic submodule itself. -/
noncomputable def submoduleEquiv (D : IsotropicReductionData L)
    {g : BilinModuleCat.OrthogonalGroup L.obj} (hg : g ∈ D.isotropicStabilizer) :
    ↥D.submodule ≃ₗ[R] ↥D.submodule where
  toFun x := ⟨(g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) x, by
    have h := Submodule.mem_map_of_mem (p := D.submodule)
      (f := (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier)) x.2
    rwa [hg] at h⟩
  invFun x := ⟨((g⁻¹).1 : L.obj.carrier →ₗ[R] L.obj.carrier) x, by
    have h := Submodule.mem_map_of_mem (p := D.submodule)
      (f := ((g⁻¹).1 : L.obj.carrier →ₗ[R] L.obj.carrier)) x.2
    rwa [submodule_map_inv D hg] at h⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

/-- The stabilizer homomorphism to `GL(P) × O(Q)`: the action on the isotropic submodule and the
action on its reduction. -/
noncomputable def parabolicHom (D : IsotropicReductionData L) (hL : L.obj.IsSymmetric) :
    D.isotropicStabilizer →* (↥D.submodule ≃ₗ[R] ↥D.submodule) ×
      BilinModuleCat.OrthogonalGroup (D.reduction hL) where
  toFun g := (submoduleEquiv D g.2,
    ⟨quotientEquiv D hL g.2, fun x y => quotientEquiv_pairing D hL g.2 x y⟩)
  map_one' := by
    apply Prod.ext
    · apply LinearEquiv.ext
      intro x
      ext
      simp [submoduleEquiv]
    · apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ y =>
        change Submodule.Quotient.mk (perpEquiv D (one_mem _) y) = Submodule.Quotient.mk y
        rw [show perpEquiv D (one_mem _) y = y from Subtype.ext rfl]
  map_mul' g h := by
    apply Prod.ext
    · apply LinearEquiv.ext
      intro x
      ext
      simp [submoduleEquiv]
    · apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ y =>
        change Submodule.Quotient.mk (perpEquiv D (mul_mem g.2 h.2) y) =
          Submodule.Quotient.mk (perpEquiv D g.2 (perpEquiv D h.2 y))
        rw [show perpEquiv D (mul_mem g.2 h.2) y =
          perpEquiv D g.2 (perpEquiv D h.2 y) from Subtype.ext rfl]

/-- The kernel of the stabilizer homomorphism: the isometries acting trivially on the isotropic
submodule and on its reduction. -/
theorem mem_parabolicHom_ker_iff (D : IsotropicReductionData L) (hL : L.obj.IsSymmetric)
    (g : D.isotropicStabilizer) :
    g ∈ (parabolicHom D hL).ker ↔
      submoduleEquiv D g.2 = 1 ∧ quotientEquiv D hL g.2 = 1 := by
  rw [MonoidHom.mem_ker, Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Subtype.ext_iff.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Subtype.ext h2⟩

end IsotropicReductionData

end Isometries

end LeanCategories.Lattices.Valued

