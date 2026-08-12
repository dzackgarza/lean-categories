/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ReflectionGeneration
public import LeanCategories.Lattices.Valued.SpinorNormConstruction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The Lipschitz group acts on the carrier by isometries

Twisted conjugation `x ↦ involute g * x * g⁻¹` by an element of the Lipschitz group keeps the
vectors of a Clifford algebra vectors. Mathlib proves that stability statement but leaves the
result inside the Clifford algebra. This file transports it back along the canonical map `ι`,
which is injective in characteristic other than two, and packages the result as a group map
from the Lipschitz group to the orthogonal group.

On a vector generator the action is the reflection in that vector, so the map is surjective
whenever reflections generate the orthogonal group.

Reference: Cassels, *Rational Quadratic Forms*, Chapter 10, §3.
-/

@[expose] public section

open CliffordAlgebra
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The canonical map into a Clifford algebra is injective away from characteristic two.

The exterior algebra is the Clifford algebra of the zero form, and `changeForm` identifies the
two modules while fixing the vectors. -/
theorem cliffordAlgebra_ι_injective {M : Type u} [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M) : Function.Injective (ι Q) := by
  intro x y hxy
  have h := congrArg (equivExterior Q) hxy
  simp only [equivExterior, changeFormEquiv_apply, changeForm_ι] at h
  exact (ExteriorAlgebra.ι_inj K x y).mp h

/-- The vectors of the Clifford algebra, as a copy of the carrier. -/
noncomputable def cliffordVectorEquiv (L : FiniteFormCat K K) :
    L.obj.carrier ≃ₗ[K] LinearMap.range (ι (finiteFormQuadratic L)) :=
  LinearEquiv.ofInjective _ (cliffordAlgebra_ι_injective _)

/-- Reading a vector of the Clifford algebra back into the carrier inverts `ι`. -/
theorem ι_cliffordVectorEquiv_symm (L : FiniteFormCat K K)
    (y : LinearMap.range (ι (finiteFormQuadratic L))) :
    ι (finiteFormQuadratic L) ((cliffordVectorEquiv L).symm y) = (y : FiniteFormClifford L) :=
  congrArg Subtype.val ((cliffordVectorEquiv L).apply_symm_apply y)

/-- Twisted conjugation by a unit, as a linear map into the Clifford algebra. -/
noncomputable def cliffordTwistMap (L : FiniteFormCat K K) (g : (FiniteFormClifford L)ˣ) :
    L.obj.carrier →ₗ[K] FiniteFormClifford L :=
  (LinearMap.mulLeft K (involute (Q := finiteFormQuadratic L) (g : FiniteFormClifford L))).comp
    ((LinearMap.mulRight K ((g⁻¹ : (FiniteFormClifford L)ˣ) : FiniteFormClifford L)).comp
      (ι (finiteFormQuadratic L)))

omit [Invertible (2 : K)] in
@[simp]
theorem cliffordTwistMap_apply (L : FiniteFormCat K K) (g : (FiniteFormClifford L)ˣ)
    (x : L.obj.carrier) :
    cliffordTwistMap L g x =
      involute (Q := finiteFormQuadratic L) (g : FiniteFormClifford L) *
        ι (finiteFormQuadratic L) x * ((g⁻¹ : (FiniteFormClifford L)ˣ) : FiniteFormClifford L) := by
  rw [cliffordTwistMap]
  simp [mul_assoc]

/-- Twisted conjugation by a Lipschitz element, as an endomorphism of the carrier. -/
noncomputable def lipschitzEnd (L : FiniteFormCat K K)
    (g : lipschitzGroup (finiteFormQuadratic L)) : L.obj.carrier →ₗ[K] L.obj.carrier :=
  (cliffordVectorEquiv L).symm.toLinearMap.comp
    (LinearMap.codRestrict (LinearMap.range (ι (finiteFormQuadratic L)))
      (cliffordTwistMap L (g : (FiniteFormClifford L)ˣ)) fun x ↦ by
        rw [cliffordTwistMap_apply]
        exact lipschitzGroup.involute_act_ι_mem_range_ι g.2 x)

/-- The defining property of the twisted-conjugation endomorphism. -/
theorem ι_lipschitzEnd (L : FiniteFormCat K K)
    (g : lipschitzGroup (finiteFormQuadratic L)) (x : L.obj.carrier) :
    ι (finiteFormQuadratic L) (lipschitzEnd L g x) =
      involute (Q := finiteFormQuadratic L) ((g : (FiniteFormClifford L)ˣ) : FiniteFormClifford L) *
        ι (finiteFormQuadratic L) x *
        (((g : (FiniteFormClifford L)ˣ)⁻¹ : (FiniteFormClifford L)ˣ) : FiniteFormClifford L) :=
  (ι_cliffordVectorEquiv_symm L _).trans (cliffordTwistMap_apply L _ x)

/-- The identity acts trivially. -/
theorem lipschitzEnd_one (L : FiniteFormCat K K) (x : L.obj.carrier) :
    lipschitzEnd L 1 x = x := by
  refine cliffordAlgebra_ι_injective (finiteFormQuadratic L) ?_
  rw [ι_lipschitzEnd]
  simp

/-- Twisted conjugation turns a product into a composition. -/
theorem lipschitzEnd_lipschitzEnd (L : FiniteFormCat K K)
    (g h : lipschitzGroup (finiteFormQuadratic L)) (x : L.obj.carrier) :
    lipschitzEnd L g (lipschitzEnd L h x) = lipschitzEnd L (g * h) x := by
  refine cliffordAlgebra_ι_injective (finiteFormQuadratic L) ?_
  rw [ι_lipschitzEnd, ι_lipschitzEnd, ι_lipschitzEnd]
  simp [mul_assoc]

/-- The action of a Lipschitz element on the carrier, by twisted conjugation. -/
noncomputable def lipschitzAction (L : FiniteFormCat K K)
    (g : lipschitzGroup (finiteFormQuadratic L)) : L.obj.carrier ≃ₗ[K] L.obj.carrier :=
  LinearEquiv.ofLinear (lipschitzEnd L g) (lipschitzEnd L g⁻¹)
    (LinearMap.ext fun x ↦ by
      simp only [LinearMap.comp_apply, LinearMap.id_apply, lipschitzEnd_lipschitzEnd,
        mul_inv_cancel, lipschitzEnd_one])
    (LinearMap.ext fun x ↦ by
      simp only [LinearMap.comp_apply, LinearMap.id_apply, lipschitzEnd_lipschitzEnd,
        inv_mul_cancel, lipschitzEnd_one])

@[simp]
theorem lipschitzAction_apply (L : FiniteFormCat K K)
    (g : lipschitzGroup (finiteFormQuadratic L)) (x : L.obj.carrier) :
    lipschitzAction L g x = lipschitzEnd L g x :=
  rfl

/-- The defining property of the Lipschitz action. -/
theorem ι_lipschitzAction (L : FiniteFormCat K K)
    (g : lipschitzGroup (finiteFormQuadratic L)) (x : L.obj.carrier) :
    ι (finiteFormQuadratic L) (lipschitzAction L g x) =
      involute (Q := finiteFormQuadratic L) ((g : (FiniteFormClifford L)ˣ) : FiniteFormClifford L) *
        ι (finiteFormQuadratic L) x *
        (((g : (FiniteFormClifford L)ˣ)⁻¹ : (FiniteFormClifford L)ˣ) : FiniteFormClifford L) :=
  ι_lipschitzEnd L g x

@[simp]
theorem lipschitzAction_one (L : FiniteFormCat K K) :
    lipschitzAction L 1 = 1 :=
  LinearEquiv.ext (lipschitzEnd_one L)

theorem lipschitzAction_mul (L : FiniteFormCat K K)
    (g h : lipschitzGroup (finiteFormQuadratic L)) :
    lipschitzAction L (g * h) = lipschitzAction L g * lipschitzAction L h :=
  LinearEquiv.ext fun x ↦ (lipschitzEnd_lipschitzEnd L g h x).symm

theorem lipschitzAction_inv (L : FiniteFormCat K K)
    (g : lipschitzGroup (finiteFormQuadratic L)) :
    lipschitzAction L g⁻¹ = (lipschitzAction L g)⁻¹ :=
  LinearEquiv.ext fun _ ↦ rfl

/-- Twisted conjugation, as a map of groups into the linear automorphisms of the carrier. -/
noncomputable def lipschitzActionHomEquiv (L : FiniteFormCat K K) :
    lipschitzGroup (finiteFormQuadratic L) →* (L.obj.carrier ≃ₗ[K] L.obj.carrier) where
  toFun := lipschitzAction L
  map_one' := lipschitzAction_one L
  map_mul' := lipschitzAction_mul L

/-- On a vector generator the Lipschitz action is the reflection in that vector. -/
theorem lipschitzAction_cliffordVectorUnit (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) :
    lipschitzAction L ⟨cliffordVectorUnit L v hv,
        cliffordVectorUnit_mem_lipschitzGroup L v hv⟩ = finiteFormReflection L v hv := by
  refine LinearEquiv.ext fun x ↦ cliffordAlgebra_ι_injective (finiteFormQuadratic L) ?_
  rw [ι_lipschitzAction]
  exact cliffordVectorUnit_involute_conj L v hv x

/-- The Lipschitz action of a vector, in whatever form the vector is presented. -/
theorem lipschitzAction_eq_reflection (L : FiniteFormCat K K)
    (g : lipschitzGroup (finiteFormQuadratic L)) (v : L.obj.carrier)
    (hv : L.obj.pairing v v ≠ 0)
    (hg : (g : (FiniteFormClifford L)ˣ) = cliffordVectorUnit L v hv) :
    lipschitzAction L g = finiteFormReflection L v hv := by
  rw [show g = ⟨cliffordVectorUnit L v hv, cliffordVectorUnit_mem_lipschitzGroup L v hv⟩ from
    Subtype.ext hg, lipschitzAction_cliffordVectorUnit]

/-- The Lipschitz action preserves the pairing.

The isometries form a subgroup, so it is enough to check the vector generators, where the
action is a reflection. -/
theorem lipschitzAction_mem_orthogonalSubgroup (L : FiniteFormCat K K)
    (g : lipschitzGroup (finiteFormQuadratic L)) :
    lipschitzAction L g ∈ BilinModuleCat.orthogonalSubgroup L.obj := by
  refine Subgroup.closure_induction
    (p := fun x hx ↦ lipschitzAction L ⟨x, hx⟩ ∈ BilinModuleCat.orthogonalSubgroup L.obj)
    ?_ ?_ ?_ ?_ g.2
  · rintro x ⟨v, hv⟩
    have hQ : L.obj.pairing v v ≠ 0 := by
      have hu : IsUnit (finiteFormQuadratic L v) :=
        isUnit_of_isUnit_ι (finiteFormQuadratic L) (hv ▸ x.isUnit)
      exact (finiteFormQuadratic_apply L v) ▸ hu.ne_zero
    have hred : ∀ hx : x ∈ lipschitzGroup (finiteFormQuadratic L),
        lipschitzAction L ⟨x, hx⟩ = finiteFormReflection L v hQ := fun hx ↦
      lipschitzAction_eq_reflection L ⟨x, hx⟩ v hQ (Units.ext hv.symm)
    rw [hred]
    exact finiteFormReflection_isometry L v hQ
  · exact (lipschitzAction_one L).symm ▸ one_mem _
  · intro x y hx hy ihx ihy
    exact (lipschitzAction_mul L ⟨x, hx⟩ ⟨y, hy⟩).symm ▸ mul_mem ihx ihy
  · intro x hx ihx
    exact (lipschitzAction_inv L ⟨x, hx⟩).symm ▸ inv_mem ihx

/-- Twisted conjugation, as a map of groups from the Lipschitz group to the orthogonal group. -/
noncomputable def lipschitzActionHom (L : FiniteFormCat K K) :
    lipschitzGroup (finiteFormQuadratic L) →* BilinModuleCat.OrthogonalGroup L.obj :=
  (lipschitzActionHomEquiv L).codRestrict _ (lipschitzAction_mem_orthogonalSubgroup L)

/-- The Lipschitz action of a vector generator is the reflection, as an isometry. -/
theorem lipschitzActionHom_cliffordVectorUnit (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) :
    lipschitzActionHom L ⟨cliffordVectorUnit L v hv,
        cliffordVectorUnit_mem_lipschitzGroup L v hv⟩ = finiteFormReflectionElement L v hv :=
  Subtype.ext (lipschitzAction_cliffordVectorUnit L v hv)

/-- The Lipschitz group covers the orthogonal group of a nondegenerate form.

Reflections generate the orthogonal group, and every reflection is the action of the
corresponding vector generator. -/
theorem lipschitzActionHom_surjective (L : FiniteFormCat K K)
    (hL : L.obj.IsLeftNondegenerate) : Function.Surjective (lipschitzActionHom L) := by
  rw [← MonoidHom.range_eq_top]
  refine top_le_iff.mp ?_
  rw [← reflectionsGenerate L hL]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨⟨cliffordVectorUnit L v hv, cliffordVectorUnit_mem_lipschitzGroup L v hv⟩,
    lipschitzActionHom_cliffordVectorUnit L v hv⟩

end LeanCategories.Lattices.Valued
