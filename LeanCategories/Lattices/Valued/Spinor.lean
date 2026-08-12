/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.LocalInvariants
public import LeanCategories.Lattices.Valued.OrthogonalGroup
public import Mathlib.LinearAlgebra.Reflection

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {K : Type u} [Field K]

/-- The covector which defines reflection in a nonsingular vector. -/
noncomputable def reflectionFunctional (L : FiniteFormCat K K)
    (v : L.obj.carrier) (_ : L.obj.pairing v v ≠ 0) :
    Module.Dual K L.obj.carrier :=
  (2 * (L.obj.pairing v v)⁻¹) • L.obj.bilinMap v

@[simp]
theorem reflectionFunctional_apply_self (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) :
    reflectionFunctional L v hv v = 2 := by
  simp [reflectionFunctional, hv]

/-- Reflection in a nonsingular vector as a linear automorphism. -/
noncomputable def finiteFormReflection (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) :
    L.obj.carrier ≃ₗ[K] L.obj.carrier :=
  Module.reflection (reflectionFunctional_apply_self L v hv)

@[simp]
theorem finiteFormReflection_apply (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0)
    (x : L.obj.carrier) :
    finiteFormReflection L v hv x =
      x - (reflectionFunctional L v hv x) • v :=
  Module.reflection_apply x (reflectionFunctional_apply_self L v hv)

/-- Reflection in a nonsingular vector preserves a symmetric form. -/
theorem finiteFormReflection_isometry (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0)
    (x y : L.obj.carrier) :
    L.obj.pairing (finiteFormReflection L v hv x)
        (finiteFormReflection L v hv y) = L.obj.pairing x y := by
  rw [finiteFormReflection_apply, finiteFormReflection_apply]
  simp only [reflectionFunctional, LinearMap.smul_apply,
    BilinModuleCat.bilinMap_apply]
  change L.obj.bilinMap
      (x - ((2 * (L.obj.pairing v v)⁻¹) * L.obj.pairing v x) • v)
      (y - ((2 * (L.obj.pairing v v)⁻¹) * L.obj.pairing v y) • v) = _
  simp only [map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, BilinModuleCat.bilinMap_apply, smul_eq_mul]
  rw [L.property.2 v x, L.property.2 v y]
  field_simp [hv]
  ring

/-- Reflection in a nonsingular vector as an orthogonal-group element. -/
noncomputable def finiteFormReflectionElement (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) :
    BilinModuleCat.OrthogonalGroup L.obj :=
  ⟨finiteFormReflection L v hv, finiteFormReflection_isometry L v hv⟩

variable [Invertible (2 : K)]

/-- A spinor norm is a group map with the standard value on reflections.

Cassels constructs the spinor norm through the Clifford group and computes a product of
reflections as the product of their quadratic values modulo squares
[@Cas08a, Chapter 10, §3]. -/
def IsSpinorNorm (L : FiniteFormCat K K)
    (ν : BilinModuleCat.OrthogonalGroup L.obj →* FieldSquareClass K) : Prop :=
  ∀ (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0),
    ν (finiteFormReflectionElement L v hv) =
      fieldSquareClass (Units.mk0 (L.obj.pairing v v) hv)

/-- Spinor norms on a finite symmetric form. -/
abbrev SpinorNorm (L : FiniteFormCat K K) :=
  { ν : BilinModuleCat.OrthogonalGroup L.obj →* FieldSquareClass K //
    IsSpinorNorm L ν }

/-- The set of reflections in nonsingular vectors. -/
def finiteFormReflections (L : FiniteFormCat K K) :
    Set (BilinModuleCat.OrthogonalGroup L.obj) :=
  {g | ∃ (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0),
    g = finiteFormReflectionElement L v hv}

/-- Reflections generate the orthogonal group.

This isolates the reflection-generation theorem needed to prove uniqueness of the spinor norm.
-/
def ReflectionsGenerate (L : FiniteFormCat K K) : Prop :=
  Subgroup.closure (finiteFormReflections L) = ⊤

omit [Invertible (2 : K)] in
/-- Two spinor norms agree when reflections generate the orthogonal group. -/
theorem spinorNorm_unique (L : FiniteFormCat K K)
    (hgenerate : ReflectionsGenerate L) (ν μ : SpinorNorm L) : ν = μ := by
  apply Subtype.ext
  apply MonoidHom.eq_of_eqOn_dense hgenerate
  intro g hg
  obtain ⟨v, hv, rfl⟩ := hg
  rw [ν.2 v hv, μ.2 v hv]

/-- Spinor norms form a subsingleton when reflections generate the orthogonal group. -/
instance (L : FiniteFormCat K K) [hgenerate : Fact (ReflectionsGenerate L)] :
    Subsingleton (SpinorNorm L) :=
  ⟨spinorNorm_unique L hgenerate.out⟩

/-- The spinor kernel consists of isometries with trivial spinor norm. -/
def spinorKernel (L : FiniteFormCat K K) (ν : SpinorNorm L) :
    Subgroup (BilinModuleCat.OrthogonalGroup L.obj) :=
  MonoidHom.ker ν.1

/-- A formed automorphism as an element of its orthogonal group. -/
noncomputable def finiteFormAutomorphismElement (L : FiniteFormCat K K)
    (e : L ≅ L) : BilinModuleCat.OrthogonalGroup L.obj := by
  let forgetFiniteForm := ObjectProperty.ι (isFiniteForm K K) ⋙
    LeanCategories.Modules.Bilinear.Valued.forget K K
  refine ⟨(forgetFiniteForm.mapIso e).toLinearEquiv, ?_⟩
  intro x y
  exact BilinModuleCat.map_pairing e.hom.hom x y

/-- The spinor class of one isometry relative to a reference isometry. -/
noncomputable def relativeSpinorClass {L M : FiniteFormCat K K}
    (ν : SpinorNorm L) (reference current : L ≅ M) :
    FieldSquareClass K :=
  ν.1 (finiteFormAutomorphismElement L (current ≪≫ reference.symm))

/-- Two isometries differ by a spinor-kernel element relative to a reference. -/
def IsSpinorEquivalentRelative {L M : FiniteFormCat K K}
    (ν : SpinorNorm L) (reference current : L ≅ M) : Prop :=
  relativeSpinorClass ν reference current = 1

end LeanCategories.Lattices.Valued
