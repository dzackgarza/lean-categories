/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantFunctor
public import LeanCategories.Lattices.Valued.DiscriminantQuadratic
public import LeanCategories.Lattices.Valued.OrthogonalGroup
public import Mathlib.Algebra.Module.Submodule.Pointwise

@[expose] public section

open CategoryTheory
open scoped Pointwise
open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]
variable {L : IntegralLatticeCat R}

namespace OrthogonalGroup

/-- Regard an orthogonal-group element as an automorphism of its integral lattice. -/
def asLatticeIso (g : OrthogonalGroup L) : L ≅ L :=
  ObjectProperty.isoMk (isLattice R R)
    (BilinModuleCat.OrthogonalGroup.toIso g)

/-- The contragredient action of `O(L)` on the value dual. -/
def actOnValueDual (g : OrthogonalGroup L) :
    L.obj.valueDual ≃ₗ[R] L.obj.valueDual :=
  g.1.symm.dualMap

/-- The dual action is the general discriminant transport for the lattice automorphism. -/
theorem actOnValueDual_eq_discriminantValueDualEquiv
    (g : OrthogonalGroup L) :
    actOnValueDual g = discriminantValueDualEquiv (asLatticeIso g) :=
  by
    ext f x
    rfl

/-- The dual action carries an adjoint vector to the adjoint of its image. -/
theorem actOnValueDual_adjoint (g : OrthogonalGroup L)
    (x : L.obj.carrier) :
    actOnValueDual g (L.obj.adjoint x) = L.obj.adjoint (g.1 x) := by
  ext y
  change L.obj.pairing x (g.1.symm y) = L.obj.pairing (g.1 x) y
  simpa using (g.property x (g.1.symm y)).symm

/-- The dual action preserves the image of the adjoint map. -/
theorem actOnValueDual_adjointRange (g : OrthogonalGroup L) :
    (LinearMap.range L.obj.adjoint).map
        (actOnValueDual g).toLinearMap =
      LinearMap.range L.obj.adjoint := by
  ext f
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨g.1 x, (actOnValueDual_adjoint g x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨L.obj.adjoint (g.1.symm x), ⟨g.1.symm x, rfl⟩, ?_⟩
    change actOnValueDual g (L.obj.adjoint (g.1.symm x)) = L.obj.adjoint x
    rw [actOnValueDual_adjoint]
    simp

/-- The action of `O(L)` on the discriminant module `A_L`. -/
def actOnDefect (g : OrthogonalGroup L) :
    L.obj.defect ≃ₗ[R] L.obj.defect :=
  Submodule.Quotient.equiv
    (LinearMap.range L.obj.adjoint)
    (LinearMap.range L.obj.adjoint)
    (actOnValueDual g)
    (actOnValueDual_adjointRange g)

/-- The defect action is the general discriminant transport for the lattice automorphism. -/
theorem actOnDefect_eq_discriminantCarrierEquiv
    (g : OrthogonalGroup L) :
    actOnDefect g = discriminantCarrierEquiv (asLatticeIso g) :=
  by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ f => rfl

@[simp]
theorem actOnDefect_mk (g : OrthogonalGroup L) (f : L.obj.valueDual) :
    actOnDefect g (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (actOnValueDual g f) :=
  rfl

@[simp]
theorem actOnValueDual_one_apply (f : L.obj.valueDual) :
    actOnValueDual (1 : OrthogonalGroup L) f = f := by
  ext x
  rfl

@[simp]
theorem actOnValueDual_mul_apply (g h : OrthogonalGroup L)
    (f : L.obj.valueDual) :
    actOnValueDual (g * h) f =
      actOnValueDual g (actOnValueDual h f) := by
  ext x
  rfl

@[simp]
theorem actOnDefect_one_apply (x : L.obj.defect) :
    actOnDefect (1 : OrthogonalGroup L) x = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ f => simp

@[simp]
theorem actOnDefect_mul_apply (g h : OrthogonalGroup L)
    (x : L.obj.defect) :
    actOnDefect (g * h) x = actOnDefect g (actOnDefect h x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ f => simp

/-- The linear action of `O(L)` on the discriminant module. -/
noncomputable instance defectDistribMulAction :
    DistribMulAction (OrthogonalGroup L) L.obj.defect where
  smul g := actOnDefect g
  one_smul := actOnDefect_one_apply
  mul_smul := actOnDefect_mul_apply
  smul_zero g := (actOnDefect g).map_zero
  smul_add g := (actOnDefect g).map_add

/-- The discriminant action commutes with scalar multiplication. -/
noncomputable instance defectSMulCommClass :
    SMulCommClass (OrthogonalGroup L) R L.obj.defect where
  smul_comm g r x := (actOnDefect g).map_smul r x

/-- The linear action of `O(L)` on its discriminant module. -/
def defectRepresentation :
    OrthogonalGroup L →* (L.obj.defect ≃ₗ[R] L.obj.defect) where
  toFun := actOnDefect
  map_one' := by
    ext x
    exact actOnDefect_one_apply x
  map_mul' g h := by
    ext x
    exact actOnDefect_mul_apply g h x

/-- The orbit of a discriminant submodule under `O(L)`. -/
noncomputable abbrev discriminantSubmoduleOrbit
    (H : Submodule R L.obj.defect) :=
  MulAction.orbit (OrthogonalGroup L) H

/-- The subgroup of `O(L)` that preserves a discriminant submodule. -/
noncomputable abbrev discriminantSubmoduleStabilizer
    (H : Submodule R L.obj.defect) :=
  MulAction.stabilizer (OrthogonalGroup L) H

/-- The scalar extension of an orthogonal action to the rational span. -/
noncomputable def actOnRationalSpan [IsDomain R]
    (g : OrthogonalGroup L) :
    RationalSpan R L ≃ₗ[FractionRing R] RationalSpan R L :=
  g.1.baseChange R (FractionRing R) L.obj.carrier L.obj.carrier

/-- The action of `O(L)` on the metric dual. -/
noncomputable def actOnMetricDual [IsDomain R]
    (g : OrthogonalGroup L) (hL : IsFractionFieldPerfect R L) :
    metricDual R L ≃ₗ[R] metricDual R L :=
  (rieszMetricDualEquiv R L hL).symm |>.trans
    (actOnValueDual g) |>.trans
      (rieszMetricDualEquiv R L hL)

@[simp]
theorem actOnMetricDual_one_apply [IsDomain R]
    (hL : IsFractionFieldPerfect R L) (x : metricDual R L) :
    actOnMetricDual (1 : OrthogonalGroup L) hL x = x := by
  simp [actOnMetricDual]

@[simp]
theorem actOnMetricDual_mul_apply [IsDomain R]
    (g h : OrthogonalGroup L)
    (hL : IsFractionFieldPerfect R L) (x : metricDual R L) :
    actOnMetricDual (g * h) hL x =
      actOnMetricDual g hL (actOnMetricDual h hL x) := by
  simp [actOnMetricDual]

/-- The rational action preserves the extended bilinear form. -/
theorem actOnRationalSpan_isometry [IsDomain R]
    (g : OrthogonalGroup L) (x y : RationalSpan R L) :
    rationalizedForm R L (actOnRationalSpan g x)
        (actOnRationalSpan g y) = rationalizedForm R L x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b y =>
          simp only [actOnRationalSpan, LinearEquiv.baseChange_tmul,
            rationalizedForm_tmul]
          rw [g.property]
      | add y z hy hz => simp [map_add, hy, hz]
  | add x z hx hz => simp [map_add, hx, hz]

@[simp]
theorem actOnRationalSpan_inv_apply [IsDomain R]
    (g : OrthogonalGroup L) (x : RationalSpan R L) :
    actOnRationalSpan g (actOnRationalSpan g⁻¹ x) = x := by
  change (g.1.baseChange R (FractionRing R) L.obj.carrier L.obj.carrier)
    (((g⁻¹).1.baseChange R (FractionRing R)
      L.obj.carrier L.obj.carrier) x) = x
  rw [← LinearEquiv.mul_apply, ← LinearEquiv.baseChange_mul]
  simp

/-- Move an orthogonal action across the rationalized form. -/
theorem rationalizedForm_actOnRationalSpan_left [IsDomain R]
    (g : OrthogonalGroup L) (x y : RationalSpan R L) :
    rationalizedForm R L (actOnRationalSpan g x) y =
      rationalizedForm R L x (actOnRationalSpan g⁻¹ y) := by
  rw [← actOnRationalSpan_isometry g x (actOnRationalSpan g⁻¹ y)]
  rw [actOnRationalSpan_inv_apply]

/-- The Riesz realization intertwines the dual and rational actions. -/
theorem rieszEmbedding_actOnValueDual [IsDomain R]
    (g : OrthogonalGroup L)
    (hL : IsFractionFieldPerfect R L) (f : L.obj.valueDual) :
    rieszEmbedding R L hL (actOnValueDual g f) =
      actOnRationalSpan g (rieszEmbedding R L hL f) := by
  apply (rationalAdjointEquiv R L hL).injective
  rw [show (rationalAdjointEquiv R L hL)
      (rieszEmbedding R L hL (actOnValueDual g f)) =
        Module.Dual.baseChange (FractionRing R) (actOnValueDual g f) by
    simp [rieszEmbedding]]
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      change Module.Dual.baseChange (FractionRing R) (actOnValueDual g f)
          (a ⊗ₜ[R] x) =
        rationalizedForm R L (actOnRationalSpan g
          (rieszEmbedding R L hL f)) (a ⊗ₜ[R] x)
      rw [Module.Dual.baseChange_apply_tmul,
        rationalizedForm_actOnRationalSpan_left]
      change (f (g.1.symm x)) • a =
        rationalizedForm R L (rieszEmbedding R L hL f)
          (a ⊗ₜ[R] g.1.symm x)
      have htensor : (a ⊗ₜ[R] g.1.symm x) =
          a • toRationalSpan R L (g.1.symm x) := by
        exact TensorProduct.tmul_eq_smul_one_tmul a (g.1.symm x)
      rw [htensor]
      rw [map_smul, rationalizedForm_rieszEmbedding]
      simp [Algebra.smul_def, mul_comm]
  | add x y hx hy => simp [map_add, hx, hy]

@[simp]
theorem metricDualToValueDual_actOnMetricDual [IsDomain R]
    (g : OrthogonalGroup L)
    (hL : IsFractionFieldPerfect R L) (x : metricDual R L) :
    metricDualToValueDual R L (actOnMetricDual g hL x) =
      actOnValueDual g (metricDualToValueDual R L x) := by
  change metricDualToValueDual R L
      (rieszToMetricDual R L hL
        (actOnValueDual g (metricDualToValueDual R L x))) = _
  rw [metricDualToValueDual_rieszToMetricDual]

/-- The metric-dual action is the restriction of the rational action. -/
theorem actOnMetricDual_coe [IsDomain R]
    (g : OrthogonalGroup L)
    (hL : IsFractionFieldPerfect R L) (x : metricDual R L) :
    (actOnMetricDual g hL x : RationalSpan R L) =
      actOnRationalSpan g x := by
  change rieszEmbedding R L hL
      (actOnValueDual g (metricDualToValueDual R L x)) =
    actOnRationalSpan g x
  rw [rieszEmbedding_actOnValueDual]
  congr 1
  exact congrArg Subtype.val
    (rieszToMetricDual_metricDualToValueDual R L hL x)

/-- The metric-dual and discriminant actions commute with the quotient map. -/
theorem metricDualToDiscriminant_actOnMetricDual [IsDomain R]
    (g : OrthogonalGroup L)
    (hL : IsFractionFieldPerfect R L) (x : metricDual R L) :
    metricDualToDiscriminant R L (actOnMetricDual g hL x) =
      actOnDefect g (metricDualToDiscriminant R L x) := by
  change Submodule.Quotient.mk
      (metricDualToValueDual R L (actOnMetricDual g hL x)) =
    actOnDefect g (Submodule.Quotient.mk (metricDualToValueDual R L x))
  rw [metricDualToValueDual_actOnMetricDual, actOnDefect_mk]

/-- The dual action preserves the Riesz bilinear form. -/
theorem rieszDualBilinMap_actOnValueDual [IsDomain R]
    (g : OrthogonalGroup L)
    (hL : IsFractionFieldPerfect R L) (f k : L.obj.valueDual) :
    rieszDualBilinMap R L hL (actOnValueDual g f)
        (actOnValueDual g k) = rieszDualBilinMap R L hL f k := by
  change rationalizedForm R L
      (rieszEmbedding R L hL (actOnValueDual g f))
      (rieszEmbedding R L hL (actOnValueDual g k)) =
    rationalizedForm R L (rieszEmbedding R L hL f)
      (rieszEmbedding R L hL k)
  rw [rieszEmbedding_actOnValueDual, rieszEmbedding_actOnValueDual]
  exact actOnRationalSpan_isometry g _ _

/-- The action on `A_L` preserves its discriminant bilinear form. -/
theorem discriminantBilinMap_actOnDefect [IsDomain R]
    (g : OrthogonalGroup L)
    (hL : IsFractionFieldPerfect R L) (x y : L.obj.defect) :
    discriminantBilinMap R L hL (actOnDefect g x) (actOnDefect g y) =
      discriminantBilinMap R L hL x y := by
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
      induction y using Submodule.Quotient.induction_on with
      | _ k =>
          simp only [actOnDefect_mk, discriminantBilinMap_mk]
          rw [rieszDualBilinMap_actOnValueDual]

/-- The induced isometry of the discriminant bilinear module. -/
noncomputable def actOnDiscriminantForm [IsDomain R]
    (g : OrthogonalGroup L)
    (hL : IsFractionFieldPerfect R L) :
    BilinModuleCat.OrthogonalGroup (discriminantBilinObject R L hL) :=
  ⟨actOnDefect g, discriminantBilinMap_actOnDefect g hL⟩

/-- The discriminant-form action is the functorial transport of the lattice automorphism. -/
theorem underlyingMap_discriminantBilinIso_asLatticeIso [IsDomain R]
    (g : OrthogonalGroup L)
    (hL : IsFractionFieldPerfect R L) :
    BilinModuleCat.underlyingMap
        (discriminantBilinIso (asLatticeIso g) hL hL).hom =
      (actOnDiscriminantForm g hL).1.toLinearMap :=
  by
    ext x
    rfl

/-- The natural homomorphism `O(L) → O(A_L)`. -/
noncomputable def discriminantRepresentation [IsDomain R]
    (hL : IsFractionFieldPerfect R L) :
    OrthogonalGroup L →*
      BilinModuleCat.OrthogonalGroup (discriminantBilinObject R L hL) where
  toFun := fun g ↦ actOnDiscriminantForm g hL
  map_one' := by
    apply Subtype.ext
    ext x
    exact actOnDefect_one_apply x
  map_mul' g h := by
    apply Subtype.ext
    ext x
    exact actOnDefect_mul_apply g h x

/-- The stable orthogonal group, which acts trivially on `A_L`. -/
noncomputable def stableOrthogonalGroup [IsDomain R]
    (hL : IsFractionFieldPerfect R L) :
    Subgroup (OrthogonalGroup L) :=
  MonoidHom.ker (discriminantRepresentation hL)

/-- The action on `A_L` preserves the even discriminant quadratic form. -/
theorem evenDiscriminantQuadraticMap_actOnDefect [IsDomain R]
    (g : OrthogonalGroup L)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (x : L.obj.defect) :
    evenDiscriminantQuadraticMap L hL hEven (actOnDefect g x) =
      evenDiscriminantQuadraticMap L hL hEven x := by
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
      simp only [actOnDefect_mk, evenDiscriminantQuadraticMap_mk]
      rw [rieszDualBilinMap_actOnValueDual]

/-- The induced isometry of the even quadratic discriminant module. -/
noncomputable def actOnEvenDiscriminantQuadraticForm [IsDomain R]
    (g : OrthogonalGroup L)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L) :
    QuadModuleCat.OrthogonalGroup
      (evenDiscriminantQuadraticObject L hL hEven) :=
  ⟨actOnDefect g, evenDiscriminantQuadraticMap_actOnDefect g hL hEven⟩

/-- The natural homomorphism `O(L) → O(q_A)` for an even lattice. -/
noncomputable def evenDiscriminantRepresentation [IsDomain R]
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L) :
    OrthogonalGroup L →*
      QuadModuleCat.OrthogonalGroup
        (evenDiscriminantQuadraticObject L hL hEven) where
  toFun := fun g ↦ actOnEvenDiscriminantQuadraticForm g hL hEven
  map_one' := by
    apply Subtype.ext
    ext x
    exact actOnDefect_one_apply x
  map_mul' g h := by
    apply Subtype.ext
    ext x
    exact actOnDefect_mul_apply g h x

/-- The subgroup of `O(L)` that acts trivially on `q_A`. -/
noncomputable def stableEvenOrthogonalGroup [IsDomain R]
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L) :
    Subgroup (OrthogonalGroup L) :=
  MonoidHom.ker (evenDiscriminantRepresentation hL hEven)

end OrthogonalGroup

end LeanCategories.Lattices.Valued
