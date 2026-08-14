/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Discriminant
public import Mathlib.CategoryTheory.Core

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable {L M N : IntegralLatticeCat R}

/-- The nonsingular finite torsion form property with values in `Frac(R) / R`. -/
abbrev isNonsingularDiscriminantForm (R : Type u) [CommRing R] [IsDomain R] :=
  isNonsingularFiniteTorsionBilinModule R (FractionValueQuotient R)

/-- Nonsingular finite torsion forms with values in `Frac(R) / R`. -/
abbrev NonsingularDiscriminantFormCat (R : Type u) [CommRing R] [IsDomain R] :=
  (isNonsingularDiscriminantForm R).FullSubcategory

/-- The carrier equivalence underlying an isomorphism of integral lattices. -/
noncomputable def latticeIsoLinearEquiv (e : L ≅ M) :
    L.obj.carrier ≃ₗ[R] M.obj.carrier :=
  ((isLattice R R).ι ⋙ forget R R).mapIso e |>.toLinearEquiv

omit [IsDomain R] in
@[simp]
theorem latticeIsoLinearEquiv_apply (e : L ≅ M) (x : L.obj.carrier) :
    latticeIsoLinearEquiv e x = BilinModuleCat.underlyingMap e.hom.hom x :=
  rfl

omit [IsDomain R] in
/-- An integral-lattice isomorphism preserves its form. -/
theorem latticeIsoLinearEquiv_pairing (e : L ≅ M)
    (x y : L.obj.carrier) :
    M.obj.pairing (latticeIsoLinearEquiv e x)
        (latticeIsoLinearEquiv e y) = L.obj.pairing x y :=
  BilinModuleCat.map_pairing e.hom.hom x y

/-- The contragredient equivalence on value duals. -/
noncomputable def discriminantValueDualEquiv (e : L ≅ M) :
    L.obj.valueDual ≃ₗ[R] M.obj.valueDual :=
  (latticeIsoLinearEquiv e).symm.dualMap

omit [IsDomain R] in
/-- The contragredient equivalence carries adjoint vectors to adjoint vectors. -/
theorem discriminantValueDualEquiv_adjoint (e : L ≅ M)
    (x : L.obj.carrier) :
    discriminantValueDualEquiv e (L.obj.adjoint x) =
      M.obj.adjoint (latticeIsoLinearEquiv e x) := by
  ext y
  change L.obj.pairing x ((latticeIsoLinearEquiv e).symm y) =
    M.obj.pairing (latticeIsoLinearEquiv e x) y
  simpa using
    (latticeIsoLinearEquiv_pairing e x
      ((latticeIsoLinearEquiv e).symm y)).symm

omit [IsDomain R] in
/-- The contragredient equivalence identifies the two adjoint ranges. -/
theorem discriminantValueDualEquiv_adjointRange (e : L ≅ M) :
    (LinearMap.range L.obj.adjoint).map
        (discriminantValueDualEquiv e).toLinearMap =
      LinearMap.range M.obj.adjoint := by
  ext f
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨latticeIsoLinearEquiv e x,
      (discriminantValueDualEquiv_adjoint e x).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨L.obj.adjoint ((latticeIsoLinearEquiv e).symm y),
      ⟨(latticeIsoLinearEquiv e).symm y, rfl⟩, ?_⟩
    exact (discriminantValueDualEquiv_adjoint e
      ((latticeIsoLinearEquiv e).symm y)).trans (by simp)

/-- An integral-lattice isomorphism induces an equivalence of discriminant carriers. -/
noncomputable def discriminantCarrierEquiv (e : L ≅ M) :
    L.obj.defect ≃ₗ[R] M.obj.defect :=
  Submodule.Quotient.equiv
    (LinearMap.range L.obj.adjoint)
    (LinearMap.range M.obj.adjoint)
    (discriminantValueDualEquiv e)
    (discriminantValueDualEquiv_adjointRange e)

omit [IsDomain R] in
@[simp]
theorem discriminantCarrierEquiv_mk (e : L ≅ M)
    (f : L.obj.valueDual) :
    discriminantCarrierEquiv e (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (discriminantValueDualEquiv e f) :=
  rfl

omit [IsDomain R] in
@[simp]
theorem discriminantCarrierEquiv_refl_apply (x : L.obj.defect) :
    discriminantCarrierEquiv (Iso.refl L) x = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ f => rfl

omit [IsDomain R] in
@[simp]
theorem discriminantCarrierEquiv_trans_apply (e : L ≅ M) (f : M ≅ N)
    (x : L.obj.defect) :
    discriminantCarrierEquiv (e ≪≫ f) x =
      discriminantCarrierEquiv f (discriminantCarrierEquiv e x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ g => rfl

/-- The scalar extension of an integral-lattice isomorphism. -/
noncomputable def latticeIsoRationalSpanEquiv (e : L ≅ M) :
    RationalSpan R L ≃ₗ[FractionRing R] RationalSpan R M :=
  (latticeIsoLinearEquiv e).baseChange R (FractionRing R)
    L.obj.carrier M.obj.carrier

omit [IsDomain R] in
/-- Scalar extension preserves the rationalized forms. -/
theorem latticeIsoRationalSpanEquiv_pairing (e : L ≅ M)
    (x : RationalSpan R L) (y : RationalSpan R L) :
    rationalizedForm R M (latticeIsoRationalSpanEquiv e x)
        (latticeIsoRationalSpanEquiv e y) =
      rationalizedForm R L x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b y =>
          simp only [latticeIsoRationalSpanEquiv,
            LinearEquiv.baseChange_tmul, rationalizedForm_tmul]
          rw [latticeIsoLinearEquiv_pairing]
      | add y z hy hz => simp [map_add, hy, hz]
  | add x z hx hz => simp [map_add, hx, hz]

omit [IsDomain R] in
/-- Move an isometry across the rationalized form. -/
theorem rationalizedForm_latticeIso_left (e : L ≅ M)
    (x : RationalSpan R L) (y : RationalSpan R M) :
    rationalizedForm R M (latticeIsoRationalSpanEquiv e x) y =
      rationalizedForm R L x ((latticeIsoRationalSpanEquiv e).symm y) := by
  rw [← latticeIsoRationalSpanEquiv_pairing e x
    ((latticeIsoRationalSpanEquiv e).symm y)]
  simp

omit [IsDomain R] in
/-- The Riesz realization is natural under integral-lattice isomorphisms. -/
theorem rieszEmbedding_latticeIso (e : L ≅ M)
    (hL : IsFractionFieldPerfect R L)
    (hM : IsFractionFieldPerfect R M) (f : L.obj.valueDual) :
    rieszEmbedding R M hM (discriminantValueDualEquiv e f) =
      latticeIsoRationalSpanEquiv e (rieszEmbedding R L hL f) := by
  apply (rationalAdjointEquiv R M hM).injective
  rw [show (rationalAdjointEquiv R M hM)
      (rieszEmbedding R M hM (discriminantValueDualEquiv e f)) =
        Module.Dual.baseChange (FractionRing R)
          (discriminantValueDualEquiv e f) by simp [rieszEmbedding]]
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      change Module.Dual.baseChange (FractionRing R)
          (discriminantValueDualEquiv e f) (a ⊗ₜ[R] y) =
        rationalizedForm R M
          (latticeIsoRationalSpanEquiv e (rieszEmbedding R L hL f))
          (a ⊗ₜ[R] y)
      rw [Module.Dual.baseChange_apply_tmul,
        rationalizedForm_latticeIso_left]
      change (discriminantValueDualEquiv e f) y • a =
        rationalizedForm R L (rieszEmbedding R L hL f)
          (((latticeIsoLinearEquiv e).baseChange R (FractionRing R)
            L.obj.carrier M.obj.carrier).symm (a ⊗ₜ[R] y))
      rw [LinearEquiv.baseChange_symm_tmul]
      change (f ((latticeIsoLinearEquiv e).symm y)) • a =
        rationalizedForm R L (rieszEmbedding R L hL f)
          (a ⊗ₜ[R] (latticeIsoLinearEquiv e).symm y)
      have htensor :
          (a ⊗ₜ[R] (latticeIsoLinearEquiv e).symm y) =
            a • toRationalSpan R L ((latticeIsoLinearEquiv e).symm y) := by
        exact TensorProduct.tmul_eq_smul_one_tmul a _
      rw [htensor, map_smul, rationalizedForm_rieszEmbedding]
      simp [Algebra.smul_def, mul_comm]
  | add x y hx hy => simp [map_add, hx, hy]

omit [IsDomain R] in
/-- An integral-lattice isomorphism preserves the Riesz form on value duals. -/
theorem rieszDualBilinMap_latticeIso (e : L ≅ M)
    (hL : IsFractionFieldPerfect R L)
    (hM : IsFractionFieldPerfect R M) (f g : L.obj.valueDual) :
    rieszDualBilinMap R M hM (discriminantValueDualEquiv e f)
        (discriminantValueDualEquiv e g) =
      rieszDualBilinMap R L hL f g := by
  change rationalizedForm R M
      (rieszEmbedding R M hM (discriminantValueDualEquiv e f))
      (rieszEmbedding R M hM (discriminantValueDualEquiv e g)) =
    rationalizedForm R L (rieszEmbedding R L hL f)
      (rieszEmbedding R L hL g)
  rw [rieszEmbedding_latticeIso, rieszEmbedding_latticeIso]
  exact latticeIsoRationalSpanEquiv_pairing e _ _

omit [IsDomain R] in
/-- An integral-lattice isomorphism preserves the discriminant bilinear form. -/
theorem discriminantBilinMap_latticeIso (e : L ≅ M)
    (hL : IsFractionFieldPerfect R L)
    (hM : IsFractionFieldPerfect R M) (x y : L.obj.defect) :
    discriminantBilinMap R M hM (discriminantCarrierEquiv e x)
        (discriminantCarrierEquiv e y) =
      discriminantBilinMap R L hL x y := by
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
      induction y using Submodule.Quotient.induction_on with
      | _ g =>
          simp only [discriminantCarrierEquiv_mk, discriminantBilinMap_mk]
          rw [rieszDualBilinMap_latticeIso]

/-- An integral-lattice isomorphism induces an isomorphism of discriminant forms. -/
noncomputable def discriminantBilinIso (e : L ≅ M)
    (hL : IsFractionFieldPerfect R L)
    (hM : IsFractionFieldPerfect R M) :
    discriminantBilinObject R L hL ≅ discriminantBilinObject R M hM := by
  let d := discriminantCarrierEquiv e
  have hd (x y : L.obj.defect) :
      (discriminantBilinObject R M hM).pairing (d x) (d y) =
        (discriminantBilinObject R L hL).pairing x y :=
    discriminantBilinMap_latticeIso e hL hM x y
  have hdSymm (x y : M.obj.defect) :
      (discriminantBilinObject R L hL).pairing (d.symm x) (d.symm y) =
        (discriminantBilinObject R M hM).pairing x y := by
    obtain ⟨x, rfl⟩ := d.surjective x
    obtain ⟨y, rfl⟩ := d.surjective y
    simpa only [LinearEquiv.symm_apply_apply] using (hd x y).symm
  exact {
    hom := BilinModuleCat.homMk d.toLinearMap hd
    inv := BilinModuleCat.homMk d.symm.toLinearMap hdSymm
    hom_inv_id := by
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      ext x
      exact d.symm_apply_apply x
    inv_hom_id := by
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      ext x
      exact d.apply_symm_apply x }

local instance (priority := 10000) moduleIntFractionRing :
    Module ℤ (FractionRing ℤ) :=
  Algebra.toModule

local instance (priority := 10000) moduleIntFractionValueQuotient :
    Module ℤ (FractionValueQuotient ℤ) :=
  Submodule.Quotient.module (Algebra.linearMap ℤ (FractionRing ℤ)).range

/-- The nonsingular discriminant form of a finite projective integral lattice. -/
noncomputable def integralDiscriminantFormObject
    (L : FractionFieldPerfectFiniteProjectiveLatticeCat ℤ) :
    NonsingularDiscriminantFormCat ℤ := by
  letI : Module.Finite ℤ L.obj.obj.obj.carrier := L.obj.property
  exact discriminantNonsingularTorsionFormModuleInt L.obj.obj L.property

/-- Forget a finite projective lattice isomorphism to an integral lattice isomorphism. -/
def integralLatticeIso
    {L M : FractionFieldPerfectFiniteProjectiveLatticeCat ℤ}
    (e : L ≅ M) : L.obj.obj ≅ M.obj.obj :=
  (fractionFieldPerfectFiniteProjectiveForget ℤ).mapIso e

/-- An integral lattice isomorphism induces an isomorphism of nonsingular discriminant forms. -/
noncomputable def integralDiscriminantFormIso
    {L M : FractionFieldPerfectFiniteProjectiveLatticeCat ℤ}
    (e : L ≅ M) :
    integralDiscriminantFormObject L ≅ integralDiscriminantFormObject M :=
  ObjectProperty.isoMk
    (isNonsingularDiscriminantForm ℤ)
    (discriminantBilinIso (integralLatticeIso e) L.property M.property)

@[simp]
theorem underlyingMap_integralDiscriminantFormIso_hom
    {L M : FractionFieldPerfectFiniteProjectiveLatticeCat ℤ}
    (e : L ≅ M) :
    BilinModuleCat.underlyingMap (integralDiscriminantFormIso e).hom.hom =
      (discriminantCarrierEquiv (integralLatticeIso e)).toLinearMap :=
  rfl

/--
The nonsingular discriminant form as a functor on the isomorphism core.

The source and target are `Core` categories on purpose.  The construction
transports a lattice isometry to an isomorphism of discriminant forms; this
declaration does not claim an extension to arbitrary lattice morphisms.
-/
noncomputable def integralDiscriminantFormFunctor :
    Core (FractionFieldPerfectFiniteProjectiveLatticeCat ℤ) ⥤
      Core (NonsingularDiscriminantFormCat ℤ) where
  obj L := ⟨integralDiscriminantFormObject L.of⟩
  map e := ⟨integralDiscriminantFormIso e.iso⟩
  map_id L := by
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    change BilinModuleCat.underlyingMap
      (integralDiscriminantFormIso (Iso.refl L.of)).hom.hom x = x
    rw [underlyingMap_integralDiscriminantFormIso_hom]
    exact discriminantCarrierEquiv_refl_apply x
  map_comp e f := by
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    change BilinModuleCat.underlyingMap
      (integralDiscriminantFormIso (e.iso ≪≫ f.iso)).hom.hom x =
        BilinModuleCat.underlyingMap
          (integralDiscriminantFormIso f.iso).hom.hom
          (BilinModuleCat.underlyingMap
            (integralDiscriminantFormIso e.iso).hom.hom x)
    rw [underlyingMap_integralDiscriminantFormIso_hom,
      underlyingMap_integralDiscriminantFormIso_hom,
      underlyingMap_integralDiscriminantFormIso_hom]
    exact discriminantCarrierEquiv_trans_apply
      (integralLatticeIso e.iso) (integralLatticeIso f.iso) x

end LeanCategories.Lattices.Valued
