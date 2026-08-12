/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.BaseChange

/-!
# Scalar extension of isometries

`baseChangeFiniteIntegral` is a functor, so an isometry `L ≅ M` of finite projective integral
lattices extends to an isometry of the scalar extensions, and the extension respects identity,
composition and inverse. This file names that isometry and records the two facts a local
comparison argument needs: the extension of an isometry on the generators `1 ⊗ₜ x`, and the
converse that agreement on those generators forces equality of maps.
-/

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u v

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-! ### Agreement on generators -/

/-- Two `S`-linear maps out of a scalar extension are equal when they agree on the pure
tensors `1 ⊗ₜ x`. -/
theorem baseChange_ext {P N : Type v} [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module S N] {f g : TensorProduct R S P →ₗ[S] N}
    (h : ∀ x : P, f (1 ⊗ₜ[R] x) = g (1 ⊗ₜ[R] x)) :
    f = g := by
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    have ha : (a ⊗ₜ[R] x : TensorProduct R S P) = a • (1 ⊗ₜ[R] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ha, map_smul, map_smul, h]
  | add z w hz hw => rw [map_add, map_add, hz, hw]

/-- Two morphisms out of a scalar-extended lattice are equal when the underlying maps agree
on the generators `1 ⊗ₜ x`. -/
theorem baseChangeFiniteIntegral_hom_ext
    {L : FiniteProjectiveLatticeCat R R} {N : FiniteProjectiveLatticeCat S S}
    {f g : (baseChangeFiniteIntegral R S).obj L ⟶ N}
    (h : ∀ x : L.obj.obj.carrier,
      ((finiteProjectiveForget S S).map f).hom (1 ⊗ₜ[R] x) =
        ((finiteProjectiveForget S S).map g).hom (1 ⊗ₜ[R] x)) :
    f = g := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  apply ModuleCat.hom_ext
  exact baseChange_ext R S h

/-! ### Scalar extension of an isometry -/

variable {L M N : FiniteProjectiveLatticeCat R R}

/-- The isometry of scalar extensions induced by an isometry of lattices. -/
noncomputable def baseChangeIsometry (e : L ≅ M) :
    (baseChangeFiniteIntegral R S).obj L ≅ (baseChangeFiniteIntegral R S).obj M :=
  (baseChangeFiniteIntegral R S).mapIso e

@[simp]
theorem baseChangeIsometry_refl (L : FiniteProjectiveLatticeCat R R) :
    baseChangeIsometry R S (Iso.refl L) = Iso.refl ((baseChangeFiniteIntegral R S).obj L) :=
  Functor.mapIso_refl _ _

theorem baseChangeIsometry_trans (e : L ≅ M) (f : M ≅ N) :
    baseChangeIsometry R S (e ≪≫ f) =
      baseChangeIsometry R S e ≪≫ baseChangeIsometry R S f :=
  Functor.mapIso_trans _ _ _

theorem baseChangeIsometry_symm (e : L ≅ M) :
    baseChangeIsometry R S e.symm = (baseChangeIsometry R S e).symm :=
  Functor.mapIso_symm _ _

/-- The scalar extension of an isometry sends `a ⊗ₜ x` to `a ⊗ₜ e x`.

Not a `simp` lemma: the left-hand side is not in simp-normal form, since the coercion of the
mapped isomorphism simplifies further. -/
theorem baseChangeIsometry_apply_tmul (e : L ≅ M) (a : S) (x : L.obj.obj.carrier) :
    ((finiteProjectiveForget S S).mapIso (baseChangeIsometry R S e)).toLinearEquiv
        (a ⊗ₜ[R] x) =
      a ⊗ₜ[R] ((finiteProjectiveForget R R).mapIso e).toLinearEquiv x :=
  rfl

end LeanCategories.Lattices.Valued
