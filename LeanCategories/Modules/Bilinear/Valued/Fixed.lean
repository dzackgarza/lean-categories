/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Map

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- The contravariant functor of `W`-valued bilinear forms on `R`-modules. -/
def bilinearForms : (ModuleCat.{u} R)ᵒᵖ ⥤ Type u where
  obj M := TensorProduct R ((M.unop : ModuleCat R) : Type u)
    ((M.unop : ModuleCat R) : Type u) →ₗ[R] W
  map f := ↾fun b ↦ b.comp (TensorProduct.map f.unop.hom f.unop.hom)
  map_id M := by
    ext b x y
    simp
  map_comp f g := by
    ext b x y
    simp

/-- The category of `W`-valued bilinear forms on `R`-modules. -/
abbrev BilinModuleCat := (bilinearForms R W).Elementsᵒᵖ

namespace BilinModuleCat

variable {R W}

/-- Make a bilinear-module object from a bilinear map. -/
def ofBilinMap {M : Type u} [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinMap R M W) : BilinModuleCat R W :=
  op ⟨op (ModuleCat.of R M),
    (TensorProduct.lift.equiv (.id R) M M W) B⟩

/-- The underlying `R`-module. -/
def carrierObj (L : BilinModuleCat R W) : ModuleCat R :=
  (unop L).1.unop

abbrev carrier (L : BilinModuleCat R W) := L.carrierObj

/-- The tensor-hom form of a bilinear module. -/
def form (L : BilinModuleCat R W) :
    TensorProduct R (L.carrier : Type u) (L.carrier : Type u) →ₗ[R] W :=
  (unop L).2

/-- The value of the form on a pair. -/
def pairing (L : BilinModuleCat R W) (x y : L.carrier) : W :=
  L.form (x ⊗ₜ[R] y)

@[simp]
theorem ofBilinMap_pairing {M : Type u} [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinMap R M W) (x y : M) :
    (ofBilinMap B).pairing x y = B x y :=
  rfl

@[simp]
theorem pairing_zero_left (L : BilinModuleCat R W) (y : L.carrier) :
    L.pairing 0 y = 0 := by
  simp [pairing]

@[simp]
theorem pairing_zero_right (L : BilinModuleCat R W) (x : L.carrier) :
    L.pairing x 0 = 0 := by
  simp [pairing]

@[simp]
theorem pairing_add_left (L : BilinModuleCat R W) (x y z : L.carrier) :
    L.pairing (x + y) z = L.pairing x z + L.pairing y z := by
  simp [pairing, TensorProduct.add_tmul]

@[simp]
theorem pairing_add_right (L : BilinModuleCat R W) (x y z : L.carrier) :
    L.pairing x (y + z) = L.pairing x y + L.pairing x z := by
  simp [pairing, TensorProduct.tmul_add]

@[simp]
theorem pairing_smul_left (L : BilinModuleCat R W) (r : R) (x y : L.carrier) :
    L.pairing (r • x) y = r • L.pairing x y := by
  rw [pairing, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
  rfl

@[simp]
theorem pairing_smul_right (L : BilinModuleCat R W) (r : R) (x y : L.carrier) :
    L.pairing x (r • y) = r • L.pairing x y := by
  rw [pairing, TensorProduct.tmul_smul, map_smul]
  rfl

/-- The underlying linear map of a morphism. -/
def underlyingMap {L M : BilinModuleCat R W} (f : L ⟶ M) :
    L.carrier →ₗ[R] M.carrier :=
  f.unop.val.unop.hom

/-- Morphisms preserve the bilinear form. -/
theorem map_pairing {L M : BilinModuleCat R W} (f : L ⟶ M)
    (x y : L.carrier) :
    M.pairing (underlyingMap f x) (underlyingMap f y) = L.pairing x y := by
  have h := f.unop.property
  exact LinearMap.congr_fun h (x ⊗ₜ[R] y)

/-- Build a formed-module morphism from a form-preserving linear map. -/
def homMk {L M : BilinModuleCat R W} (f : L.carrier →ₗ[R] M.carrier)
    (h : ∀ x y, M.pairing (f x) (f y) = L.pairing x y) : L ⟶ M := by
  refine Quiver.Hom.op (CategoryOfElements.homMk _ _
    (op (ModuleCat.ofHom f)) ?_)
  dsimp [bilinearForms]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => exact h x y
  | add x y hx hy => simp [hx, hy]

@[simp]
theorem underlyingMap_homMk {L M : BilinModuleCat R W}
    (f : L.carrier →ₗ[R] M.carrier)
    (h : ∀ x y, M.pairing (f x) (f y) = L.pairing x y) :
    underlyingMap (homMk f h) = f :=
  rfl

/-- Symmetry of the form. -/
def IsSymmetric (L : BilinModuleCat R W) : Prop :=
  ∀ x y, L.pairing x y = L.pairing y x

/-- Skew-symmetry of the form. -/
def IsSkewSymmetric (L : BilinModuleCat R W) : Prop :=
  ∀ x y, L.pairing x y = -L.pairing y x

/-- Alternation of the form. -/
def IsAlternating (L : BilinModuleCat R W) : Prop :=
  ∀ x, L.pairing x x = 0

/-- Every alternating bilinear form is skew-symmetric. -/
theorem isSkewSymmetric_of_isAlternating (L : BilinModuleCat R W)
    (hL : L.IsAlternating) : L.IsSkewSymmetric := by
  intro x y
  apply eq_neg_of_add_eq_zero_left
  calc
    L.pairing x y + L.pairing y x = L.pairing (x + y) (x + y) := by
      rw [BilinModuleCat.pairing_add_left, BilinModuleCat.pairing_add_right,
        BilinModuleCat.pairing_add_right, hL x, hL y]
      simp
    _ = 0 := hL (x + y)

/-- The module adjoint `L → Hom_R(L,W)`. No formed structure on the codomain is implied. -/
def adjoint (L : BilinModuleCat R W) :
    L.carrier →ₗ[R] (L.carrier →ₗ[R] W) :=
  (TensorProduct.lift.equiv (.id R) L.carrier L.carrier W).symm L.form

abbrev bilinMap (L : BilinModuleCat R W) := L.adjoint

@[simp]
theorem bilinMap_apply (L : BilinModuleCat R W) (x y : L.carrier) :
    L.bilinMap x y = L.pairing x y :=
  rfl

/-- Restrict a formed module to a submodule. -/
def restrict (L : BilinModuleCat R W) (P : Submodule R L.carrier) :
    BilinModuleCat R W :=
  ofBilinMap (LinearMap.domRestrict₁₂ L.bilinMap P P)

@[simp]
theorem restrict_pairing (L : BilinModuleCat R W) (P : Submodule R L.carrier)
    (x y : P) :
    (L.restrict P).pairing x y = L.pairing x y :=
  rfl

/-- The inclusion of a restricted formed module. -/
def restrictInclusion (L : BilinModuleCat R W) (P : Submodule R L.carrier) :
    L.restrict P ⟶ L :=
  homMk P.subtype fun _ _ ↦ rfl

@[simp]
theorem underlyingMap_restrictInclusion
    (L : BilinModuleCat R W) (P : Submodule R L.carrier) :
    underlyingMap (L.restrictInclusion P) = P.subtype :=
  rfl

/-- The radical is the kernel of the adjoint map. -/
def radical (L : BilinModuleCat R W) : Submodule R L.carrier :=
  LinearMap.ker L.adjoint

/-- The module of `W`-valued linear maps. It has no canonical induced form. -/
abbrev valueDual (L : BilinModuleCat R W) := L.carrier →ₗ[R] W

/-- The cokernel of the adjoint map. -/
abbrev defect (L : BilinModuleCat R W) :=
  L.valueDual ⧸ LinearMap.range L.adjoint

def radicalInclusion (L : BilinModuleCat R W) :
    L.radical →ₗ[R] L.carrier :=
  L.radical.subtype

def defectProjection (L : BilinModuleCat R W) :
    L.valueDual →ₗ[R] L.defect :=
  Submodule.mkQ (LinearMap.range L.adjoint)

theorem exact_radical_adjoint (L : BilinModuleCat R W) :
    Function.Exact L.radicalInclusion L.adjoint :=
  LinearMap.exact_subtype_ker_map L.adjoint

theorem exact_adjoint_defect (L : BilinModuleCat R W) :
    Function.Exact L.adjoint L.defectProjection :=
  LinearMap.exact_map_mkQ_range L.adjoint

theorem radicalInclusion_injective (L : BilinModuleCat R W) :
    Function.Injective L.radicalInclusion :=
  Subtype.val_injective

theorem defectProjection_surjective (L : BilinModuleCat R W) :
    Function.Surjective L.defectProjection :=
  Submodule.mkQ_surjective _

/-- A form is nondegenerate when its radical is zero. -/
def IsNondegenerate (L : BilinModuleCat R W) : Prop :=
  L.radical = ⊥

theorem isNondegenerate_iff_adjoint_injective (L : BilinModuleCat R W) :
    L.IsNondegenerate ↔ Function.Injective L.adjoint := by
  exact LinearMap.ker_eq_bot

/-- A form is perfect when its adjoint map is bijective. -/
def IsPerfect (L : BilinModuleCat R W) : Prop :=
  Function.Bijective L.adjoint

/-- A perfect form has zero radical. -/
theorem isNondegenerate_of_isPerfect (L : BilinModuleCat R W)
    (hL : L.IsPerfect) : L.IsNondegenerate :=
  L.isNondegenerate_iff_adjoint_injective.mpr hL.1

end BilinModuleCat

/-- The forgetful functor to `R`-modules. -/
def forget : BilinModuleCat R W ⥤ ModuleCat R where
  obj := BilinModuleCat.carrierObj
  map := fun f ↦ ModuleCat.ofHom (BilinModuleCat.underlyingMap f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Symmetric objects in the fixed-value bilinear-module category. -/
def isSymmetricBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun L ↦ L.IsSymmetric

/-- Fixed-value symmetric bilinear modules. -/
abbrev SymBilinModuleCat := (isSymmetricBilinModule R W).FullSubcategory

/-- Skew-symmetric objects in the fixed-value bilinear-module category. -/
def isSkewSymmetricBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun L ↦ L.IsSkewSymmetric

/-- Fixed-value skew-symmetric bilinear modules. -/
abbrev SkewBilinModuleCat := (isSkewSymmetricBilinModule R W).FullSubcategory

/-- Alternating objects in the fixed-value bilinear-module category. -/
def isAlternatingBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun L ↦ L.IsAlternating

/-- Fixed-value alternating bilinear modules. -/
abbrev AltBilinModuleCat := (isAlternatingBilinModule R W).FullSubcategory

/-- Symmetric forms with zero radical. -/
def isRadicalFreeSymBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun L ↦ L.IsSymmetric ∧ L.IsNondegenerate

/-- Fixed-value radical-free symmetric bilinear modules. -/
abbrev RadicalFreeSymBilinModuleCat :=
  (isRadicalFreeSymBilinModule R W).FullSubcategory

/-- Symmetric forms whose adjoint map is bijective. -/
def isPerfectSymBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun L ↦ L.IsSymmetric ∧ L.IsPerfect

/-- Fixed-value perfect symmetric bilinear modules. -/
abbrev PerfectSymBilinModuleCat :=
  (isPerfectSymBilinModule R W).FullSubcategory

/-- The inclusion from alternating forms to skew-symmetric forms. -/
def alternatingToSkew : AltBilinModuleCat R W ⥤ SkewBilinModuleCat R W where
  obj L := ⟨L.obj, L.obj.isSkewSymmetric_of_isAlternating L.property⟩
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inclusion from radical-free symmetric forms to symmetric forms. -/
def radicalFreeToSymmetric :
    RadicalFreeSymBilinModuleCat R W ⥤ SymBilinModuleCat R W where
  obj L := ⟨L.obj, L.property.1⟩
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inclusion from perfect symmetric forms to radical-free symmetric forms. -/
def perfectToRadicalFree :
    PerfectSymBilinModuleCat R W ⥤ RadicalFreeSymBilinModuleCat R W where
  obj L := ⟨L.obj, ⟨L.property.1,
    L.obj.isNondegenerate_of_isPerfect L.property.2⟩⟩
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

end LeanCategories.Modules.Bilinear.Valued
