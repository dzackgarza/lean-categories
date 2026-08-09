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

/-- Symmetry of the form. -/
def IsSymmetric (L : BilinModuleCat R W) : Prop :=
  ∀ x y, L.pairing x y = L.pairing y x

/-- The module adjoint `L → Hom_R(L,W)`. No formed structure on the codomain is implied. -/
def adjoint (L : BilinModuleCat R W) :
    L.carrier →ₗ[R] (L.carrier →ₗ[R] W) :=
  (TensorProduct.lift.equiv (.id R) L.carrier L.carrier W).symm L.form

abbrev bilinMap (L : BilinModuleCat R W) := L.adjoint

@[simp]
theorem bilinMap_apply (L : BilinModuleCat R W) (x y : L.carrier) :
    L.bilinMap x y = L.pairing x y :=
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

end BilinModuleCat

/-- The forgetful functor to `R`-modules. -/
def forget : BilinModuleCat R W ⥤ ModuleCat R where
  obj := BilinModuleCat.carrierObj
  map := fun f ↦ ModuleCat.ofHom (BilinModuleCat.underlyingMap f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Postcomposition by `f : W → W'` as a natural transformation of form functors. -/
def changeValueNatTrans {W' : Type u} [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') : bilinearForms R W ⟶ bilinearForms R W' where
  app M := ↾fun b ↦ f.comp b
  naturality M N g := by
    ext b
    rfl

/-- Change the value module of a bilinear form by postcomposition. -/
def changeValue {W' : Type u} [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') : BilinModuleCat R W ⥤ BilinModuleCat R W' :=
  (NatTrans.mapElements (changeValueNatTrans R W f)).op

/-- The functor of formed-module categories indexed by their value modules. -/
def valueFibers : ModuleCat.{u} R ⥤ Cat.{u, u + 1} where
  obj W := Cat.of (BilinModuleCat R W)
  map {W _} α := (changeValue R W α.hom).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The category of formed `R`-modules with a variable module of values. -/
abbrev BilWFormCat := Grothendieck (valueFibers R)

namespace BilWFormCat

variable {R}

/-- The value module of a formed module in the total category. -/
abbrev value (X : BilWFormCat R) : ModuleCat R := X.base

/-- The fixed-value formed module underlying an object of the total category. -/
abbrev formed (X : BilWFormCat R) : BilinModuleCat R X.value := X.fiber

/-- The carrier module of a formed module in the total category. -/
abbrev carrier (X : BilWFormCat R) : ModuleCat R := X.formed.carrierObj

/-- The bilinear form of an object in the total category. -/
abbrev form (X : BilWFormCat R) :
    TensorProduct R (X.carrier : Type u) (X.carrier : Type u) →ₗ[R] X.value :=
  X.formed.form

/-- The value of the form on two carrier elements. -/
abbrev pairing (X : BilWFormCat R) (x y : X.carrier) : X.value :=
  X.formed.pairing x y

/-- Symmetry of a formed module in the total category. -/
def IsSymmetric (X : BilWFormCat R) : Prop :=
  X.formed.IsSymmetric

/-- The map between value modules underlying a morphism in the total category. -/
abbrev valueMap {X Y : BilWFormCat R} (f : X ⟶ Y) : X.value ⟶ Y.value :=
  f.base

/-- The map between carrier modules underlying a morphism in the total category. -/
abbrev carrierMap {X Y : BilWFormCat R} (f : X ⟶ Y) : X.carrier ⟶ Y.carrier :=
  ModuleCat.ofHom (BilinModuleCat.underlyingMap f.fiber)

/-- Build an object of the total category from its carrier, value module, and form. -/
def of (M W : ModuleCat.{u} R)
    (b : TensorProduct R (M : Type u) (M : Type u) →ₗ[R] W) : BilWFormCat R where
  base := W
  fiber := op ⟨op M, b⟩

/-- Build a morphism in the total category from compatible carrier and value maps. -/
def homMk {X Y : BilWFormCat R}
    (f : X.carrier →ₗ[R] Y.carrier) (α : X.value →ₗ[R] Y.value)
    (h : ∀ x y, α (X.pairing x y) = Y.pairing (f x) (f y)) : X ⟶ Y where
  base := ModuleCat.ofHom α
  fiber := by
    refine Quiver.Hom.op (CategoryOfElements.homMk _ _
      (op (ModuleCat.ofHom f)) ?_)
    dsimp [bilinearForms]
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => exact (h x y).symm
    | add x y hx hy => simp [hx, hy]

@[ext]
theorem hom_ext {X Y : BilWFormCat R} (f g : X ⟶ Y)
    (hValue : valueMap f = valueMap g)
    (hCarrier : carrierMap f = carrierMap g) : f = g := by
  cases f with
  | mk fBase fFiber =>
    cases g with
    | mk gBase gFiber =>
      dsimp [valueMap] at hValue
      subst gBase
      congr
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      exact congrArg ModuleCat.Hom.hom hCarrier

/-- The zero morphism in the total formed-module category. -/
def zeroHom (X Y : BilWFormCat R) : X ⟶ Y :=
  homMk 0 0 (by
    intro x y
    change 0 = Y.formed.bilinMap 0 0
    rw [map_zero])

instance (X Y : BilWFormCat R) : Zero (X ⟶ Y) :=
  ⟨zeroHom X Y⟩

@[simp]
theorem valueMap_zero (X Y : BilWFormCat R) : valueMap (0 : X ⟶ Y) = 0 :=
  rfl

@[simp]
theorem carrierMap_zero (X Y : BilWFormCat R) : carrierMap (0 : X ⟶ Y) = 0 :=
  rfl

@[simp]
theorem valueMap_comp {X Y Z : BilWFormCat R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    valueMap (f ≫ g) = valueMap f ≫ valueMap g :=
  rfl

@[simp]
theorem carrierMap_comp {X Y Z : BilWFormCat R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    carrierMap (f ≫ g) = carrierMap f ≫ carrierMap g :=
  rfl

instance : HasZeroMorphisms (BilWFormCat R) where
  comp_zero := by
    intro X Y f Z
    apply hom_ext
    · rw [valueMap_comp, valueMap_zero]
      simp
    · rw [carrierMap_comp, carrierMap_zero]
      simp
  zero_comp := by
    intro X Y Z f
    apply hom_ext
    · rw [valueMap_comp, valueMap_zero]
      simp
    · rw [carrierMap_comp, carrierMap_zero]
      simp

/-- Morphisms in the total category preserve forms through their value maps. -/
theorem map_pairing {X Y : BilWFormCat R} (f : X ⟶ Y)
    (x y : X.carrier) :
    (valueMap f).hom (X.pairing x y) =
      Y.pairing ((carrierMap f).hom x) ((carrierMap f).hom y) :=
  (BilinModuleCat.map_pairing f.fiber x y).symm

section Cokernel

variable {X Y : BilWFormCat R} (f : X ⟶ Y)

/-- Pairings between the image of the carrier map and the target carrier. -/
def leftMixedRelations : Submodule R Y.value :=
  Submodule.span R (Set.range fun p : X.carrier × Y.carrier ↦
    Y.pairing ((carrierMap f).hom p.1) p.2)

/-- Pairings between the target carrier and the image of the carrier map. -/
def rightMixedRelations : Submodule R Y.value :=
  Submodule.span R (Set.range fun p : Y.carrier × X.carrier ↦
    Y.pairing p.1 ((carrierMap f).hom p.2))

/-- Relations killed in the value module of the categorical cokernel. -/
def cokernelValueRelations : Submodule R Y.value :=
  (LinearMap.range (valueMap f).hom ⊔ leftMixedRelations f) ⊔ rightMixedRelations f

/-- Relations killed in the carrier module of the categorical cokernel. -/
def cokernelCarrierRelations : Submodule R Y.carrier :=
  LinearMap.range (carrierMap f).hom

abbrev CokernelCarrier := Y.carrier ⧸ cokernelCarrierRelations f

abbrev CokernelValue := Y.value ⧸ cokernelValueRelations f

def cokernelCarrierProjection : Y.carrier →ₗ[R] CokernelCarrier f :=
  Submodule.mkQ (cokernelCarrierRelations f)

def cokernelValueProjection : Y.value →ₗ[R] CokernelValue f :=
  Submodule.mkQ (cokernelValueRelations f)

def projectedCokernelBilinMap :
    LinearMap.BilinMap R Y.carrier (CokernelValue f) :=
  Y.formed.bilinMap.compr₂ (cokernelValueProjection f)

theorem carrierRelations_le_ker_projectedCokernelBilinMap :
    cokernelCarrierRelations f ≤ LinearMap.ker (projectedCokernelBilinMap f) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  change cokernelValueProjection f
    (Y.pairing ((carrierMap f).hom x) y) = 0
  rw [cokernelValueProjection, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_right
  exact Submodule.subset_span (Set.mem_range_self (x, y))

theorem carrierRelations_le_flipKer_projectedCokernelBilinMap :
    cokernelCarrierRelations f ≤
      LinearMap.ker (projectedCokernelBilinMap f).flip := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  change cokernelValueProjection f
    (Y.pairing y ((carrierMap f).hom x)) = 0
  rw [cokernelValueProjection, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  apply Submodule.mem_sup_right
  exact Submodule.subset_span (Set.mem_range_self (y, x))

/-- The bilinear form on the carrier quotient of the categorical cokernel. -/
def cokernelBilinMap :
    LinearMap.BilinMap R (CokernelCarrier f) (CokernelValue f) :=
  (projectedCokernelBilinMap f).liftQ₂
    (cokernelCarrierRelations f) (cokernelCarrierRelations f)
    (carrierRelations_le_ker_projectedCokernelBilinMap f)
    (carrierRelations_le_flipKer_projectedCokernelBilinMap f)

def cokernelForm :
    TensorProduct R (CokernelCarrier f) (CokernelCarrier f) →ₗ[R]
      CokernelValue f :=
  (TensorProduct.lift.equiv (.id R) (CokernelCarrier f) (CokernelCarrier f)
    (CokernelValue f)) (cokernelBilinMap f)

theorem cokernelBilinMap_isSymmetric (hY : Y.IsSymmetric) :
    ∀ x y, cokernelBilinMap f x y = cokernelBilinMap f y x := by
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      change cokernelValueProjection f (Y.pairing x y) =
        cokernelValueProjection f (Y.pairing y x)
      exact congrArg (cokernelValueProjection f) (hY x y)

/-- The categorical cokernel candidate with both carrier and value relations removed. -/
def cokernelObject : BilWFormCat R :=
  of (ModuleCat.of R (CokernelCarrier f))
    (ModuleCat.of R (CokernelValue f)) (cokernelForm f)

/-- The quotient morphism into the categorical cokernel candidate. -/
def cokernelProjection : Y ⟶ cokernelObject f :=
  homMk (cokernelCarrierProjection f) (cokernelValueProjection f) (by
    intro x y
    rfl)

theorem comp_cokernelProjection : f ≫ cokernelProjection f = 0 := by
  apply hom_ext
  · rw [valueMap_comp, valueMap_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    change cokernelValueProjection f ((valueMap f).hom w) = 0
    rw [cokernelValueProjection, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    apply Submodule.mem_sup_left
    apply Submodule.mem_sup_left
    exact ⟨w, rfl⟩
  · rw [carrierMap_comp, carrierMap_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change cokernelCarrierProjection f ((carrierMap f).hom x) = 0
    rw [cokernelCarrierProjection, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩

theorem cokernelCarrierRelations_le_ker {Z : BilWFormCat R} (g : Y ⟶ Z)
    (h : (carrierMap g).hom ∘ₗ (carrierMap f).hom = 0) :
    cokernelCarrierRelations f ≤ LinearMap.ker (carrierMap g).hom := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  exact LinearMap.congr_fun h x

theorem cokernelValueRelations_le_ker {Z : BilWFormCat R} (g : Y ⟶ Z)
    (hCarrier : (carrierMap g).hom ∘ₗ (carrierMap f).hom = 0)
    (hValue : (valueMap g).hom ∘ₗ (valueMap f).hom = 0) :
    cokernelValueRelations f ≤ LinearMap.ker (valueMap g).hom := by
  rw [cokernelValueRelations, sup_le_iff, sup_le_iff]
  constructor
  · constructor
    · rintro _ ⟨w, rfl⟩
      rw [LinearMap.mem_ker]
      exact LinearMap.congr_fun hValue w
    · rw [leftMixedRelations, Submodule.span_le]
      rintro _ ⟨⟨x, y⟩, rfl⟩
      change (valueMap g).hom
        (Y.pairing ((carrierMap f).hom x) y) = 0
      rw [map_pairing]
      have hx : (carrierMap g).hom ((carrierMap f).hom x) = 0 := by
        exact LinearMap.congr_fun hCarrier x
      rw [hx]
      change Z.formed.bilinMap 0 ((carrierMap g).hom y) = 0
      rw [map_zero]
      rfl
  · rw [rightMixedRelations, Submodule.span_le]
    rintro _ ⟨⟨y, x⟩, rfl⟩
    change (valueMap g).hom
      (Y.pairing y ((carrierMap f).hom x)) = 0
    rw [map_pairing]
    have hx : (carrierMap g).hom ((carrierMap f).hom x) = 0 := by
      exact LinearMap.congr_fun hCarrier x
    rw [hx]
    change Z.formed.bilinMap ((carrierMap g).hom y) 0 = 0
    rw [map_zero]

def cokernelCarrierDesc {Z : BilWFormCat R} (g : Y ⟶ Z)
    (hCarrier : (carrierMap g).hom ∘ₗ (carrierMap f).hom = 0) :
    CokernelCarrier f →ₗ[R] Z.carrier :=
  Submodule.liftQ (cokernelCarrierRelations f) (carrierMap g).hom
    (cokernelCarrierRelations_le_ker f g hCarrier)

def cokernelValueDesc {Z : BilWFormCat R} (g : Y ⟶ Z)
    (hCarrier : (carrierMap g).hom ∘ₗ (carrierMap f).hom = 0)
    (hValue : (valueMap g).hom ∘ₗ (valueMap f).hom = 0) :
    CokernelValue f →ₗ[R] Z.value :=
  Submodule.liftQ (cokernelValueRelations f) (valueMap g).hom
    (cokernelValueRelations_le_ker f g hCarrier hValue)

/-- The unique candidate induced from a morphism that kills both components of `f`. -/
def cokernelDesc {Z : BilWFormCat R} (g : Y ⟶ Z)
    (hCarrier : (carrierMap g).hom ∘ₗ (carrierMap f).hom = 0)
    (hValue : (valueMap g).hom ∘ₗ (valueMap f).hom = 0) :
    cokernelObject f ⟶ Z :=
  homMk (cokernelCarrierDesc f g hCarrier)
    (cokernelValueDesc f g hCarrier hValue) (by
      intro x y
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        induction y using Submodule.Quotient.induction_on with
        | _ y =>
          change (valueMap g).hom (Y.pairing x y) =
            Z.pairing ((carrierMap g).hom x) ((carrierMap g).hom y)
          exact map_pairing g x y)

theorem cokernelProjection_desc {Z : BilWFormCat R} (g : Y ⟶ Z)
    (hCarrier : (carrierMap g).hom ∘ₗ (carrierMap f).hom = 0)
    (hValue : (valueMap g).hom ∘ₗ (valueMap f).hom = 0) :
    cokernelProjection f ≫ cokernelDesc f g hCarrier hValue = g := by
  apply hom_ext
  · rw [valueMap_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    rfl
  · rw [carrierMap_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

theorem carrier_comp_eq_zero_of_comp_eq_zero {Z : BilWFormCat R} (g : Y ⟶ Z)
    (h : f ≫ g = 0) :
    (carrierMap g).hom ∘ₗ (carrierMap f).hom = 0 := by
  have h' := congrArg (fun k ↦ (carrierMap k).hom) h
  exact h'

theorem value_comp_eq_zero_of_comp_eq_zero {Z : BilWFormCat R} (g : Y ⟶ Z)
    (h : f ≫ g = 0) :
    (valueMap g).hom ∘ₗ (valueMap f).hom = 0 := by
  have h' := congrArg (fun k ↦ (valueMap k).hom) h
  exact h'

/-- The cokernel cofork carried by the quotient in the total category. -/
def cokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ (cokernelProjection f) (comp_cokernelProjection f)

/-- The quotient construction is the categorical cokernel in `BilWFormCat R`. -/
def cokernelIsColimit : IsColimit (cokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ (cokernelProjection f)
    (comp_cokernelProjection f)
    (fun g h ↦
      cokernelDesc f g
        (carrier_comp_eq_zero_of_comp_eq_zero f g h)
        (value_comp_eq_zero_of_comp_eq_zero f g h))
    (fun g h ↦
      cokernelProjection_desc f g
        (carrier_comp_eq_zero_of_comp_eq_zero f g h)
        (value_comp_eq_zero_of_comp_eq_zero f g h))
    (fun g h m hm ↦ by
      let hCarrier := carrier_comp_eq_zero_of_comp_eq_zero f g h
      let hValue := value_comp_eq_zero_of_comp_eq_zero f g h
      have hDesc := cokernelProjection_desc f g hCarrier hValue
      apply hom_ext
      · apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
          (cokernelValueRelations f) z
        have hm' := congrArg (fun k ↦ (valueMap k).hom) hm
        have hDesc' := congrArg (fun k ↦ (valueMap k).hom) hDesc
        exact (LinearMap.congr_fun hm' y).trans
          (LinearMap.congr_fun hDesc' y).symm
      · apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
          (cokernelCarrierRelations f) z
        have hm' := congrArg (fun k ↦ (carrierMap k).hom) hm
        have hDesc' := congrArg (fun k ↦ (carrierMap k).hom) hDesc
        exact (LinearMap.congr_fun hm' x).trans
          (LinearMap.congr_fun hDesc' x).symm)

end Cokernel

end BilWFormCat

/-- Symmetric objects in the total category of variable-valued forms. -/
def isSymmetricBilWForm : ObjectProperty (BilWFormCat R) :=
  fun X ↦ X.IsSymmetric

/-- The total category of symmetric forms with variable value modules. -/
abbrev SymBilWFormCat := (isSymmetricBilWForm R).FullSubcategory

namespace SymBilWFormCat

variable {R}
variable {X Y : SymBilWFormCat R} (f : X ⟶ Y)

/-- The symmetric categorical cokernel object. -/
def cokernelObject : SymBilWFormCat R :=
  ⟨BilWFormCat.cokernelObject f.hom,
    BilWFormCat.cokernelBilinMap_isSymmetric f.hom Y.property⟩

/-- The quotient morphism into the symmetric categorical cokernel. -/
def cokernelProjection : Y ⟶ cokernelObject f :=
  ObjectProperty.homMk (BilWFormCat.cokernelProjection f.hom)

theorem comp_cokernelProjection : f ≫ cokernelProjection f = 0 := by
  apply ObjectProperty.hom_ext
  exact BilWFormCat.comp_cokernelProjection f.hom

/-- The cokernel cofork in the total category of symmetric forms. -/
def cokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ (cokernelProjection f) (comp_cokernelProjection f)

/-- The morphism induced from a symmetric formed morphism that kills `f`. -/
def cokernelDesc {Z : SymBilWFormCat R} (g : Y ⟶ Z) (h : f ≫ g = 0) :
    cokernelObject f ⟶ Z :=
  ObjectProperty.homMk
    (BilWFormCat.cokernelDesc f.hom g.hom
      (BilWFormCat.carrier_comp_eq_zero_of_comp_eq_zero f.hom g.hom
        (congrArg (fun k ↦ k.hom) h))
      (BilWFormCat.value_comp_eq_zero_of_comp_eq_zero f.hom g.hom
        (congrArg (fun k ↦ k.hom) h)))

theorem cokernelProjection_desc {Z : SymBilWFormCat R} (g : Y ⟶ Z)
    (h : f ≫ g = 0) :
    cokernelProjection f ≫ cokernelDesc f g h = g := by
  apply ObjectProperty.hom_ext
  exact BilWFormCat.cokernelProjection_desc f.hom g.hom
    (BilWFormCat.carrier_comp_eq_zero_of_comp_eq_zero f.hom g.hom
      (congrArg (fun k ↦ k.hom) h))
    (BilWFormCat.value_comp_eq_zero_of_comp_eq_zero f.hom g.hom
      (congrArg (fun k ↦ k.hom) h))

/-- The quotient is the categorical cokernel among symmetric formed modules. -/
def cokernelIsColimit : IsColimit (cokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ (cokernelProjection f)
    (comp_cokernelProjection f)
    (cokernelDesc f)
    (cokernelProjection_desc f)
    (fun g h m hm ↦ by
      apply ObjectProperty.hom_ext
      apply Cofork.IsColimit.hom_ext (BilWFormCat.cokernelIsColimit f.hom)
      calc
        BilWFormCat.cokernelProjection f.hom ≫ m.hom = g.hom :=
          congrArg (fun k ↦ k.hom) hm
        _ = BilWFormCat.cokernelProjection f.hom ≫ (cokernelDesc f g h).hom :=
          (congrArg (fun k ↦ k.hom) (cokernelProjection_desc f g h)).symm)

end SymBilWFormCat

end LeanCategories.Modules.Bilinear.Valued
