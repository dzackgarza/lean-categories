/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Symmetric
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.LinearAlgebra.Quotient.Bilinear

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable (R : Type u) [CommRing R]

namespace BilWFormCat

variable {R}

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

