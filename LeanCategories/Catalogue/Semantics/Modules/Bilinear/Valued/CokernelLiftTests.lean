/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ConstructionTests
public import Mathlib.Data.ZMod.Basic
public import LeanCategories.Catalogue.Semantics.Limits.Registration

@[expose] public section

/-!
# Nonzero prescribed descent from a formed cokernel

Multiply the hyperbolic plane's carrier by two and values by four. Reduction
modulo two annihilates both components, so the existing universal property gives
a prescribed descent. Its carrier and value actions are nonzero. The quotient
pairing is checked through its defining map rather than replaced by an unrelated
pairing on the carrier quotient.
-/

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued
open CasCatalogue.Modules.Bilinear.Valued.Constructions
open CasCatalogue.Modules.Bilinear.Valued.ConstructionTests
namespace CasCatalogue.Modules.Bilinear.Valued.CokernelLiftTests

abbrev integralPlane := formed integers vectors ConstructionTests.values hyperbolic
def doublePlane : integralPlane ⟶ integralPlane :=
  morphism integers integralPlane integralPlane
    (ModuleCat.ofHom ((2 : ℤ) • LinearMap.id))
    (ModuleCat.ofHom ((4 : ℤ) • LinearMap.id)) (by
    intro x y
    change 4 * (x 0 * y 1 + x 1 * y 0) = (2 * x 0) * (2 * y 1) + (2 * x 1) * (2 * y 0)
    ring)
abbrev modVectors : ModuleCat integers := ModuleCat.of integers (Fin 2 → ZMod 2)
abbrev modValues : ModuleCat integers := ModuleCat.of integers (ZMod 2)
def modBilinear : bilinearMaps integers modVectors modVectors modValues :=
  admitBilinear integers modVectors modVectors modValues
    (fun xy => xy.1 0 * xy.2 1 + xy.1 1 * xy.2 0)
    (by constructor <;> intros <;> simp [zsmul_eq_mul] <;> ring) PUnit.unit
abbrev modPlane := formed integers modVectors modValues modBilinear
def reduceValues : ℤ →ₗ[ℤ] ZMod 2 := (Int.castAddHom (ZMod 2)).toIntLinearMap
def reduceCarrier : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ZMod 2) :=
  LinearMap.pi fun i => reduceValues.comp (LinearMap.proj i)
def reducePlane : integralPlane ⟶ modPlane :=
  morphism integers integralPlane modPlane
    (ModuleCat.ofHom reduceCarrier) (ModuleCat.ofHom reduceValues) (by
    intro x y
    change ((x 0 * y 1 + x 1 * y 0 : ℤ) : ZMod 2) =
      (x 0 : ZMod 2) * (y 1 : ZMod 2) + (x 1 : ZMod 2) * (y 0 : ZMod 2)
    simp)
theorem double_reduce_zero : doublePlane ≫ reducePlane = 0 := by
  apply BilWFormCat.hom_ext
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ℤ at x
    change ((4 * x : ℤ) : ZMod 2) = 0
    rw [Int.cast_mul, show ((4 : ℤ) : ZMod 2) = 0 by decide, zero_mul]
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change ((2 * x i : ℤ) : ZMod 2) = 0
    rw [Int.cast_mul, show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul]

/-- The universal property prescribes this descent of the supplied modulo-two map. -/
noncomputable def descended : cokernel integers doublePlane ⟶ modPlane :=
  (CasCatalogue.Limits.Registration.bilWFormCokernel doublePlane).isColimit.desc
    (CategoryTheory.Limits.CokernelCofork.ofπ reducePlane double_reduce_zero)

def projection : integralPlane ⟶ cokernel integers doublePlane :=
  cokernelProjection integers doublePlane

/-- The induced carrier map sends the projected first basis vector to the first basis vector. -/
theorem descended_carrier_basis :
    (BilWFormCat.carrierMap descended).hom
      ((BilWFormCat.carrierMap projection).hom ![1, 0]) =
        (![1, 0] : Fin 2 → ZMod 2) := by
  change (BilWFormCat.carrierMap
    (cokernelProjection integers doublePlane ≫
      cokernelDesc integers doublePlane reducePlane double_reduce_zero)).hom ![1, 0] = _
  rw [cokernelProjection_desc]
  funext i
  fin_cases i <;> rfl

/-- The prescribed value map likewise retains the class of one. -/
theorem descended_value_one :
    (BilWFormCat.valueMap descended).hom
      ((BilWFormCat.valueMap projection).hom (1 : ℤ)) = (1 : ZMod 2) := by
  change (BilWFormCat.valueMap
    (cokernelProjection integers doublePlane ≫
      cokernelDesc integers doublePlane reducePlane double_reduce_zero)).hom (1 : ℤ) = _
  rw [cokernelProjection_desc]
  rfl

/-- The quotient pairing is the induced pairing, with the actual value quotient retained. -/
example : (cokernel integers doublePlane).pairing
    ((BilWFormCat.carrierMap projection).hom ![1, 0])
    ((BilWFormCat.carrierMap projection).hom ![0, 1]) =
      (BilWFormCat.valueMap projection).hom (1 : ℤ) :=
  (BilWFormCat.map_pairing projection ![1, 0] ![0, 1]).symm

/-- This is a genuinely nonzero descent, not merely the zero lift. -/
example : descended ≠ 0 := by
  intro h
  have hx := congrArg (fun k => (BilWFormCat.valueMap k).hom
    ((BilWFormCat.valueMap projection).hom (1 : ℤ))) h
  rw [descended_value_one] at hx
  change (1 : ZMod 2) = 0 at hx
  exact one_ne_zero hx

end CasCatalogue.Modules.Bilinear.Valued.CokernelLiftTests
