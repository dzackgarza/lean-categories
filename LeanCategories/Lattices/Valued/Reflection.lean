/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Constructions

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The integral reflection in a vector of square `2` or `-2`. -/
def reflectionMap (L : IntegralLatticeCat ℤ) (r : L.obj.carrier)
    (_hr : L.obj.pairing r r = -2 ∨ L.obj.pairing r r = 2) :
    L.obj.carrier →ₗ[ℤ] L.obj.carrier :=
  let f : L.obj.carrier →+ L.obj.carrier :=
    { toFun x := if L.obj.pairing r r = -2 then
          x + (L.obj.pairing x r) • r
        else x - (L.obj.pairing x r) • r
      map_zero' := by simp
      map_add' := by
        intro x y
        by_cases h : L.obj.pairing r r = -2
        · rw [if_pos h, if_pos h, if_pos h, BilinModuleCat.pairing_add_left,
            add_zsmul]
          abel
        · rw [if_neg h, if_neg h, if_neg h, BilinModuleCat.pairing_add_left,
            add_zsmul]
          abel }
  { toFun := f
    map_add' := f.map_add
    map_smul' := by
      intro c x
      exact map_intCast_smul f ℤ ℤ c x }

theorem reflectionMap_apply_of_neg (L : IntegralLatticeCat ℤ)
    (r : L.obj.carrier) (hr : L.obj.pairing r r = -2 ∨ L.obj.pairing r r = 2)
    (h : L.obj.pairing r r = -2) (x : L.obj.carrier) :
    reflectionMap L r hr x = x + (L.obj.pairing x r) • r := by
  simp [reflectionMap, h]

theorem reflectionMap_apply_of_pos (L : IntegralLatticeCat ℤ)
    (r : L.obj.carrier) (hr : L.obj.pairing r r = -2 ∨ L.obj.pairing r r = 2)
    (h : L.obj.pairing r r = 2) (x : L.obj.carrier) :
    reflectionMap L r hr x = x - (L.obj.pairing x r) • r := by
  have h' : L.obj.pairing r r ≠ -2 := by rw [h]; decide
  simp [reflectionMap, h']

/-- A root reflection preserves the lattice form. -/
theorem reflectionMap_isometry (L : IntegralLatticeCat ℤ)
    (r : L.obj.carrier) (hr : L.obj.pairing r r = -2 ∨ L.obj.pairing r r = 2)
    (x y : L.obj.carrier) :
    L.obj.pairing (reflectionMap L r hr x) (reflectionMap L r hr y) =
      L.obj.pairing x y := by
  change L.obj.bilinMap (reflectionMap L r hr x) (reflectionMap L r hr y) =
    L.obj.bilinMap x y
  have hsymm : ∀ a b, L.obj.pairing a b = L.obj.pairing b a := L.property.2
  rcases hr with h | h
  · rw [reflectionMap_apply_of_neg L r (Or.inl h) h x,
      reflectionMap_apply_of_neg L r (Or.inl h) h y]
    simp only [map_add, LinearMap.add_apply, map_zsmul, LinearMap.smul_apply,
      smul_eq_mul, BilinModuleCat.bilinMap_apply, h]
    rw [hsymm r y]
    ring
  · rw [reflectionMap_apply_of_pos L r (Or.inr h) h x,
      reflectionMap_apply_of_pos L r (Or.inr h) h y]
    simp only [map_sub, LinearMap.sub_apply, map_zsmul, LinearMap.smul_apply,
      smul_eq_mul, BilinModuleCat.bilinMap_apply, h]
    rw [hsymm r y]
    ring

/-- An involutive lattice isometry. -/
structure Involution (L : IntegralLatticeCat ℤ) where
  hom : L ⟶ L
  involutive : ∀ x, BilinModuleCat.underlyingMap hom.hom
    (BilinModuleCat.underlyingMap hom.hom x) = x

/-- The fixed submodule of an involution. -/
def fixedSubmodule (L : IntegralLatticeCat ℤ) (J : Involution L) :
    Submodule ℤ L.obj.carrier :=
  LinearMap.ker (BilinModuleCat.underlyingMap J.hom.hom - LinearMap.id)

/-- The anti-fixed submodule of an involution. -/
def antiFixedSubmodule (L : IntegralLatticeCat ℤ) (J : Involution L) :
    Submodule ℤ L.obj.carrier :=
  LinearMap.ker (BilinModuleCat.underlyingMap J.hom.hom + LinearMap.id)

end LeanCategories.Lattices.Valued
