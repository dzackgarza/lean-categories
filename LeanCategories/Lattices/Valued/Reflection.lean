/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.OrthogonalGroup

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

/-- A root reflection has square one. -/
theorem reflectionMap_involutive (L : IntegralLatticeCat ℤ)
    (r : L.obj.carrier) (hr : L.obj.pairing r r = -2 ∨
      L.obj.pairing r r = 2) (x : L.obj.carrier) :
    reflectionMap L r hr (reflectionMap L r hr x) = x := by
  rcases hr with h | h
  · have hpair : L.obj.pairing (reflectionMap L r (Or.inl h) x) r =
        -L.obj.pairing x r := by
      change L.obj.bilinMap (reflectionMap L r (Or.inl h) x) r =
        -L.obj.bilinMap x r
      rw [reflectionMap_apply_of_neg L r (Or.inl h) h]
      simp only [map_add, LinearMap.add_apply, map_zsmul,
        LinearMap.smul_apply, smul_eq_mul, BilinModuleCat.bilinMap_apply, h]
      ring
    rw [reflectionMap_apply_of_neg L r (Or.inl h) h,
      hpair, reflectionMap_apply_of_neg L r (Or.inl h) h]
    simp
  · have hpair : L.obj.pairing (reflectionMap L r (Or.inr h) x) r =
        -L.obj.pairing x r := by
      change L.obj.bilinMap (reflectionMap L r (Or.inr h) x) r =
        -L.obj.bilinMap x r
      rw [reflectionMap_apply_of_pos L r (Or.inr h) h]
      simp only [map_sub, LinearMap.sub_apply, map_zsmul,
        LinearMap.smul_apply, smul_eq_mul, BilinModuleCat.bilinMap_apply, h]
      ring
    rw [reflectionMap_apply_of_pos L r (Or.inr h) h,
      hpair, reflectionMap_apply_of_pos L r (Or.inr h) h]
    simp

/-- A root reflection as a linear automorphism. -/
def reflectionEquiv (L : IntegralLatticeCat ℤ) (r : L.obj.carrier)
    (hr : L.obj.pairing r r = -2 ∨ L.obj.pairing r r = 2) :
    L.obj.carrier ≃ₗ[ℤ] L.obj.carrier where
  toLinearMap := reflectionMap L r hr
  invFun := reflectionMap L r hr
  left_inv := reflectionMap_involutive L r hr
  right_inv := reflectionMap_involutive L r hr

/-- A root reflection as an element of the orthogonal group. -/
def reflectionOrthogonalElement (L : IntegralLatticeCat ℤ)
    (r : L.obj.carrier)
    (hr : L.obj.pairing r r = -2 ∨ L.obj.pairing r r = 2) :
    OrthogonalGroup L :=
  ⟨reflectionEquiv L r hr, reflectionMap_isometry L r hr⟩

/-- An element of `O(L)` with square one. -/
structure Involution (L : IntegralLatticeCat ℤ) where
  element : OrthogonalGroup L
  involutive : element * element = 1

/-- A root reflection as an involution. -/
def reflectionInvolution (L : IntegralLatticeCat ℤ)
    (r : L.obj.carrier)
    (hr : L.obj.pairing r r = -2 ∨ L.obj.pairing r r = 2) :
    Involution L where
  element := reflectionOrthogonalElement L r hr
  involutive := by
    apply Subtype.ext
    ext x
    exact reflectionMap_involutive L r hr x

/-- The fixed submodule of an involution. -/
def fixedSubmodule (L : IntegralLatticeCat ℤ) (J : Involution L) :
    Submodule ℤ L.obj.carrier :=
  LinearMap.ker (J.element.1.toLinearMap - LinearMap.id)

/-- The anti-fixed submodule of an involution. -/
def antiFixedSubmodule (L : IntegralLatticeCat ℤ) (J : Involution L) :
    Submodule ℤ L.obj.carrier :=
  LinearMap.ker (J.element.1.toLinearMap + LinearMap.id)

end LeanCategories.Lattices.Valued
