/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Constructions

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The form of the integral hyperbolic plane. -/
def hyperbolicPlaneBilinMap : LinearMap.BilinMap ℤ (ℤ × ℤ) ℤ :=
  LinearMap.mk₂ ℤ
    (fun x y ↦ x.1 * y.2 + x.2 * y.1)
    (fun _ _ _ ↦ by simp; ring)
    (fun _ _ _ ↦ by simp; ring)
    (fun _ _ _ ↦ by simp; ring)
    (fun _ _ _ ↦ by simp; ring)

/-- The integral hyperbolic plane `U`. -/
def hyperbolicPlane : IntegralLatticeCat ℤ := by
  refine ⟨BilinModuleCat.ofBilinMap hyperbolicPlaneBilinMap, ?_, ?_⟩
  · change Module.Projective ℤ (ℤ × ℤ)
    infer_instance
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  change x₁ * y₂ + x₂ * y₁ = y₁ * x₂ + y₂ * x₁
  ring

@[simp]
theorem hyperbolicPlane_pairing (x y : hyperbolicPlane.obj.carrier) :
    hyperbolicPlane.obj.pairing x y = x.1 * y.2 + x.2 * y.1 :=
  rfl

end LeanCategories.Lattices.Valued
