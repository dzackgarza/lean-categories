/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

@[expose] public section

open CategoryTheory

namespace CategoryTheory.CategoryOfElements

universe w v u

variable {C : Type u} [Category.{v} C]

/-- The morphism from an element to its image under `F.map f` is strongly co-Cartesian
over `f` for the category-of-elements projection.

This extends Mathlib's `CategoryOfElements.homMk` and `CategoryOfElements.π` with the
`Functor.IsStronglyCocartesian` structure from
`Mathlib.CategoryTheory.FiberedCategory.Cocartesian`. -/
instance homMk_map_isStronglyCocartesian (F : C ⥤ Type w) {R S : C}
    (x : F.obj R) (f : R ⟶ S) :
    Functor.IsStronglyCocartesian (π F) f
      (homMk ⟨R, x⟩ ⟨S, F.map f x⟩ f rfl) := by
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · apply IsHomLift.of_fac' (π F) f _ (by simp) (by simp)
    simp [π]
  · rintro ⟨T, z⟩ g φ hφ
    letI : (π F).IsHomLift (f ≫ g) φ := hφ
    have hφfac := IsHomLift.fac' (π F) (f ≫ g) φ
    have hφval : φ.val = f ≫ g := by
      simpa [π] using hφfac
    change S ⟶ T at g
    have hφval' : φ.val = f ≫ g := hφval
    refine ⟨homMk _ _ g ?_, ?_, ?_⟩
    · rw [← F.map_comp_apply, ← hφval']
      exact φ.property
    · constructor
      · apply IsHomLift.of_fac' (π F) g _ (by simp) (by simp)
        simp [π]
      · apply ext
        change f ≫ g = φ.val
        exact hφval'.symm
    · intro χ hχ
      apply ext
      letI : (π F).IsHomLift g χ := hχ.1
      have hχfac := IsHomLift.fac' (π F) g χ
      simpa [π] using hχfac

end CategoryTheory.CategoryOfElements
