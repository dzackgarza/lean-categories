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

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism from an element to its image under `F.map f` is strongly co-Cartesian
over `f` for the category-of-elements projection.

This extends Mathlib's `CategoryOfElements.homMk` and `CategoryOfElements.π` with the
`Functor.IsStronglyCocartesian` structure from
`Mathlib.CategoryTheory.FiberedCategory.Cocartesian`. -/
instance homMk_map_isStronglyCocartesian (F : C ⥤ Type w) {R S : C}
    (x : F.obj R) (f : R ⟶ S) :
    Functor.IsStronglyCocartesian (π F) f
      (homMk f rfl : Functor.Elements.mk x ⟶ Functor.Elements.mk (F.map f x)) := by
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · exact IsHomLift.of_fac' (π F) f (homMk f rfl :
      Functor.Elements.mk x ⟶ Functor.Elements.mk (F.map f x)) rfl rfl (by simp [π])
  · intro b' g φ hφ
    letI : (π F).IsHomLift (f ≫ g) φ := hφ
    have hφfac := IsHomLift.fac' (π F) (f ≫ g) φ
    have hφval : φ.hom = f ≫ g := by
      simpa [π] using hφfac
    change S ⟶ b'.obj at g
    have hφval' : φ.hom = f ≫ g := hφval
    refine ⟨homMk g ?_, ?_, ?_⟩
    · rw [← F.map_comp_apply, ← hφval']
      exact φ.map_val
    · constructor
      · refine IsHomLift.of_fac' (π F) g _ ?_ ?_ ?_
        · rfl
        · rfl
        · simp [π]
      · apply ext
        change f ≫ g = φ.hom
        exact hφval'.symm
    · intro χ hχ
      apply ext
      letI : (π F).IsHomLift g χ := hχ.1
      have hχfac := IsHomLift.fac' (π F) g χ
      simpa [π] using hχfac

end CategoryTheory.CategoryOfElements
