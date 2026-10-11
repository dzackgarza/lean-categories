/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

/-!
# The kernel as a functor from arrows to subobjects

In a category with kernels, `f ↦ (ker f, ker.ι f)` is a functor from the arrow category to the
full subcategory of arrows on monomorphisms: a commutative square `f → f'` induces
`kernel.map` between the kernels, and the kernel inclusion is always a monomorphism. The kernel is
returned with its inclusion — complete universal data (CC-UNIV), not an apex.
-/

open CategoryTheory CategoryTheory.Limits

namespace LeanCategories

universe v u

variable (C : Type u) [Category.{v} C]

/-- Monomorphisms, as a property of arrows: the subobjects of `C` are its full subcategory. -/
def isMonoArrow : ObjectProperty (Arrow C) := fun f ↦ Mono f.hom

variable [HasZeroMorphisms C] [HasKernels C]

/-- The kernel of an arrow, with its inclusion, as a monomorphism. -/
@[simps]
noncomputable def kernelFunctor : Arrow C ⥤ (isMonoArrow C).FullSubcategory where
  obj f := ⟨Arrow.mk (kernel.ι f.hom), inferInstanceAs (Mono (kernel.ι f.hom))⟩
  map {f g} sq := ObjectProperty.homMk
    (Arrow.homMk (kernel.map f.hom g.hom sq.left sq.right sq.w.symm) sq.left (by simp))
  map_id f := by
    ext
    · exact equalizer.hom_ext (by simp)
    · simp
  map_comp _ _ := by
    ext
    · exact equalizer.hom_ext (by simp)
    · simp

end LeanCategories

namespace LeanCategories

universe v u

variable (C : Type u) [Category.{v} C]

/-- Epimorphisms as chosen quotient arrows, retaining their projections. -/
def isEpiArrow : ObjectProperty (Arrow C) := fun f ↦ Epi f.hom

variable [HasZeroMorphisms C] [HasCokernels C]

/-- A cokernel together with its actual projection. Commutative squares act by
`cokernel.map`; the universal laws remain formal specifications of this construction. -/
@[simps]
noncomputable def cokernelFunctor : Arrow C ⥤ (isEpiArrow C).FullSubcategory where
  obj f := ⟨Arrow.mk (cokernel.π f.hom), inferInstanceAs (Epi (cokernel.π f.hom))⟩
  map {f g} sq := ObjectProperty.homMk
    (Arrow.homMk sq.right (cokernel.map f.hom g.hom sq.left sq.right sq.w.symm) (by simp))
  map_id f := by
    ext
    · simp
    · exact coequalizer.hom_ext (by simp)
  map_comp _ _ := by
    ext
    · simp
    · exact coequalizer.hom_ext (by simp)

end LeanCategories
