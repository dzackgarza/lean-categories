/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryTheory.OneCat.KernelFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Images

@[expose] public section

/-!
# The image as a functor from arrows to subobjects

In a category with images and functorial image maps, `f ↦ (image f ↪ codomain f)` is a functor
`Arr(C) ⥤ Subobjects(C)` (Mathlib's `Limits.im`, with its inclusion retained): the image of an
arrow is the subobject of its codomain, not only the object `image f`.
-/

open CategoryTheory CategoryTheory.Limits

namespace LeanCategories

universe v u

variable (C : Type u) [Category.{v} C] [HasImages C] [HasImageMaps C]

/-- The image of an arrow, with its inclusion into the codomain, as a monomorphism. -/
@[simps]
noncomputable def imageFunctor : Arrow C ⥤ (isMonoArrow C).FullSubcategory where
  obj f := ⟨Arrow.mk (image.ι f.hom), inferInstanceAs (Mono (image.ι f.hom))⟩
  map {f g} sq := ObjectProperty.homMk (Arrow.homMk (image.map sq) sq.right (by simp))
  map_id f := by
    ext
    · exact (cancel_mono (image.ι f.hom)).1 (by simp)
    · simp
  map_comp _ _ := by
    ext
    · exact (cancel_mono (image.ι _)).1 (by simp)
    · simp

end LeanCategories
