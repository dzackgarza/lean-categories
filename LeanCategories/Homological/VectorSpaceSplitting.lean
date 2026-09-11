/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SplitComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic

import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection

/-!
# Splittings of complexes of vector spaces

Weibel, *An Introduction to Homological Algebra* (1994), §1.4,
FC05-C01-U030.

Over a field, choosing complements to the image of each differential produces
reverse-degree maps satisfying `d = d s d`.  The construction below works over
any division ring and for an arbitrary homological-complex shape.

The subsequent decomposition into homology and contractible summands is a
theorem about this splitting data and is intentionally left to Sweep IV.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory

universe v u

/-- Every linear map of vector spaces has an inner inverse `g` with `f = f g f`. -/
theorem existsInnerInverse
    {K : Type u} [DivisionRing K]
    {V W : Type v} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) : ∃ g : W →ₗ[K] V, f = f.comp (g.comp f) := by
  obtain ⟨q, hq⟩ := f.range.exists_isCompl
  obtain ⟨r, hr⟩ :=
    f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let g : W →ₗ[K] V := r.comp (f.range.projectionOnto q hq)
  refine ⟨g, LinearMap.ext fun x => ?_⟩
  change f x = f (r (f.range.projectionOnto q hq (f x)))
  rw [Submodule.projectionOnto_apply_of_mem_left hq (LinearMap.mem_range_self f x)]
  have hrx := LinearMap.congr_fun hr ⟨f x, LinearMap.mem_range_self f x⟩
  exact congrArg Subtype.val hrx |>.symm

variable {K : Type u} [DivisionRing K]
variable {ι : Type*} {c : ComplexShape ι}

/-- Every complex of vector spaces admits Weibel splitting maps `d = d s d`. -/
noncomputable def vectorSpaceSplitting
    (C : HomologicalComplex (ModuleCat.{v} K) c) : Splitting C where
  s i j _ := ModuleCat.ofHom <| Classical.choose (existsInnerInverse (C.d j i).hom)
  d_s_d i j _ := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    rw [LinearMap.comp_assoc]
    exact Classical.choose_spec (existsInnerInverse (C.d i j).hom)

/-- Every complex of vector spaces is split in Weibel's sense. -/
theorem isSplit_vectorSpace
    (C : HomologicalComplex (ModuleCat.{v} K) c) : IsSplit C :=
  ⟨vectorSpaceSplitting C⟩

end LeanCategories.Homological
