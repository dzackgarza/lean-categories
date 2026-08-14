/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.DividedPowerAlgebra.Init

@[expose] public section

open CategoryTheory

namespace LeanCategories.Modules.DividedPowers

universe u v

variable (R : Type u) [CommRing R]

/-!
# The fixed-base divided-power algebra functor

`DividedPowerAlgebra R M` is Mathlib's quotient construction of the universal
divided-power algebra on an `R`-module `M`. This file only packages its existing
functoriality in the category of `R`-modules. Grading and the degree-two
quadratic comparison belong to separate files.
-/

/-- The universal divided-power algebra as a functor of its module. -/
noncomputable def dividedPowerAlgebraFunctor :
    ModuleCat.{v} R ⥤ CommAlgCat.{max u v} R where
  obj M := CommAlgCat.of R (DividedPowerAlgebra R (M : Type v))
  map f := CommAlgCat.ofHom (DividedPowerAlgebra.map R f.hom)
  map_id M := by
    apply CommAlgCat.hom_ext
    exact DividedPowerAlgebra.map_id
  map_comp f g := by
    apply CommAlgCat.hom_ext
    exact DividedPowerAlgebra.map_comp f.hom g.hom

@[simp]
theorem dividedPowerAlgebraFunctor_map_dp
    {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℕ) (m : M) :
    (dividedPowerAlgebraFunctor R).map f
        (DividedPowerAlgebra.dp R n m) =
      DividedPowerAlgebra.dp R n (f.hom m) := by
  change DividedPowerAlgebra.map R f.hom (DividedPowerAlgebra.dp R n m) = _
  simp

@[simp]
theorem dividedPowerAlgebraFunctor_map_embed
    {M N : ModuleCat.{v} R} (f : M ⟶ N) (m : M) :
    (dividedPowerAlgebraFunctor R).map f
        (DividedPowerAlgebra.embed R M m) =
      DividedPowerAlgebra.embed R N (f.hom m) := by
  change DividedPowerAlgebra.map R f.hom (DividedPowerAlgebra.embed R M m) = _
  simp

end LeanCategories.Modules.DividedPowers
