/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Standard free algebras on modules

This file defines the symmetric and exterior algebra functors from Mathlib's
canonical universal constructions.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace LeanCategories.Algebra.AlgCat

variable (R : Type u) [CommRing R]

/-- The symmetric algebra functor on `R`-modules. -/
@[simps]
noncomputable def symmetricAlgebra : ModuleCat.{v} R ⥤ AlgCat.{max u v} R where
  obj M := AlgCat.of R (SymmetricAlgebra R M)
  map f := AlgCat.ofHom <| SymmetricAlgebra.lift
    (SymmetricAlgebra.ι R _ ∘ₗ f.hom)
  map_id M := by
    apply AlgCat.hom_ext
    ext x
    simp
  map_comp f g := by
    apply AlgCat.hom_ext
    ext x
    simp

/-- The exterior algebra functor on `R`-modules. -/
@[simps]
noncomputable def exteriorAlgebra : ModuleCat.{v} R ⥤ AlgCat.{max u v} R where
  obj M := AlgCat.of R (ExteriorAlgebra R M)
  map f := AlgCat.ofHom (ExteriorAlgebra.map f.hom)
  map_id M := by
    apply AlgCat.hom_ext
    exact ExteriorAlgebra.map_id
  map_comp f g := by
    apply AlgCat.hom_ext
    exact (ExteriorAlgebra.map_comp_map f.hom g.hom).symm

end LeanCategories.Algebra.AlgCat
