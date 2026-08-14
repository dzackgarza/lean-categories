/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Standard free algebras on modules

This file exposes Mathlib's tensor, symmetric, and exterior algebras as
functors from modules to algebras.  The tensor algebra functor is imported
from Mathlib; the other two use their canonical universal constructions.
-/

public import Mathlib.Algebra.Category.AlgCat.TensorAlgebra
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

@[expose] public section

open CategoryTheory

universe u v

namespace LeanCategories.Algebra.AlgebraCat

variable (R : Type u) [CommRing R]

/-- The tensor algebra functor over `R`, from Mathlib's canonical construction. -/
abbrev tensorAlgebra : ModuleCat.{v} R ⥤ AlgCat.{max u v} R :=
  AlgCat.tensorAlgebra R

/-- The symmetric algebra functor on `R`-modules. -/
@[simps]
noncomputable def symmetricAlgebra : ModuleCat.{v} R ⥤ AlgCat.{max u v} R where
  obj M := AlgCat.of R (SymmetricAlgebra R M)
  map f := AlgCat.ofHom <| SymmetricAlgebra.lift R
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
    exact ExteriorAlgebra.map_comp_map f.hom g.hom

end LeanCategories.Algebra.AlgebraCat
