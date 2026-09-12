/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CotripleResolution
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# The free-module cotriple resolution

Weibel, *An Introduction to Homological Algebra*, Construction 8.6.14,
pp. 278--285 (FC05-C08-U072).

The free-module functor `Type ⥤ ModuleCat R` is left adjoint to the forgetful
functor.  The induced comonad on `R`-modules is the free-module cotriple.  Its
canonical cotriple construction has degree `T^(n+1) M`, with the standard
counit faces, comultiplication degeneracies, and counit augmentation.

The claims that the resulting augmented simplicial module is aspherical and
that its alternating-face chain complex is a functorial free resolution are
result-level assertions and are not included here.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

universe u

variable {R : Type u} [Ring R]

/-- The comonad on `R`-modules induced by the free/forgetful adjunction.

Source: Weibel, Construction 8.6.14 (FC05-C08-U072). -/
noncomputable def freeModuleComonad : Comonad (ModuleCat.{u} R) :=
  (ModuleCat.adj R).toComonad

/-- Degree `n` of the canonical free-module cotriple construction on `M`. -/
abbrev freeModuleResolutionDegree (M : ModuleCat.{u} R) (n : ℕ) : ModuleCat.{u} R :=
  (freeModuleComonad (R := R)).simplicialDegree M n

/-- The `i`th face of the canonical free-module cotriple construction. -/
def freeModuleResolutionFace (M : ModuleCat.{u} R) (n : ℕ) (i : Fin (n + 1)) :
    freeModuleResolutionDegree M n ⟶ (freeModuleComonad (R := R)).iterObj M n :=
  (freeModuleComonad (R := R)).face M n i

/-- The `i`th degeneracy of the canonical free-module cotriple construction. -/
def freeModuleResolutionDegeneracy (M : ModuleCat.{u} R) (n : ℕ) (i : Fin (n + 1)) :
    freeModuleResolutionDegree M n ⟶ (freeModuleComonad (R := R)).iterObj M (n + 2) :=
  (freeModuleComonad (R := R)).degeneracy M n i

/-- The augmentation from degree zero to `M`. -/
def freeModuleResolutionAugmentation (M : ModuleCat.{u} R) :
    freeModuleResolutionDegree M 0 ⟶ M :=
  (freeModuleComonad (R := R)).augmentation M

end LeanCategories.Homological
