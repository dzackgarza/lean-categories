/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

/-!
# The annihilator as an isomorphism invariant

The annihilator `Ann_R(M) = {r | r • M = 0}` of an `R`-module depends on `M` only up to
isomorphism (`LinearEquiv.annihilator_eq`): a functor `Core(Mod_R) ⥤ Disc(Ideal R)`.
-/

open CategoryTheory

namespace LeanCategories.Modules

universe w u

/-- `Ann_R`, on the core of `R`-modules. -/
def annihilatorFunctor (R : Type u) [Ring R] : Core (ModuleCat.{w} R) ⥤ Discrete (Ideal R) where
  obj M := ⟨Module.annihilator R M.of⟩
  map f := eqToHom (congrArg Discrete.mk f.iso.toLinearEquiv.annihilator_eq)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

end LeanCategories.Modules
