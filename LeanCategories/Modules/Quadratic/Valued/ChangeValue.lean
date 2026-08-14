/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Fixed

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- Postcomposition by `f : W → W'` as a natural transformation of quadratic-map functors. -/
def changeValueNatTrans {W' : Type u} [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') : quadraticMaps R W ⟶ quadraticMaps R W' where
  app M := ↾fun q : QuadraticMap R ((M.unop : ModuleCat R) : Type u) W ↦
    f.compQuadraticMap q
  naturality M N g := by
    ext q
    rfl

/-- Change the value module of a quadratic form by postcomposition. -/
def changeValue {W' : Type u} [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') : QuadModuleCat R W ⥤ QuadModuleCat R W' :=
  (NatTrans.mapElements (changeValueNatTrans R W f)).op

/-- Changing values along the identity map is the identity functor. -/
theorem changeValue_id :
    changeValue R W LinearMap.id = 𝟭 (QuadModuleCat R W) :=
  by
    apply Functor.hext
    · intro Q
      rfl
    · intro Q P f
      rfl

/-- Successive value changes equal change along the composite map. -/
theorem changeValue_comp {W' W'' : Type u}
    [AddCommGroup W'] [Module R W']
    [AddCommGroup W''] [Module R W'']
    (f : W →ₗ[R] W') (g : W' →ₗ[R] W'') :
    changeValue R W (g.comp f) =
      changeValue R W f ⋙ changeValue R W' g :=
  by
    apply Functor.hext
    · intro Q
      rfl
    · intro Q P h
      rfl

end LeanCategories.Modules.Quadratic.Valued
