/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Fixed

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- Postcomposition by `f : W → W'` as a natural transformation of form functors. -/
def changeValueNatTrans {W' : Type u} [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') : bilinearForms R W ⟶ bilinearForms R W' where
  app M := ↾fun b ↦ f.comp b
  naturality M N g := by
    ext b
    rfl

/-- Change the value module of a bilinear form by postcomposition. -/
def changeValue {W' : Type u} [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') : BilinModuleCat R W ⥤ BilinModuleCat R W' :=
  (NatTrans.mapElements (changeValueNatTrans R W f)).op

/-- Changing values along the identity map is the identity functor. -/
theorem changeValue_id :
    changeValue R W LinearMap.id = 𝟭 (BilinModuleCat R W) :=
  rfl

/-- Successive value changes equal change along the composite map. -/
theorem changeValue_comp {W' W'' : Type u}
    [AddCommGroup W'] [Module R W']
    [AddCommGroup W''] [Module R W'']
    (f : W →ₗ[R] W') (g : W' →ₗ[R] W'') :
    changeValue R W (g.comp f) =
      changeValue R W f ⋙ changeValue R W' g :=
  rfl

end LeanCategories.Modules.Bilinear.Valued
