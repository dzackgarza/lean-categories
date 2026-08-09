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

end LeanCategories.Modules.Bilinear.Valued

