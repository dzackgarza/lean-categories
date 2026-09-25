/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Core data of a bicategory

Definition-level realization of Kerodon Construction 2.2.8.27, tag `02BB`
(`FC17-KER-U02698`).

For a bicategory `B`, the core has the same objects as `B`.  Its hom-category
from `X` to `Y` is the full subcategory of the pith hom-category
`Hom_B(X,Y)^≃` spanned by those 1-morphisms which are equivalences.

Kerodon obtains the restricted composition law from Remark 2.2.8.22, the
result that equivalence 1-morphisms are closed under composition.  Sweep III
does not prove that result.  Instead this file records the exact graph of the
restricted composition.  Proving that this graph is total and single-valued,
and then packaging the resulting operations and coherence data as a
`Bicategory`, is result-layer work.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Bicategory

namespace LeanCategories.ForMathlib

universe w v u

variable (B : Type u) [Bicategory.{w, v} B]

namespace BicategoryCoreData

/-- Predicate selecting the invertible 1-morphisms of a bicategory. -/
def IsEquivalence1Cell {X Y : B} (f : X ⟶ Y) : Prop :=
  ∃ e : X ≌ Y, e.hom = f

/-- Kerodon's core hom-category: the full subcategory of the pith hom-category
spanned by equivalence 1-morphisms. -/
abbrev Hom (X Y : B) :=
  ObjectProperty.FullSubcategory
    (C := Core (X ⟶ Y))
    (fun f ↦ IsEquivalence1Cell B f.of)

/-- The identity 1-morphism as an object of the core hom-category. -/
def idData (X : B) : Hom B X X :=
  ⟨⟨𝟙 X⟩, ⟨Equivalence.id X, rfl⟩⟩

/-- Exact graph of the core composition law.

`IsCompData f g h` says that the underlying 1-morphism of `h` is exactly the
bicategorical composite of the underlying 1-morphisms of `f` and `g`.  The
existence of such an `h` for every `f,g` is precisely the closure result used
by Kerodon Remark 2.2.8.22 and is not proved here. -/
def IsCompData {X Y Z : B}
    (f : Hom B X Y) (g : Hom B Y Z) (h : Hom B X Z) : Prop :=
  h.obj.of = f.obj.of ≫ g.obj.of

/-- Raw construction package for the definition-level core data. -/
structure StructureData where
  id : ∀ X : B, Hom B X X
  IsComp : ∀ {X Y Z : B}, Hom B X Y → Hom B Y Z → Hom B X Z → Prop

/-- The source-prescribed identity and restricted-composition graph. -/
def structureData : StructureData B where
  id := idData B
  IsComp := IsCompData B

end BicategoryCoreData

end LeanCategories.ForMathlib
