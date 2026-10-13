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

The core 1-cells carry their equivalence witnesses.  Their restricted
composition is therefore constructed directly by composing those witnesses,
using Mathlib's existing bicategorical adjointification machinery.  The two
whiskerings, associator, and unitors are the corresponding restrictions of the
ambient bicategory operations.  Verifying the bicategory coherence laws is
proposition work and is not bundled into Sweep III.
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
abbrev homProperty (X Y : B) : ObjectProperty (Core (X ⟶ Y)) :=
  fun f ↦ IsEquivalence1Cell B f.of

/-- Kerodon's core hom-category: the full subcategory of the pith hom-category
spanned by equivalence 1-morphisms. -/
abbrev Hom (X Y : B) :=
  (homProperty B X Y).FullSubcategory

/-- The identity 1-morphism as an object of the core hom-category. -/
def idData (X : B) : Hom B X X :=
  ⟨⟨𝟙 X⟩, ⟨Equivalence.id X, rfl⟩⟩

/-- Unit 2-isomorphism for the composite of two equivalence 1-cells.

This is assembled entirely from the two supplied equivalence witnesses and
the ambient bicategory coherence isomorphisms. -/
noncomputable def equivalenceCompUnitIso {X Y Z : B}
    (e : X ≌ Y) (e' : Y ≌ Z) :
    𝟙 X ≅ (e.hom ≫ e'.hom) ≫ e'.inv ≫ e.inv :=
  e.unit ≪⊗≫
    (whiskerLeftIso e.hom e'.unit ▷ᵢ e.inv) ≪⊗≫
      Iso.refl _

/-- Counit 2-isomorphism for the composite of two equivalence 1-cells. -/
noncomputable def equivalenceCompCounitIso {X Y Z : B}
    (e : X ≌ Y) (e' : Y ≌ Z) :
    (e'.inv ≫ e.inv) ≫ e.hom ≫ e'.hom ≅ 𝟙 Z :=
  Iso.refl _ ≪⊗≫
    (whiskerLeftIso e'.inv e.counit ▷ᵢ e'.hom) ≪⊗≫
      e'.counit

/-- Composite of two already-supplied equivalence 1-cells.

No closure theorem is proved here: the input equivalence witnesses are part of
the core-cell data, and Mathlib's existing adjointification constructor
packages their composite. -/
noncomputable def equivalenceComp {X Y Z : B}
    (e : X ≌ Y) (e' : Y ≌ Z) : X ≌ Z :=
  Equivalence.mkOfAdjointifyCounit
    (equivalenceCompUnitIso B e e')
    (equivalenceCompCounitIso B e e')

/-- A chosen equivalence witness carried by a core 1-cell. -/
noncomputable def equivalenceWitness {X Y : B}
    (f : Hom B X Y) :
    {e : X ≌ Y // e.hom = f.obj.of} :=
  Classical.choice <| f.property.elim fun e he => ⟨⟨e, he⟩⟩

/-- Actual restricted composition of core 1-cells.

The composite equivalence witness is obtained from the witnesses already
carried by the two input objects. This constructs the source's restricted
composition operation without proving a separate closure proposition. -/
noncomputable def compData {X Y Z : B}
    (f : Hom B X Y) (g : Hom B Y Z) : Hom B X Z := by
  refine ⟨⟨f.obj.of ≫ g.obj.of⟩, ?_⟩
  refine ⟨equivalenceComp B (equivalenceWitness B f).1 (equivalenceWitness B g).1, ?_⟩
  change (equivalenceWitness B f).1.hom ≫ (equivalenceWitness B g).1.hom =
    f.obj.of ≫ g.obj.of
  rw [(equivalenceWitness B f).2, (equivalenceWitness B g).2]

/-- Left whiskering in the core, obtained by restricting ambient whiskering to
invertible 2-cells. -/
noncomputable def whiskerLeftData {X Y Z : B}
    (f : Hom B X Y) {g h : Hom B Y Z} (η : g ⟶ h) :
    compData B f g ⟶ compData B f h :=
  ObjectProperty.homMk
    (CoreHom.mk <| whiskerLeftIso f.obj.of η.hom.iso)

/-- Right whiskering in the core, obtained by restricting ambient whiskering
to invertible 2-cells. -/
noncomputable def whiskerRightData {X Y Z : B}
    {f g : Hom B X Y} (η : f ⟶ g) (h : Hom B Y Z) :
    compData B f h ⟶ compData B g h :=
  ObjectProperty.homMk
    (CoreHom.mk <| whiskerRightIso η.hom.iso h.obj.of)

/-- Associator of the core, inherited from the ambient bicategory. -/
noncomputable def associatorData {W X Y Z : B}
    (f : Hom B W X) (g : Hom B X Y) (h : Hom B Y Z) :
    compData B (compData B f g) h ≅ compData B f (compData B g h) :=
  ObjectProperty.isoMk (P := homProperty B W Z) <| Core.isoMk <|
    α_ f.obj.of g.obj.of h.obj.of

/-- Left unitor of the core, inherited from the ambient bicategory. -/
noncomputable def leftUnitorData {X Y : B} (f : Hom B X Y) :
    compData B (idData B X) f ≅ f :=
  ObjectProperty.isoMk (P := homProperty B X Y) <| Core.isoMk <| λ_ f.obj.of

/-- Right unitor of the core, inherited from the ambient bicategory. -/
noncomputable def rightUnitorData {X Y : B} (f : Hom B X Y) :
    compData B f (idData B Y) ≅ f :=
  ObjectProperty.isoMk (P := homProperty B X Y) <| Core.isoMk <| ρ_ f.obj.of

/-- Exact graph of the core composition law.

`IsCompData f g h` says that the underlying 1-morphism of `h` is exactly the
bicategorical composite of the underlying 1-morphisms of `f` and `g`. -/
def IsCompData {X Y Z : B}
    (f : Hom B X Y) (g : Hom B Y Z) (h : Hom B X Z) : Prop :=
  h.obj.of = f.obj.of ≫ g.obj.of

/-- Raw construction package for the definition-level core data.

The identity and restricted composition are actual operations. The separate
graph remains available for consumers that need the source equation without
bundling the bicategory coherence laws. -/
structure StructureData where
  id : ∀ X : B, Hom B X X
  comp : ∀ {X Y Z : B}, Hom B X Y → Hom B Y Z → Hom B X Z
  IsComp : ∀ {X Y Z : B}, Hom B X Y → Hom B Y Z → Hom B X Z → Prop

/-- The source-prescribed identity and actual restricted composition package. -/
noncomputable def structureData : StructureData B where
  id := idData B
  comp := fun f g => compData B f g
  IsComp := IsCompData B

end BicategoryCoreData

end LeanCategories.ForMathlib
