/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Constructions
public import LeanCategories.Catalogue.Holds
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Expressions

@[expose] public section

/-!
# Alternating formed modules retain the chosen form

The property and its full subcategory are owned by
`LeanCategories.Modules.Bilinear.Valued.isAlternatingBilinModule` and
`AltBilinModuleCat`. The classifier retains the actual formed module; its projection
forgets only the proof of alternation. No new carrier, value module or pairing is
chosen by classification.
-/

open CategoryTheory LeanCategories LeanCategories.Modules.Bilinear.Valued
namespace CasCatalogue.Modules.Bilinear.Valued.Alternating
open _root_.CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration
universe u

/-- The classifier of alternation for the actual selected scalar and value modules. -/
noncomputable def alternatingClassifier (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    Classifier (bilinModuleCategory R W) :=
  Classifier.ofProperty (C := bilinModuleCategory R W) (isAlternatingBilinModule R W)

noncomputable def alternatingRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    ClassifierRealization Catalogue.BilinModule ⟨"clf.bilin_module.alternating"⟩
      (bilinModuleCategory R W) (alternatingClassifier R W) :=
  { hostRealization := bilinModuleRealization R W, totalRealization := {} }

/-- The existing full subcategory of alternating formed modules. -/
noncomputable def alternatingCategory (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :=
  (alternatingClassifier R W).total

noncomputable def alternatingCategoryRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    CategoryRealization (.classifierTotal ⟨"clf.bilin_module.alternating"⟩)
      (alternatingCategory R W) := {}

/-- An actual chosen form with the full proof of alternation retained. -/
def alternating (R : CommRingCat.{u}) (M W : ModuleCat.{u} R)
    (b : Constructions.bilinearMaps R M M W)
    (h : (Constructions.bilinear R M W b).IsAlternating) : AltBilinModuleCat R W :=
  ⟨Constructions.bilinear R M W b, h⟩

end CasCatalogue.Modules.Bilinear.Valued.Alternating

namespace CasCatalogue
normalized_registry .classifier
  { id := ⟨"clf.bilin_module.alternating"⟩
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Alternating.alternatingClassifier
    host := Modules.Bilinear.Valued.Catalogue.BilinModule
    realization := `CasCatalogue.Modules.Bilinear.Valued.Alternating.alternatingRealization }
normalized_registry .category
  { id := ⟨"cat.alternating_forms"⟩, name := "AlternatingForms"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Alternating.alternatingCategory
    expression := .classifierTotal ⟨"clf.bilin_module.alternating"⟩
    realization :=
      `CasCatalogue.Modules.Bilinear.Valued.Alternating.alternatingCategoryRealization }
normalized_registry .property
  { id := ⟨"prop.bilin_module.is_alternating"⟩, name := "is_alternating"
    classifier := ⟨"clf.bilin_module.alternating"⟩ }
normalized_registry .object
  { id := ⟨"obj.alternating_forms.chosen_form"⟩, category := ⟨"cat.alternating_forms"⟩
    name := "AlternatingForm"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Alternating.alternating }
end CasCatalogue
