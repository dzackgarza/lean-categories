/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Modules.Expressions

@[expose] public section

/-!
# Torsion-free modules

The property `NoZeroSMulDivisors R M` of an `R`-module, as a classifier on `Mod_R`
(`clf.modules.torsion_free`): its total is the full subcategory of torsion-free modules
(`cat.torsion_free_modules`). No operation is declared on it: everything it has, it inherits along
its forgetful functor. Torsion-freeness passes to submodules, but no lift of subobjects is
registered, so a kernel of torsion-free modules is not yet returned to them.
-/

open CategoryTheory
open LeanCategories

namespace CasCatalogue.Modules.TorsionFree

universe u

/-- The torsion-free property on `R`-modules. -/
noncomputable def torsionFree (R : RingCat.{u}) :
    Classifier (Modules.Mathlib.ModulesOf.{u, u} R) where
  total := Cat.of (ObjectProperty.FullSubcategory
    (C := ModuleCat.{u} R) fun M => NoZeroSMulDivisors R M)
  forget := (ObjectProperty.ι (C := ModuleCat.{u} R) fun M => NoZeroSMulDivisors R M).toCatHom

noncomputable def torsionFreeModules (R : RingCat.{u}) := (torsionFree R).total

noncomputable def torsionFreeRealization (R : RingCat.{u}) :
    ClassifierRealization Modules.Modules ⟨"clf.modules.torsion_free"⟩
      (Modules.Mathlib.ModulesOf.{u, u} R) (torsionFree R) :=
  { hostRealization := CasCatalogue.Modules.CatalogueRegistration.modulesRealization R
    totalRealization := {} }

noncomputable def torsionFreeModulesRealization (R : RingCat.{u}) :
    CategoryRealization (.classifierTotal ⟨"clf.modules.torsion_free"⟩)
      (torsionFreeModules R) := { familyFibre := none }

end CasCatalogue.Modules.TorsionFree

namespace CasCatalogue

normalized_registry .classifier
  { id := ⟨"clf.modules.torsion_free"⟩
    declaration := `CasCatalogue.Modules.TorsionFree.torsionFree
    host := Modules.Modules
    realization := `CasCatalogue.Modules.TorsionFree.torsionFreeRealization }

normalized_registry .category
  { id := ⟨"cat.torsion_free_modules"⟩
    declaration := `CasCatalogue.Modules.TorsionFree.torsionFreeModules
    expression := .classifierTotal ⟨"clf.modules.torsion_free"⟩
    realization := `CasCatalogue.Modules.TorsionFree.torsionFreeModulesRealization }

end CasCatalogue
