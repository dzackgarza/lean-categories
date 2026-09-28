/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.FibrationCatalogue
public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Modules.CatalogueRegistration
public import LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration
public import LeanCategories.Exceptional.CatalogueRegistration
public meta import LeanCategories.Catalogue.FibrationCatalogue
public meta import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Modules.Expressions
public meta import LeanCategories.Algebra.Catalogue.Rings

@[expose] public section

/-!
# Registered fibrations (CC-FIB)

Each row registers a projection functor and a Lean proof that it is a cartesian or cocartesian
fibration (`FibrationEntry`); registration checks that the proof is about exactly the realized
projection.

* `fib.modules` — `∫ᶜ Mod → Ring`, cartesian, reindexing = restriction of scalars
  (`CategoryFamilyRealization.projection_isFibered`).
* `fib.modules_ext` — `∫ Mod → CommRing`, cocartesian, transport = extension of scalars
  (`Pseudofunctor.Grothendieck.isCofibered_forget`).
* `fib.bilin_forms` — `p : Bil → ∫ Mod`, cocartesian (FOUNDATIONS Proposition 31.2b,
  `BilinFormsOverRings.isCofibered_values`).
-/

namespace LeanCategories.Catalogue.FibrationRegistration

open CategoryTheory LeanCategories
open LeanCategories.Modules.CatalogueRegistration
open LeanCategories.Lattices.Valued

noncomputable section

universe u w

/-! ### `fib.modules` -/

noncomputable def modulesProjectionDeclaration :
    modulesTotalCategory.{u, w} ⥤ Algebra.Rings.{u} :=
  modulesFamilyRealization.{u, w}.projection

noncomputable def modulesProjectionRealization :
    FunctorRealization Fibrations.ModulesProjectionExpr modulesTotalCategory.{u, w}
      Algebra.Rings.{u} modulesProjectionDeclaration :=
  { sourceRealization := modulesTotalRealization
    targetRealization := Algebra.CatalogueRegistration.ringsRealization }

theorem modulesProjection_isFibered : modulesProjectionDeclaration.{u, w}.IsFibered :=
  modulesFamilyRealization.{u, w}.projection_isFibered

/-! ### `fib.modules_ext` -/

noncomputable def modulesOverRingsExtCategory : ObjCat.{u + 1, u} :=
  Cat.of ModulesOverRingsExt.{u}

noncomputable def modulesOverRingsExtRealization :
    CategoryRealization Fibrations.ModulesOverRingsExt modulesOverRingsExtCategory.{u} := {}

noncomputable def modulesExtRingDeclaration :
    modulesOverRingsExtCategory.{u} ⥤ Algebra.CommutativeRings.{u} :=
  ModulesOverRingsExt.ring

noncomputable def modulesExtRingRealization :
    FunctorRealization Fibrations.ModulesExtRingExpr modulesOverRingsExtCategory.{u}
      Algebra.CommutativeRings.{u} modulesExtRingDeclaration :=
  { sourceRealization := modulesOverRingsExtRealization
    targetRealization := Algebra.CatalogueRegistration.commutativeRingsRealization }

theorem modulesExtRing_isCofibered : modulesExtRingDeclaration.{u}.IsCofibered :=
  Pseudofunctor.Grothendieck.isCofibered_forget _

/-! ### `fib.bilin_forms` -/

noncomputable def bilinFormsOverRingsCategory : ObjCat.{u + 1, u} :=
  Cat.of BilinFormsOverRings.{u}

noncomputable def bilinFormsOverRingsRealization :
    CategoryRealization Fibrations.BilinFormsOverRings bilinFormsOverRingsCategory.{u} := {}

noncomputable def bilinFormsValuesDeclaration :
    bilinFormsOverRingsCategory.{u} ⥤ modulesOverRingsExtCategory.{u} :=
  BilinFormsOverRings.values

noncomputable def bilinFormsValuesRealization :
    FunctorRealization Fibrations.BilinFormsValuesExpr bilinFormsOverRingsCategory.{u}
      modulesOverRingsExtCategory.{u} bilinFormsValuesDeclaration :=
  { sourceRealization := bilinFormsOverRingsRealization
    targetRealization := modulesOverRingsExtRealization }

theorem bilinFormsValues_isCofibered : bilinFormsValuesDeclaration.{u}.IsCofibered :=
  BilinFormsOverRings.isCofibered_values

normalized_registry .functor
  { id := FunctorId.modulesProjection,
    source := Modules.ModulesTotal
    target := Algebra.Catalogue.Rings.Rings
    declaration :=
      `LeanCategories.Catalogue.FibrationRegistration.modulesProjectionDeclaration
    realization :=
      `LeanCategories.Catalogue.FibrationRegistration.modulesProjectionRealization
    expression := Fibrations.ModulesProjectionExpr }
normalized_registry .fibration
  { id := FibrationId.modules, projection := FunctorId.modulesProjection,
    variance := .cartesian
    evidence := `LeanCategories.Catalogue.FibrationRegistration.modulesProjection_isFibered }

normalized_registry .category
  { id := CategoryId.modulesOverRingsExt,
    declaration :=
      `LeanCategories.Catalogue.FibrationRegistration.modulesOverRingsExtCategory
    expression := Fibrations.ModulesOverRingsExt
    realization :=
      `LeanCategories.Catalogue.FibrationRegistration.modulesOverRingsExtRealization }
normalized_registry .functor
  { id := FunctorId.modulesExtRing,
    source := Fibrations.ModulesOverRingsExt
    target := Algebra.Catalogue.Rings.CommutativeRings
    declaration := `LeanCategories.Catalogue.FibrationRegistration.modulesExtRingDeclaration
    realization := `LeanCategories.Catalogue.FibrationRegistration.modulesExtRingRealization
    expression := Fibrations.ModulesExtRingExpr }
normalized_registry .fibration
  { id := FibrationId.modulesExt, projection := FunctorId.modulesExtRing,
    variance := .cocartesian
    evidence := `LeanCategories.Catalogue.FibrationRegistration.modulesExtRing_isCofibered }

normalized_registry .category
  { id := CategoryId.bilinFormsOverRings,
    declaration :=
      `LeanCategories.Catalogue.FibrationRegistration.bilinFormsOverRingsCategory
    expression := Fibrations.BilinFormsOverRings
    realization :=
      `LeanCategories.Catalogue.FibrationRegistration.bilinFormsOverRingsRealization }
normalized_registry .functor
  { id := FunctorId.bilinFormsValues,
    source := Fibrations.BilinFormsOverRings
    target := Fibrations.ModulesOverRingsExt
    declaration := `LeanCategories.Catalogue.FibrationRegistration.bilinFormsValuesDeclaration
    realization := `LeanCategories.Catalogue.FibrationRegistration.bilinFormsValuesRealization
    expression := Fibrations.BilinFormsValuesExpr }
normalized_registry .fibration
  { id := FibrationId.bilinForms, projection := FunctorId.bilinFormsValues,
    variance := .cocartesian
    evidence := `LeanCategories.Catalogue.FibrationRegistration.bilinFormsValues_isCofibered }

end

/-! ### Negative probes: evidence must prove the stated variance of the registered projection -/

open Lean Meta Elab Command in
run_cmd
  liftTermElabM do
    let rejects (entry : RegistryEntry) : MetaM Bool := do
      try
        validateRegistryEntryDeclaration entry
        pure false
      catch _ => pure true
    -- cartesian evidence registered as cocartesian
    unless ← rejects (.fibration
        { id := ⟨"fib.probe.variance"⟩, projection := FunctorId.modulesProjection,
          variance := .cocartesian
          evidence :=
            `LeanCategories.Catalogue.FibrationRegistration.modulesProjection_isFibered }) do
      throwError "cartesian evidence was accepted for a cocartesian fibration"
    -- evidence about another functor
    unless ← rejects (.fibration
        { id := ⟨"fib.probe.functor"⟩, projection := FunctorId.bilinFormsValues,
          variance := .cocartesian
          evidence :=
            `LeanCategories.Catalogue.FibrationRegistration.modulesExtRing_isCofibered }) do
      throwError "evidence about q was accepted for p"
    -- positive control
    if ← rejects (.fibration
        { id := ⟨"fib.probe.control"⟩, projection := FunctorId.bilinFormsValues,
          variance := .cocartesian
          evidence :=
            `LeanCategories.Catalogue.FibrationRegistration.bilinFormsValues_isCofibered }) then
      throwError "the canonical forms fibration was rejected"

end LeanCategories.Catalogue.FibrationRegistration
