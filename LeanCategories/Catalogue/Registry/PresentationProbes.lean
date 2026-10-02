/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms
public import LeanCategories.Catalogue.Semantics.Algebra.RealLimits
public import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Magmas
public meta import LeanCategories.Catalogue.Semantics.Algebra.Units

@[expose] public section

/-!
# Presentation comparisons retain parameters and category structures

These probes admit the generic declarations and reject comparisons specialized
at a different monoid, and categorical data using a different category structure
on the same carrier. They add no semantic rows.
-/

open CategoryTheory

namespace CasCatalogue.PresentationProbes

/-- A deliberately different category structure on the same group-object carrier. -/
def unrelatedGroups : Category GrpCat.{0} where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

/-- A functor into the unrelated category, rather than the category of group maps. -/
def unrelatedConstruction (C : Cat.{0, 0}) :
    @Functor (Core C) inferInstance GrpCat.{0} unrelatedGroups := by
  letI : Category GrpCat.{0} := unrelatedGroups
  exact { obj := fun _ => GrpCat.of PUnit, map := fun _ => PUnit.unit }

/-- A comparison in the unrelated category on precisely the named group objects. -/
def unrelatedComparison (M : MonCat.{0}) :
    @Iso GrpCat.{0} unrelatedGroups (Algebra.Units.groupUnits M)
      (Algebra.Units.groupUnits M) :=
  @Iso.refl GrpCat.{0} unrelatedGroups _

/-- Correct units mathematics, but at a fixed monoid instead of the selected parameter. -/
def specializedComparison (_M : MonCat.{0}) :
    (forget GrpCat).obj (Algebra.Units.groupUnits (MonCat.of ℕ)) ≅
      Algebra.Units.units (MonCat.of ℕ) := Iso.refl _

open Lean Meta in
run_meta do
  let state ← semanticState
  let expectRefusal (label : String) (operation : MetaM Unit) := do
    let failure ← try operation; pure none catch e => pure (some (← e.toMessageData.toString))
    unless failure.isSome do throwError "accepted {label}"
  let some conditional := state.inclusions.find? (·.id.raw == "incl.sets.punctured_units")
    | throwError "missing conditional punctured-units inclusion"
  validateInclusion state conditional
  expectRefusal "a conditional inclusion treated as a shared-parameter family" <|
    validateInclusion state { conditional with parameterization := .shared }
  expectRefusal "a mono proof at different dependent parameters" <|
    validateInclusion state
      { conditional with mono := ``Algebra.RealLimits.realsExtendedReals_mono }
  let some units := state.objects.find? (·.id.raw == "obj.sets.units")
    | throwError "missing units presentation"
  let probe := { units with id := ⟨"obj.probe.units_presentation"⟩, name := "probe units" }
  validateObject state probe
  let some presentation := probe.functorPresentation
    | throwError "units have no functor presentation"
  expectRefusal "a comparison specialized at another monoid" <|
    validateObject state { probe with functorPresentation := some { presentation with identification := ``specializedComparison } }
  validateConstruction state
    { id := ⟨"con.probe.automorphisms"⟩, name := "probe automorphisms"
      declaration := ``Algebra.Automorphisms.automorphismsConstruction
      target := Algebra.Catalogue.Magmas.Groups }
  expectRefusal "a functor with the wrong group-category structure" <|
    validateConstruction state
      { id := ⟨"con.probe.unrelated"⟩, name := "probe unrelated"
        declaration := ``unrelatedConstruction, target := Algebra.Catalogue.Magmas.Groups }
  expectRefusal "an isomorphism in the wrong group-category structure" <|
    validatePresentation state
      { id := ⟨"cmp.probe.unrelated"⟩, name := "probe unrelated comparison"
        source := ⟨"obj.groups.units"⟩, target := ⟨"obj.groups.units"⟩
        declaration := ``unrelatedComparison }

end CasCatalogue.PresentationProbes
