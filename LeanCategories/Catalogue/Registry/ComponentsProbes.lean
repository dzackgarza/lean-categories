/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.CatalogueRegistration
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Data.Fin.Rev
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Full selected cones in component metadata

The positive witness is Mathlib's product of a two-element constant family. Reindexing that
same full limit cone by `Fin.revPerm` gives another genuine limiting cone with exactly the same
apex and diagram, but different ordered legs. It must be refused as evidence for the original
coordinate family. General coordinate families without a universal-property witness remain
valid. These are upstream schema controls, with no claims about downstream computations.
-/

open CategoryTheory Limits

namespace CasCatalogue.Registry.ComponentsProbes

universe u

def twoFunctions (X : Type u) : Type u := Fin 2 → X
def twoArity (_X : Type u) : ℕ := 2
def evaluation (X : Type u) (i : Fin 2) : twoFunctions X ⟶ X :=
  TypeCat.ofHom fun f => f i

/-- The complete limit cone with the original ordered coordinate evaluations. -/
def coordinateIsLimit (X : Type u) : IsLimit (Fan.mk (twoFunctions X) (evaluation X)) :=
  (Types.productLimitCone (fun _ : Fin 2 => X)).isLimit

/-- A genuine full limit cone on the same apex and same constant diagram, with swapped legs. -/
def swappedIsLimit (X : Type u) :
    IsLimit (Fan.mk (twoFunctions X) (fun i : Fin 2 => evaluation X (Fin.rev i))) :=
  Fan.isLimitEquivOfEquiv Fin.revPerm (Fan.mk (twoFunctions X) (evaluation X))
    (coordinateIsLimit X)

/-- A valid limit witness whose object parameter is fixed instead of retained. -/
def fixedIsLimit (_X : Type u) :
    IsLimit (Fan.mk (twoFunctions PUnit.{u + 1}) (evaluation PUnit.{u + 1})) :=
  coordinateIsLimit PUnit.{u + 1}

/-- A witness with an additional hypothesis does not cover the complete object family. -/
def restrictedIsLimit (X : Type u) (_h : Nonempty X) :
    IsLimit (Fan.mk (twoFunctions X) (evaluation X)) :=
  coordinateIsLimit X

def repeatedObject (X : Type u) : Type u := X
def repeatedProjection (X : Type u) (_i : Fin 2) : repeatedObject X ⟶ X := 𝟙 X

open Lean Meta Elab Command in
run_cmd
  liftTermElabM do
    let state ← semanticState
    let components : ObjectComponents :=
      { arity := `CasCatalogue.Registry.ComponentsProbes.twoArity
        projection := `CasCatalogue.Registry.ComponentsProbes.evaluation
        isLimit := some `CasCatalogue.Registry.ComponentsProbes.coordinateIsLimit }
    let object : ObjectEntry :=
      { id := ⟨"probe.components.selected_product"⟩, category := CategoryId.sets
        name := "ProbeSelectedProduct"
        declaration := `CasCatalogue.Registry.ComponentsProbes.twoFunctions
        components := some components }
    validateObject state object
    let rejects (description : String) (witness : Name) : MetaM Unit := do
      let candidate := { object with components := some { components with isLimit := some witness } }
      let accepted ← try
        validateObject state candidate
        pure true
      catch _ => pure false
      if accepted then throwError "component validation accepted {description}"
    rejects "a full limit cone with the same apex and diagram but swapped ordered legs"
      `CasCatalogue.Registry.ComponentsProbes.swappedIsLimit
    rejects "a fixed object in place of the full selected object parameter"
      `CasCatalogue.Registry.ComponentsProbes.fixedIsLimit
    rejects "a witness requiring an extra hypothesis on the object"
      `CasCatalogue.Registry.ComponentsProbes.restrictedIsLimit
    validateObject state
      { id := ⟨"probe.components.without_product_claim"⟩, category := CategoryId.sets
        name := "ProbeRepeatedCoordinates"
        declaration := `CasCatalogue.Registry.ComponentsProbes.repeatedObject
        components := some
          { arity := `CasCatalogue.Registry.ComponentsProbes.twoArity
            projection := `CasCatalogue.Registry.ComponentsProbes.repeatedProjection } }

end CasCatalogue.Registry.ComponentsProbes
