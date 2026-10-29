/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

open CategoryTheory

namespace CasCatalogue.Foundation.PowerSetsTests

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- A family specialized to a fixed source cannot implement the general action. -/
def specializedDirectImage (X Y : Type) (_f : (X : Type) ⟶ (Y : Type)) :
    powerSet ℕ ⟶ powerSet Y := TypeCat.ofHom fun _ => ∅

/-- A generalized subset retains an arbitrary, possibly infinite, outer stage. -/
example (S X Y : Type) (A : (S : Type) ⟶ powerSet X)
    (f : (X : Type) ⟶ (Y : Type)) (s : S) (y : Y) :
    y ∈ (A ≫ directImage X Y f) s ↔ ∃ x, x ∈ A s ∧ f x = y :=
  directImage_at_stage S X Y A f s y

open Lean Meta in
run_meta do
  let state ← semanticState
  let some row := state.powerObjects.find? (·.id.raw == "pow.sets")
    | throwError "missing the selected powerset interface"
  validatePowerObject state row
  let expectRefusal (label : String) (name : Name) := do
    let rejected ← try
        validatePowerObject state { row with directImage := some name }
        pure false
      catch _ => pure true
    unless rejected do throwError "accepted {label} as the whole direct-image action"
  expectRefusal "the global-image operation" ``image
  expectRefusal "a source specialized to the natural numbers" ``specializedDirectImage

end CasCatalogue.Foundation.PowerSetsTests
