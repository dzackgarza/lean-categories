/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
public import LeanCategories.Catalogue.Semantics.Foundation.Maps
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Admission belongs to the named object (LC-18)

`Maps (Fin 1) ℝ` and `Vec ℝ 1` have the same function carrier, but are different
named catalogue objects (Foundation/Maps.lean). A coordinate operation on `Vec`
cannot borrow `Maps`' admission. It becomes a valid binder only when `Vec` has
its own admission of vectors. All hypothetical rows remain local to these
probes; no vector admission or binder is registered.
-/

open CategoryTheory

namespace CasCatalogue.AdmissionOwnerProbes

open Foundation.Objects Foundation.Maps Algebra.LinearAlgebra Algebra.NumberSystems

def coordinate : vectors ℝ 1 ⟶ reals := TypeCat.ofHom fun v => v 0

def mapCoordinate : maps (Fin 1) ℝ ⟶ reals := TypeCat.ofHom fun f => f 0

def coordinateDomain : LeanCategories.Foundation.Mathlib.Sets.{0} := Fin 1

/-- Every vector belongs to the vector object, without any further hypothesis. -/
def admitVector (X : Type) (n : ℕ) (v : Fin n → X) : fin 1 ⟶ vectors X n :=
  TypeCat.ofHom fun _ => v

end CasCatalogue.AdmissionOwnerProbes

namespace CasCatalogue

open Lean Meta in
run_meta do
  let state ← semanticState
  let binder : BinderEntry :=
    { id := ⟨"bind.probe.coordinate"⟩, category := CategoryId.sets, token := "coordinate"
      operation := ``AdmissionOwnerProbes.coordinate
      domain := ``AdmissionOwnerProbes.coordinateDomain }
  -- The genuine map-object admission is still accepted.
  validateBinder state { binder with operation := ``AdmissionOwnerProbes.mapCoordinate }
  let expectRefused (check : MetaM Unit) (fragment : String) : MetaM Unit := do
    let refusal ← try check; pure none
      catch e => pure (some (← e.toMessageData.toString))
    match refusal with
    | none => throwError "admission-owner probe was accepted ({fragment})"
    | some message =>
        unless (message.splitOn fragment).length > 1 do
          throwError "admission-owner probe refused for another reason: {message}"
  -- A carrier match alone supplies no admission to the vector object.
  expectRefused (validateBinder state binder) "with an admission and evidence"
  let some vectors := state.objects.find? (·.id.raw == "obj.sets.vectors")
    | throwError "missing vector specimen"
  let admitted := { vectors with
    id := ⟨"obj.probe.admitted_vectors"⟩
    name := "probe admitted vectors"
    admission := some ``AdmissionOwnerProbes.admitVector
    evidence := some ``Foundation.Maps.mapsEvidence }
  validateObject state admitted
  validateBinder { state with objects := state.objects.push admitted } binder
  -- Registration refuses an admission that actually lands in another named object.
  let forged := { admitted with admission := some ``Foundation.Maps.admit }
  expectRefused (validateObject state forged) "does not land in it"
  -- Even an independently assembled state cannot lend that foreign admission to Vec.
  expectRefused (validateBinder { state with objects := state.objects.push forged } binder)
    "with an admission and evidence"

end CasCatalogue
