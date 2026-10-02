/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Calculus
public import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Constants of parameterized objects retain their actual source (LC-13)

The coefficient parameter of the power-series family is a commutative ring
object. The constants map starts at its underlying set. Legacy set parameters
still work, and neither a point of the power-series object nor an unrelated map
can be substituted for its constants. These probes register no rows.
-/

namespace CasCatalogue

open Lean Meta in
run_meta do
  let state ← semanticState
  for id in ["obj.sets.power_series", "obj.sets.polynomials"] do
    let some row := state.objects.find? (·.id.raw == id)
      | throwError "missing constants specimen {id}"
    let probe := { row with id := ⟨"obj.probe.constants"⟩, name := "probe constants" }
    validateObject state probe
  let some row := state.objects.find? (·.id.raw == "obj.sets.power_series")
    | throwError "missing power-series specimen"
  let probe := { row with id := ⟨"obj.probe.constants"⟩, name := "probe constants" }
  for constants in [``Algebra.Calculus.powerSeriesGenerator, ``Algebra.Calculus.sin] do
    let refusal ← try
      validateObject state { probe with constants := some constants }
      pure none
    catch e => pure (some (← e.toMessageData.toString))
    match refusal with
    | none => throwError "accepted unrelated constants map {constants}"
    | some message =>
        unless (message.splitOn "underlying set to it").length > 1 do
          throwError "constants map {constants} refused for another reason: {message}"

end CasCatalogue
