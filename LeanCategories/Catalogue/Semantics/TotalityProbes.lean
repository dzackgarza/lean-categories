/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import LeanCategories.Catalogue.Semantics.Algebra.Units
public meta import Lean
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Probes of the totality gate (LC-14, LC-16) and of registered evidence

Each encoding the catalogue once used for a partial or structureless operation is refused when it
is registered. A unit's inverse and division by a unit are accepted. The refused rows are never
registered, because the command fails.

The evidence of a domain is a `meta` proof procedure `TacticM Unit` of `lean-categories`,
registered with an admission: evidence without an admission, of another type, or not `meta`, is
refused, and so is an admission with a hypothesis that is neither a proposition nor a subsingleton.
-/

open CategoryTheory

namespace CasCatalogue.TotalityProbes

open CasCatalogue.Foundation.PowerSets

/-- The element literal `k ↦ some k` of `Fin n`, `none` off `k < n` (the pre-LC-15 form). -/
def optionLiteral (n k : ℕ) : Option (Fin n) := if h : k < n then some ⟨k, h⟩ else none

/-- `k ↦ some k` as a morphism into `Option (Fin n)`. -/
def optionLiteralHom (n : ℕ) : (ℕ : SetsCat.{0}) ⟶ (Option (Fin n) : SetsCat.{0}) :=
  TypeCat.ofHom (optionLiteral n)

/-- `M ↦ M⁻¹` on all of `Matₙ(ℚ)` (Lean's `nonsing_inv`, `0` off `GLₙ`). -/
noncomputable def matrixInverse (n : ℕ) :
    (Matrix (Fin n) (Fin n) ℚ : SetsCat.{0}) ⟶ (Matrix (Fin n) (Fin n) ℚ : SetsCat.{0}) :=
  TypeCat.ofHom fun M => M⁻¹

/-- `(a, b) ↦ a / b` on all of `ℚ × ℚ` (Lean's `a / 0 = 0`). -/
def fieldDivide : (ℚ × ℚ : SetsCat.{0}) ⟶ (ℚ : SetsCat.{0}) := TypeCat.ofHom fun p => p.1 / p.2

/-- `u ↦ u⁻¹` on `ℚˣ`, a group: accepted. -/
def unitInverse : (ℚˣ : SetsCat.{0}) ⟶ (ℚˣ : SetsCat.{0}) := TypeCat.ofHom fun u => u⁻¹

/-- `(a, u) ↦ a u⁻¹` on `ℚ × ℚˣ`: accepted. -/
def unitDivide : (ℚ × ℚˣ : SetsCat.{0}) ⟶ (ℚ : SetsCat.{0}) :=
  TypeCat.ofHom fun p => p.1 * ↑(p.2⁻¹)

/-- An admission into `Mˣ` whose hypothesis carries an element of `M` besides the inverse: data
with more than one value, so the admitted unit would not be determined by `x`. -/
def probeAdmitData (M : Type) [Monoid M] (x : M) (h : M × Invertible x) :
    CasCatalogue.Foundation.Objects.fin 1 ⟶ CasCatalogue.Algebra.Units.units (MonCat.of M) :=
  TypeCat.ofHom fun _ => @unitOfInvertible M _ x h.2

/-- A proof procedure: well-formed evidence, but here registered without an admission. -/
meta def probeEvidence : Lean.Elab.Tactic.TacticM Unit := pure ()

/-- Not a proof procedure. -/
meta def probeNotEvidence : Nat := 0

/-- A proof procedure that is not `meta`. -/
def probeEvidenceNotMeta : Lean.Elab.Tactic.TacticM Unit := pure ()

end CasCatalogue.TotalityProbes

namespace CasCatalogue

open Lean Meta in
run_meta do
  for refused in [`CasCatalogue.TotalityProbes.optionLiteralHom,
      `CasCatalogue.TotalityProbes.matrixInverse, `CasCatalogue.TotalityProbes.fieldDivide] do
    if (← totalityViolations refused).isEmpty then
      throwError "the totality gate accepts {refused}"
  for accepted in [`CasCatalogue.TotalityProbes.unitInverse,
      `CasCatalogue.TotalityProbes.unitDivide] do
    let violations ← totalityViolations accepted
    unless violations.isEmpty do
      throwError "the totality gate refuses {accepted}: {violations}"

open Lean Meta in
run_meta do
  let state ← semanticState
  let some units := state.objects.find? (·.id.raw == "obj.sets.units")
    | throwError "obj.sets.units is not registered"
  let probe := { units with id := ⟨"obj.probe.evidence"⟩, name := "probe evidence" }
  let cases : List (ObjectEntry × String) :=
    [({ probe with admission := none, evidence := some `CasCatalogue.TotalityProbes.probeEvidence },
        "without an admission"),
     ({ probe with evidence := some `CasCatalogue.TotalityProbes.probeNotEvidence },
        "is not a proof procedure"),
     ({ probe with evidence := some `CasCatalogue.TotalityProbes.probeEvidenceNotMeta },
        "is not `meta`"),
     ({ probe with admission := some `CasCatalogue.TotalityProbes.probeAdmitData },
        "is neither a proposition nor a subsingleton")]
  for (row, fragment) in cases do
    let refused ← try validateObject state row; pure none
      catch e => pure (some (← e.toMessageData.toString))
    match refused with
    | some message =>
        unless (message.splitOn fragment).length > 1 do
          throwError "evidence refused for another reason than '{fragment}': {message}"
    | none => throwError "evidence accepted: {row.evidence} ('{fragment}')"
  validateObject state { probe with evidence := some `CasCatalogue.TotalityProbes.probeEvidence }

/-- error: registry row mor.probe.field_divide is refused by the totality gate:
  CasCatalogue.TotalityProbes.fieldDivide applies HDiv.hDiv on ℚ, which is not a group: inverses and division exist on units and automorphisms only (LC-16)
An operation is a total morphism out of its domain object, and exists only where its structure exists (CONTRIBUTING LC-14, LC-16). -/
#guard_msgs in
normalized_registry .morphism
  { id := ⟨"mor.probe.field_divide"⟩, category := CategoryId.sets, name := "probe /"
    declaration := `CasCatalogue.TotalityProbes.fieldDivide }

end CasCatalogue
