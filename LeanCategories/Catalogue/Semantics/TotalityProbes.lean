/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Probes of the totality gate (LC-14, LC-16)

Each encoding the catalogue once used for a partial or structureless operation is refused when it
is registered. A unit's inverse and division by a unit are accepted. The refused rows are never
registered, because the command fails.
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

/-- error: registry row mor.probe.field_divide is refused by the totality gate:
  CasCatalogue.TotalityProbes.fieldDivide applies HDiv.hDiv on ℚ, which is not a group: inverses and division exist on units and automorphisms only (LC-16)
An operation is a total morphism out of its domain object, and exists only where its structure exists (CONTRIBUTING LC-14, LC-16). -/
#guard_msgs in
normalized_registry .morphism
  { id := ⟨"mor.probe.field_divide"⟩, category := CategoryId.sets, name := "probe /"
    declaration := `CasCatalogue.TotalityProbes.fieldDivide }

end CasCatalogue
