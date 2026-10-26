/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
public meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
public meta import LeanCategories.Catalogue.Registry.Computation

@[expose] public section

/-!
# Formal interface probes for complete computational derivations

These are source-level positive and separating checks of the upstream API. They
do not install implementations, inspect leaves, or compare computational answers.
-/

open CategoryTheory

namespace CasCatalogue.ComputationProbes

open CasCatalogue.Algebra

/-- An identity plan is a mathematically valid self-dependent equation. -/
def identityMulPlan
    (mul : (M : MonCat.{0}) → (M × M : Type) ⟶ (M : Type)) := mul

theorem identityMulPlan_correct :
    identityMulPlan MonoidOperations.mul = MonoidOperations.mul := rfl

/-- The identity retains the independent ring and numeral parameters. -/
def identityPowerPlan
    (pow : (R : RingCat.{0}) → ℕ → ((R : Type) ⟶ (R : Type))) := pow

theorem identityPowerPlan_correct :
    identityPowerPlan NamedRings.pow = NamedRings.pow := rfl

/-- A discarded let occurrence cannot manufacture a required primitive. -/
def unusedPlan
    (mul : (M : MonCat.{0}) → (M × M : Type) ⟶ (M : Type)) :=
  let _discarded := mul
  NamedRings.mul

theorem unusedPlan_correct :
    unusedPlan MonoidOperations.mul = NamedRings.mul := rfl

/-- A proof-only occurrence cannot manufacture a required primitive. -/
def proofOnlyPlan
    (mul : (M : MonCat.{0}) → (M × M : Type) ⟶ (M : Type)) :=
  have _ : mul = mul := rfl
  NamedRings.mul

theorem proofOnlyPlan_correct :
    proofOnlyPlan MonoidOperations.mul = NamedRings.mul := rfl

/-- This equation is valid only after choosing a ring, so it is not a derivation
of the complete ring-indexed operation. -/
def selectedObjectPlan
    (mul : (R : RingCat.{0}) → (R × R : Type) ⟶ (R : Type)) :=
  mul NamedRings.ringIntegers

theorem selectedObjectPlan_correct :
    selectedObjectPlan NamedRings.mul = NamedRings.mul NamedRings.ringIntegers := rfl

/-- This equation omits the independent exponent parameter. -/
def selectedNumeralPlan
    (pow : (R : RingCat.{0}) → ℕ → ((R : Type) ⟶ (R : Type)))
    (R : RingCat.{0}) := pow R 0

theorem selectedNumeralPlan_correct :
    selectedNumeralPlan NamedRings.pow = (fun R => NamedRings.pow R 0) := rfl

/-- A universe-zero equation does not prove the polymorphic functor family. -/
def selectedUniversePlan := Ports.ringsMultiplicative.{0}

theorem selectedUniversePlan_correct :
    selectedUniversePlan = Ports.ringsMultiplicative.{0} := rfl

open Lean Meta

meta def requireRejected (label : String) (entry : ComputationDerivationEntry) : MetaM Unit := do
  let rejected ← withoutModifyingState do
    try
      let _ ← validateComputationDerivation (← semanticState) entry
      pure false
    catch _ => pure true
  unless rejected do throwError "computation probe accepted {label}"

run_meta do
  let state ← semanticState
  let alternatives ← checkedComputationDerivations (.operation ⟨"op.rings.mul"⟩)
  unless alternatives.size == 2 do
    throwError "both independently proved ring multiplication plans must be retained"
  for checked in alternatives do
    unless checked.entry.target == .operation ⟨"op.rings.mul"⟩ do
      throwError "a plan changed its exact target operation"
    unless ← isDefEq (← inferType checked.plan) checked.familyType do
      throwError "the applied plan lost the complete target type"
    unless ← isDefEq (← inferType checked.correctness) (← mkEq checked.plan checked.target) do
      throwError "a checked derivation lost its whole-family proof"
    unless checked.prerequisites.size == 2 do
      throwError "the plan lost its selected functor or multiplication prerequisite"
  let some viaSemiring := alternatives.find?
    (·.entry.id.raw == "derive.rings.mul.semiring")
    | throwError "the chain through semiring multiplication is absent"
  unless viaSemiring.prerequisites.any
      (·.reference == .operation ⟨"op.semirings.mul"⟩) do
    throwError "the selected semiring operation address was erased"
  let middle ← checkedComputationDerivations (.operation ⟨"op.semirings.mul"⟩)
  let #[middlePlan] := middle
    | throwError "the semiring multiplication plan is absent or duplicated"
  unless middlePlan.prerequisites.any (·.reference == .operation ⟨"op.monoids.mul"⟩) do
    throwError "the second link of the multiplication chain is absent"
  let functorPlans ← checkedComputationDerivations (.functor FunctorId.ringsMultiplicative)
  let #[functorPlan] := functorPlans
    | throwError "the functor plan is absent or duplicated"
  unless !functorPlan.universeParams.isEmpty do
    throwError "the whole polymorphic functor derivation is absent"
  let primitive ← checkedComputationDerivations (.operation ⟨"op.monoids.mul"⟩)
  unless primitive.isEmpty do
    throwError "this catalogue must not invent a computation for the primitive"
  let ring := viaSemiring.entry
  requireRejected "an unknown target"
    { ring with target := .operation ⟨"op.unregistered"⟩ }
  requireRejected "an unknown prerequisite"
    { ring with prerequisites := #[.functor FunctorId.ringsSemiring,
        .operation ⟨"op.unregistered"⟩] }
  requireRejected "an omitted primitive slot"
    { ring with prerequisites := #[.functor FunctorId.ringsSemiring] }
  requireRejected "the wrong full prerequisite family"
    { ring with prerequisites := #[.functor FunctorId.ringsSemiring,
        .operation ⟨"op.rings.mul"⟩] }
  requireRejected "a proof about the additive operation"
    { ring with correctness := ``MonoidOperationAgreement.additive_port }
  requireRejected "a proposition unrelated to whole-family equality"
    { ring with correctness := ``True.intro }
  requireRejected "a discarded prerequisite"
    { id := ⟨"probe.unused"⟩, target := .operation ⟨"op.rings.mul"⟩
      prerequisites := #[.operation ⟨"op.monoids.mul"⟩]
      plan := ``unusedPlan, correctness := ``unusedPlan_correct }
  requireRejected "a proof-only prerequisite"
    { id := ⟨"probe.proof_only"⟩, target := .operation ⟨"op.rings.mul"⟩
      prerequisites := #[.operation ⟨"op.monoids.mul"⟩]
      plan := ``proofOnlyPlan, correctness := ``proofOnlyPlan_correct }
  requireRejected "a selected ring in place of its full family"
    { id := ⟨"probe.selected_object"⟩, target := .operation ⟨"op.rings.mul"⟩
      prerequisites := #[.operation ⟨"op.rings.mul"⟩]
      plan := ``selectedObjectPlan, correctness := ``selectedObjectPlan_correct }
  requireRejected "a selected exponent in place of its full family"
    { id := ⟨"probe.selected_numeral"⟩, target := .operation ⟨"op.rings.pow"⟩
      prerequisites := #[.operation ⟨"op.rings.pow"⟩]
      plan := ``selectedNumeralPlan, correctness := ``selectedNumeralPlan_correct }
  requireRejected "a selected universe in place of its full family"
    { id := ⟨"probe.selected_universe"⟩, target := .functor FunctorId.ringsMultiplicative
      prerequisites := #[]
      plan := ``selectedUniversePlan, correctness := ``selectedUniversePlan_correct }
  -- A self-dependent equation is valid mathematics. This check establishes no
  -- computational availability; only a consumer can ground a derivation tree.
  let cycle ← validateComputationDerivation state
    { id := ⟨"probe.cycle"⟩, target := .operation ⟨"op.monoids.mul"⟩
      prerequisites := #[.operation ⟨"op.monoids.mul"⟩]
      plan := ``identityMulPlan, correctness := ``identityMulPlan_correct }
  let #[cyclePrerequisite] := cycle.prerequisites
    | throwError "the self-dependent plan lost its prerequisite"
  unless cyclePrerequisite.reference == cycle.entry.target do
    throwError "the valid self-dependency was not retained"
  let power ← validateComputationDerivation state
    { id := ⟨"probe.dependent_parameters"⟩, target := .operation ⟨"op.rings.pow"⟩
      prerequisites := #[.operation ⟨"op.rings.pow"⟩]
      plan := ``identityPowerPlan, correctness := ``identityPowerPlan_correct }
  forallTelescope power.familyType fun parameters _ => do
    unless parameters.size == 2 do
      throwError "the complete ring and exponent parameters were not preserved"
  -- All existing family kinds use their exact published declarations.
  for entry in state.methods do
    let actual ← (ComputationRef.method entry.id).declaration state
    let expected ← (ComputationRef.functor entry.functor).declaration state
    unless actual == expected do throwError "method reference lost its registered functor"
  for entry in state.constructions do
    unless (← (ComputationRef.construction entry.id).declaration state) == entry.declaration do
      throwError "construction reference lost its registered family"
  for entry in state.morphisms do
    unless (← (ComputationRef.morphism entry.id).declaration state) == entry.declaration do
      throwError "morphism reference lost its registered family"

end CasCatalogue.ComputationProbes
