/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
public meta import Lean.Elab.Tactic.Basic

@[expose] public section

/-! Intrinsic tests of selected presentation point evaluation and its metadata validation.
These exercise the source's defining maps and coefficient data, independently of any consumer. -/
namespace CasCatalogue.PresentationEvaluationTests
open Algebra.PolynomialPresentations
open LeanCategories.Algebra.PolynomialPresentation
open Lean Meta Elab Tactic Command

meta def registeredEvaluation : TacticM Unit := do
  let state ← semanticState
  let some row := state.presentations.find? (·.id.raw == "cmp.f9.translation")
    | throwError "missing selected F9 comparison"
  let some name := row.evaluation | throwError "missing comparison evaluation"
  let procedure ← unsafe evalConst (TacticM Unit) name
  procedure

example : quadraticComparison.hom (AdjoinRoot.root firstPolynomial) =
    AdjoinRoot.root secondPolynomial + 2 := by run_tac registeredEvaluation

example : quadraticComparison.inv (AdjoinRoot.root secondPolynomial) =
    AdjoinRoot.root firstPolynomial - 2 := by run_tac registeredEvaluation

example : ((CategoryTheory.forget CommRingCat).map quadraticComparison.hom)
    (firstGenerator 0) = secondGenerator 0 + 2 := by run_tac registeredEvaluation

example : ((CategoryTheory.forget CommRingCat).map quadraticComparison.inv)
    (secondGenerator 0) = firstGenerator 0 - 2 := by run_tac registeredEvaluation

example (c : ZMod 3) : quadraticComparison.hom (firstConstants c) =
    secondConstants c := by run_tac registeredEvaluation

example (c : ZMod 3) : quadraticComparison.inv (secondConstants c) =
    firstConstants c := by run_tac registeredEvaluation

example : quadraticComparison.hom ((AdjoinRoot.root firstPolynomial) ^ 3 +
    firstConstants 2) = (AdjoinRoot.root secondPolynomial + 2) ^ 3 + secondConstants 2 := by
  run_tac registeredEvaluation

example : quadraticComparison.inv ((AdjoinRoot.root secondPolynomial) ^ 3 -
    secondConstants 1) = (AdjoinRoot.root firstPolynomial - 2) ^ 3 - firstConstants 1 := by
  run_tac registeredEvaluation

example (a b : ZMod 3) : quadraticComparison.hom (firstConstants a + firstConstants b) =
    secondConstants a + secondConstants b := by run_tac registeredEvaluation

example : quadraticComparison.hom
    (Algebra.NamedRings.ringNumeral (RingCat.of first) 1 0) = (1 : second) := by
  run_tac registeredEvaluation

/-- A false action cannot be closed by the registered evaluator. -/
example : quadraticComparison.hom (AdjoinRoot.root firstPolynomial) ≠
    AdjoinRoot.root secondPolynomial := comparison_root_ne

-- Refuse the false identity action even when the same two selected quotient objects occur.
run_cmd liftTermElabM do
  let statements ← pure #[
    (← `(quadraticComparison.hom (AdjoinRoot.root firstPolynomial) =
      AdjoinRoot.root secondPolynomial)),
    (← `(quadraticComparison.hom (firstConstants 1) = secondConstants 0)),
    (← `((CategoryTheory.Iso.refl first).hom (AdjoinRoot.root firstPolynomial) =
      AdjoinRoot.root firstPolynomial + 2))]
  for statement in statements do
    let type ← Term.elabType statement
    Term.synthesizeSyntheticMVarsNoPostponing
    let goal ← mkFreshExprMVar (← instantiateMVars type)
    let saved ← saveState
    let closed ← try
      let remaining ← Tactic.run goal.mvarId! registeredEvaluation
      pure remaining.isEmpty
    catch _ => pure false
    saved.restore
    if closed then throwError "false or unrelated selected comparison action was proved"

meta def notProcedure : Nat := 0

def notMeta : TacticM Unit := pure ()

run_meta do
  let state ← semanticState
  let some row := state.presentations.find? (·.id.raw == "cmp.f9.translation")
    | throwError "missing comparison"
  let without := { state with presentations := state.presentations.filter (·.id != row.id) }
  validatePresentation without row
  for procedure in [``notProcedure, ``notMeta, `CasCatalogue.absentPresentationEvaluation] do
    let refused ← try
      validatePresentation without { row with evaluation := some procedure }
      pure false
    catch _ => pure true
    unless refused do throwError "invalid comparison evaluator accepted"
  let wrong := { row with declaration := ``CategoryTheory.Iso.refl }
  let refused ← try validatePresentation without wrong; pure false catch _ => pure true
  unless refused do throwError "comparison with unrelated endpoints accepted"

end CasCatalogue.PresentationEvaluationTests
