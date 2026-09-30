/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.BuiltinTactic

@[expose] public section

/-!
# Membership evidence: how a proof procedure establishes a hypothesis (LC-18)

The evidence of a domain `D ↪ B` is a proof procedure run on one hypothesis `P x` of the domain's
admission, at a closed value `x : B`. It establishes `P x` or fails: it never leaves a goal open, a
`sorry`, or an unassigned metavariable in the proof. `establish` is that contract; each domain's
procedure is written with the domain as `establish` applied to the domain's mathematics, and
`closeByFirst` tries the domain's cases in turn, restoring the state after each that fails.
-/

namespace CasCatalogue.Evidence

open Lean Meta Elab Tactic

/-- Run `procedure` on the main goal alone, so that it establishes that goal: afterwards no goal it
produced remains and the proof term contains no `sorry` and no metavariable. The other goals are
kept. Elaboration errors inside `procedure` are errors, never `sorry`. -/
meta def establish (domain : String) (procedure : TacticM Unit) : TacticM Unit := do
  let goal ← getMainGoal
  let statement ← instantiateMVars (← goal.getType)
  let others := (← getGoals).drop 1
  setGoals [goal]
  try
    Term.withoutErrToSorry procedure
  catch failure =>
    throwError "{domain}: the evidence does not establish{indentExpr statement}\n\
      {failure.toMessageData}"
  let open_ ← getUnsolvedGoals
  unless open_.isEmpty do
    throwError "{domain}: the evidence leaves {open_.length} goal(s) open for{indentExpr statement}"
  let proof ← instantiateMVars (mkMVar goal)
  if proof.hasSorry then
    throwError "{domain}: the evidence proves{indentExpr statement}\nwith `sorry`"
  if proof.hasExprMVar then
    throwError "{domain}: the evidence leaves a metavariable in the proof of{indentExpr statement}"
  setGoals others

/-- Close the main goal by the first procedure of `cases` that closes it; the state is restored
after each that fails or leaves goals. Fails with `failure` when none does. -/
meta def closeByFirst (failure : MessageData) : List (TacticM Unit) → TacticM Unit
  | [] => throwError failure
  | case :: cases => do
    let saved ← saveState
    try
      focusAndDone case
    catch _ =>
      saved.restore
      closeByFirst failure cases

end CasCatalogue.Evidence
