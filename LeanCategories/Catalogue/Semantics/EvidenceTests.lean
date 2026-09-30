/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Semirings
public import LeanCategories.Catalogue.Semantics.Algebra.Units
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence
public meta import LeanCategories.Catalogue.Semantics.Algebra.Semirings
public meta import LeanCategories.Catalogue.Semantics.Algebra.Units
public meta import Lean.Meta.Closure

@[expose] public section

/-!
# Tests of the registered membership evidence (LC-18)

Each domain's registered evidence is run, as a consumer runs it, through `Lean.Elab.Tactic.run`
on the admission's hypothesis at closed values. A value of the domain is established, and the
proof is checked by the kernel; a value outside the domain is refused (the procedure fails).
-/

namespace CasCatalogue.EvidenceTests

open Lean Meta Elab Tactic

/-- The row `row` registers `procedure` as its evidence. -/
meta def expectRegistered (row : String) (procedure : Name) : MetaM Unit := do
  let state ← semanticState
  let some entry := state.objects.find? (·.id.raw == row)
    | throwError "{row} is not registered"
  unless entry.evidence == some procedure do
    throwError "{row} registers the evidence {entry.evidence}, not {procedure}"

/-- Run `procedure` on the closed statement `statement` through `Lean.Elab.Tactic.run`. `some`
proof when it closes the goal with a `sorry`-free proof that the kernel accepts; `none` when it
fails. A procedure that returns with goals open is an error of the procedure. -/
meta def run (procedure : TacticM Unit) (statement : Term) : TermElabM (Option Expr) := do
  let type ← Term.elabType statement
  Term.synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  if type.hasMVar then throwError "the statement{indentExpr type}\nis not closed"
  let goal ← mkFreshExprMVar type
  let saved ← saveState
  let remaining ← try Tactic.run goal.mvarId! procedure catch _ => saved.restore; return none
  unless remaining.isEmpty do
    throwError "the evidence returned with {remaining.length} goal(s) open on{indentExpr type}"
  let proof ← instantiateMVars goal
  if proof.hasSorry || proof.hasMVar then
    throwError "the evidence proved{indentExpr type}\nwith `sorry` or a metavariable"
  -- The kernel checks the proof.
  discard <| mkAuxTheorem type proof
  return some proof

/-- `procedure` establishes each statement. -/
meta def expectEstablished (procedure : TacticM Unit) (statements : List Term) :
    TermElabM Unit := do
  for statement in statements do
    if (← run procedure statement).isNone then
      throwError "the evidence does not establish {statement}"

/-- `procedure` refuses each statement: it fails, establishing nothing. -/
meta def expectRefused (procedure : TacticM Unit) (statements : List Term) :
    TermElabM Unit := do
  for statement in statements do
    if (← run procedure statement).isSome then
      throwError "the evidence establishes {statement}, which is false"

end CasCatalogue.EvidenceTests

namespace CasCatalogue.EvidenceTests

open CasCatalogue.Algebra

/-! ## `Mˣ ↪ M`: `IsUnit x` -/

#guard_msgs in
run_meta expectRegistered "obj.sets.units" ``Units.isUnitEvidence

#guard_msgs in
run_elab do
  expectEstablished Units.isUnitEvidence
    [← `(IsUnit (2 : ℚ)), ← `(IsUnit (-3 / 4 : ℝ)),
      ← `(IsUnit (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ)),
      ← `(IsUnit (5 : ZMod 7)), ← `(IsUnit (-1 : ℤ)),
      ← `(IsUnit (!![1, 2, 0; 3, 4, 1; 0, 5, 7] : Matrix (Fin 3) (Fin 3) ℚ)),
      ← `(IsUnit (!![2, 1, 0, 0; 0, 1, 3, 0; 1, 0, 1, 1; 0, 2, 0, 5] :
        Matrix (Fin 4) (Fin 4) ℚ)),
      ← `(IsUnit (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ)),
      ← `(IsUnit (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 2))),
      ← `(IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)),
      ← `(IsUnit (1 : ℕ)), ← `(IsUnit (3 : ZMod 10)), ← `(IsUnit (-(7 : ZMod 12))),
      ← `(IsUnit ((-1 : ℤ) ^ 5)), ← `(IsUnit (Real.pi)), ← `(IsUnit (Real.sqrt 2)),
      ← `(IsUnit (2 + 3 * Complex.I)), ← `(IsUnit (Complex.I)),
      ← `(IsUnit (1 / 3 - 1 / 4 : ℚ))]

#guard_msgs in
run_elab do
  expectRefused Units.isUnitEvidence
    [← `(IsUnit (2 : ℤ)), ← `(IsUnit (0 : ℚ)),
      ← `(IsUnit (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℚ)),
      ← `(IsUnit (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)),
      ← `(IsUnit (!![1, 2, 3; 4, 5, 6; 7, 8, 9] : Matrix (Fin 3) (Fin 3) ℚ)),
      ← `(IsUnit (2 : ℕ)), ← `(IsUnit (0 : ℕ)), ← `(IsUnit (2 : ZMod 4)),
      ← `(IsUnit (6 : ZMod 9)), ← `(IsUnit ((2 : ℤ) * 3)), ← `(IsUnit (1 / 2 - 2 / 4 : ℚ))]

/-! ## `ℕ⁺ ↪ ℕ`: `0 < n` -/

#guard_msgs in
run_meta expectRegistered "obj.sets.positive_naturals" ``Semirings.positiveEvidence

#guard_msgs in
run_elab do
  expectEstablished Semirings.positiveEvidence
    [← `(0 < 1), ← `(0 < 2), ← `(0 < 2 ^ 100 - 3), ← `(0 < 7 * 13 + 1),
      ← `(0 < Nat.factorial 5), ← `(0 < 1000000007 % 97), ← `(0 < 10 / 3)]

#guard_msgs in
run_elab do
  expectRefused Semirings.positiveEvidence
    [← `(0 < 0), ← `(0 < 3 - 5), ← `(0 < 2 * 0 + 0), ← `(0 < 2 / 3), ← `(0 < 91 % 7)]

/-! ## `ℙ ↪ ℕ`: `n.Prime` -/

#guard_msgs in
run_meta expectRegistered "obj.sets.primes" ``Semirings.primeEvidence

#guard_msgs in
run_elab do
  expectEstablished Semirings.primeEvidence
    [← `(Nat.Prime 2), ← `(Nat.Prime 3), ← `(Nat.Prime 97), ← `(Nat.Prime 1000003),
      ← `(Nat.Prime (2 ^ 19 - 1)), ← `(Nat.Prime (2 ^ 5 - 1)), ← `(Nat.Prime (Nat.factorial 3 + 1)),
      ← `(Nat.Prime (10 ^ 6 + 3))]

#guard_msgs in
run_elab do
  expectRefused Semirings.primeEvidence
    [← `(Nat.Prime 0), ← `(Nat.Prime 1), ← `(Nat.Prime 91), ← `(Nat.Prime (2 ^ 11 - 1)),
      ← `(Nat.Prime 1000001), ← `(Nat.Prime 561)]

end CasCatalogue.EvidenceTests
