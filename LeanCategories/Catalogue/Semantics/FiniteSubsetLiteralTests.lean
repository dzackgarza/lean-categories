/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
public meta import Lean.Elab.Tactic.BuiltinTactic
public meta import Lean.Meta.Closure

@[expose] public section

/-!
# Finite-subset literals: denotation, evaluation and cardinality

Over the catalogue's own declarations: the literal form `lit.sets.finite_subsets` of the power
object `pow.sets` (`FiniteSubsetLiterals.literal`), the operations `∪ ∩ \ △` of the Boolean algebra
`𝒫(X)` applied through the registered product cone `lim.sets.product`, and the registered
cardinality functor `fun.sets.cardinality` with the cardinal literals `lit.cardinals`.

Equality in `𝒫(ℤ) = Set ℤ` is not decidable in general; between literals it is. An equation
between an operation's image of literals and a literal is decided by the literal form's registered
evaluation (`FiniteSubsetLiterals.evaluation`, which rewrites the image to a literal by the generic
lemmas `union_literal`, …, `cardinality_literal`) and `decide`, whose proof is a kernel evaluation
of equality of `Finset`s (resp. of cardinal literals).

The last section runs the evaluation as a consumer of the catalogue runs it: read from the row
`lit.sets.finite_subsets`, evaluated by name, through `Lean.Elab.Tactic.run`, on statements in
exactly the term shapes a consumer forms (expected-type hints `@id T a`, the operation applied as
the composite `lift (BinaryFan.mk A B) ≫ op`, elements as ring numerals, the cardinality functor
applied to an object of `Core Sets` with Mathlib's instances), followed by `decide`; the proof is
checked by the kernel.
-/

namespace CasCatalogue.FiniteSubsetLiteralTests

open CategoryTheory
open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.FiniteSubsetLiterals
open CasCatalogue.Foundation.Cardinality

/-! ## Running the registered evaluation -/

open Lean Meta Elab Tactic in
/-- The evaluation registered for `lit.sets.finite_subsets`, read from the registry. -/
meta def registeredEvaluation : CoreM Name := do
  let state ← semanticState
  let some entry := state.subsetLiterals.find? (·.id.raw == "lit.sets.finite_subsets")
    | throwError "lit.sets.finite_subsets is not registered"
  let some procedure := entry.evaluation
    | throwError "lit.sets.finite_subsets registers no evaluation"
  unless procedure == ``CasCatalogue.Foundation.FiniteSubsetLiterals.evaluation do
    throwError "lit.sets.finite_subsets registers the evaluation {procedure}"
  return procedure

open Lean Meta Elab Tactic in
/-- Run the registered evaluation, found by its name in the registry and evaluated as a consumer
evaluates it, on the main goal. -/
meta def runRegisteredEvaluation : TacticM Unit := do
  let name ← registeredEvaluation
  let procedure ← unsafe evalConst (TacticM Unit) name
  procedure

open Lean Meta Elab Tactic in
/-- Run the registered evaluation and then `decide` on the closed statement `statement`, through
`Lean.Elab.Tactic.run`: `some` proof when they close it with a `sorry`-free proof, which the kernel
then checks; `none` when they fail. -/
meta def evaluateAndDecide (statement : Term) : TermElabM (Option Expr) := do
  let type ← Term.elabType statement
  Term.synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  if type.hasMVar then throwError "the statement{indentExpr type}\nis not closed"
  let goal ← mkFreshExprMVar type
  let saved ← saveState
  let remaining ← try
      Tactic.run goal.mvarId! do
        runRegisteredEvaluation
        evalTactic (← `(tactic| decide))
    catch _ => saved.restore; return none
  unless remaining.isEmpty do
    throwError "the evaluation and `decide` left {remaining.length} goal(s) open \
      on{indentExpr type}"
  let proof ← instantiateMVars goal
  if proof.hasSorry || proof.hasMVar then
    throwError "proved{indentExpr type}\nwith `sorry` or a metavariable"
  -- The kernel checks the proof.
  discard <| mkAuxTheorem type proof
  return some proof

open Lean Elab Term in
/-- Each statement is established by the registered evaluation and `decide`. -/
meta def expectDecided (statements : List Term) : TermElabM Unit := do
  for statement in statements do
    if (← evaluateAndDecide statement).isNone then
      throwError "the evaluation and `decide` do not establish {statement}"

open Lean Elab Term in
/-- No statement is established: each is false. -/
meta def expectRefused (statements : List Term) : TermElabM Unit := do
  for statement in statements do
    if (← evaluateAndDecide statement).isSome then
      throwError "the evaluation and `decide` establish {statement}, which is false"

/-! ## Denotation and evaluation -/

/-- The literal `[1, 2, 3]` denotes the subset `{1, 2, 3} ⊆ ℤ`. -/
example : ConcreteCategory.hom (C := Type) (literal ℤ [1, 2, 3].toFinset) 0 =
    ({1, 2, 3} : Set ℤ) := by
  ext x; simp [literal]

/-- Reordered and repeated lists are the same literal, and denote the same subset. -/
example : literal ℤ [3, 1, 2, 2].toFinset = literal ℤ [1, 2, 3].toFinset := by decide

/-- `{1, 2, 3} ≠ {1, 2}` in `𝒫(ℤ)`. -/
example : literal ℤ {1, 2, 3} ≠ literal ℤ {1, 2} := by decide

/-- `{1, 2, 3} ∪ {3, 4, 5} = {1, 2, 3, 4, 5}` in `𝒫(ℤ)`. -/
example : applyBinary (union (boolPowerSet ℤ)) (literal ℤ {1, 2, 3}) (literal ℤ {3, 4, 5}) =
    literal ℤ {1, 2, 3, 4, 5} := by
  (run_tac runRegisteredEvaluation); decide

/-- `{1, 2, 3} ∪ {3, 4, 5} ≠ {1, 2, 3, 4}` in `𝒫(ℤ)`. -/
example : applyBinary (union (boolPowerSet ℤ)) (literal ℤ {1, 2, 3}) (literal ℤ {3, 4, 5}) ≠
    literal ℤ {1, 2, 3, 4} := by
  (run_tac runRegisteredEvaluation); decide

/-- `{1, 2, 3} ∩ {3, 4, 5} = {3}` in `𝒫(ℕ)`. -/
example : applyBinary (inter (boolPowerSet ℕ)) (literal ℕ {1, 2, 3}) (literal ℕ {3, 4, 5}) =
    literal ℕ {3} := by
  (run_tac runRegisteredEvaluation); decide

/-- `{0, 1, 2} \ {2, 3} = {0, 1}` in `𝒫(ℤ/5)`. -/
example : applyBinary (diff (boolPowerSet (ZMod 5))) (literal (ZMod 5) {0, 1, 2})
    (literal (ZMod 5) {2, 3}) = literal (ZMod 5) {0, 1} := by
  (run_tac runRegisteredEvaluation); decide

/-- `{0, 1, 2} △ {2, 3} = {0, 1, 3}` in `𝒫(Fin 4)`, and not `{0, 1}`. -/
example : applyBinary (Foundation.PowerSets.symmDiff (boolPowerSet (Fin 4)))
    (literal (Fin 4) {0, 1, 2})
    (literal (Fin 4) {2, 3}) = literal (Fin 4) {0, 1, 3} := by
  (run_tac runRegisteredEvaluation); decide

example : applyBinary (Foundation.PowerSets.symmDiff (boolPowerSet (Fin 4)))
    (literal (Fin 4) {0, 1, 2})
    (literal (Fin 4) {2, 3}) ≠ literal (Fin 4) {0, 1} := by
  (run_tac runRegisteredEvaluation); decide

/-- `{-1, 2} ∪ {2, 3} = {-1, 2, 3}` in `𝒫(ℚ)`. -/
example : applyBinary (union (boolPowerSet ℚ)) (literal ℚ {-1, 2}) (literal ℚ {2, 3}) =
    literal ℚ {-1, 2, 3} := by
  (run_tac runRegisteredEvaluation); decide

/-- `|{1, 2, 3}| = 3`, by the cardinality functor. -/
example : setsCardinality.obj (⟨extent ℤ (literal ℤ {1, 2, 3})⟩ : Core Type) =
    CardinalLiteral.denote 3 := by
  (run_tac runRegisteredEvaluation); decide

/-- `|{1, 2, 2, 3}| ≠ 4` and `≠ ℵ₀`: a repeated element is counted once. -/
example : setsCardinality.obj (⟨extent ℤ (literal ℤ [1, 2, 2, 3].toFinset)⟩ : Core Type) ≠
    CardinalLiteral.denote 4 := by
  (run_tac runRegisteredEvaluation); decide

example : setsCardinality.obj (⟨extent ℤ (literal ℤ {1, 2, 3})⟩ : Core Type) ≠
    CardinalLiteral.denote .aleph0 := by
  (run_tac runRegisteredEvaluation); decide

/-- `|{1, 2, 3} ∪ {3, 4, 5}| = 5`. -/
example : setsCardinality.obj (⟨extent ℤ (applyBinary (union (boolPowerSet ℤ))
    (literal ℤ {1, 2, 3}) (literal ℤ {3, 4, 5}))⟩ : Core Type) = CardinalLiteral.denote 5 := by
  (run_tac runRegisteredEvaluation); decide

/-! ## A consumer's term shapes -/

/- A consumer's statements over `ℤ`, in the term shapes it forms. `A = {1, 2, 3}` and
`B = {3, 4, 5}` are literals of the named set `ℤ` whose elements are the ring numerals of `ℤ`
(LC-15), and `{a₁, …, aₙ}` is `insert a₁ (… (singleton aₙ))`, as the notation elaborates. `A ∪ B`
is the composite of the mediator of the product cone and `∪`, each under an expected-type hint
`@id T _`, and the whole under one. `|·|` is the cardinality functor applied to the extent of a
subset, in each spelling of a functor's action on an object: `setsCardinality.obj ⟨…⟩`
(`Functor.obj`), `Prefunctor.obj setsCardinality.toPrefunctor ⟨…⟩` (as `mkAppM` forms it), and the
latter over `Core Sets` with the instances of Mathlib's `Core` (`CategoryTheory.coreCategory`). -/
open Lean Elab Term in
#guard_msgs in
run_elab do
  let n (k : Nat) : TermElabM Term := do
    let k := Syntax.mkNumLit (toString k)
    `(ConcreteCategory.hom (Algebra.NamedRings.ringNumeral Algebra.NamedRings.ringIntegers $k) 0)
  let subset (ks : List Nat) : TermElabM Term := do
    let some last := ks.getLast? | throwError "no elements"
    let finset ← ks.dropLast.foldrM (fun k rest => do `(Insert.insert $(← n k) $rest))
      (← `((Singleton.singleton $(← n last) : Finset Foundation.Objects.integers)))
    `(Foundation.FiniteSubsetLiterals.literal Foundation.Objects.integers $finset)
  let A ← subset [1, 2, 3]
  let B ← subset [3, 4, 5]
  let union : Term ← `(@id (Foundation.Objects.fin 1 ⟶ Foundation.PowerSets.powerSet ℤ)
    (CategoryStruct.comp
      (@id _ ((Limits.Registration.setsProduct
          (Foundation.PowerSets.powerSet Foundation.Objects.integers)
          (Foundation.PowerSets.powerSet Foundation.Objects.integers)).isLimit.lift
        (Limits.BinaryFan.mk $A $B)))
      (@id _ (Foundation.PowerSets.union
        (Foundation.PowerSets.boolPowerSet Foundation.Objects.integers)))))
  let object (subset : Term) : TermElabM Term :=
    `(Core.mk (Foundation.PowerSets.extent Foundation.Objects.integers $subset))
  -- `F.obj X`, `Functor.obj`.
  let card (subset : Term) : TermElabM Term := do
    `(Foundation.Cardinality.setsCardinality.obj $(← object subset))
  -- `Prefunctor.obj F.toPrefunctor X`.
  let prefunctorCard (subset : Term) : TermElabM Term := do
    `(Prefunctor.obj (Functor.toPrefunctor Foundation.Cardinality.setsCardinality.{0})
        $(← object subset))
  -- The same over `Core Sets`, with `Core`'s own instances.
  let coreCard (subset : Term) : TermElabM Term := do
    `(@Prefunctor.obj (Core LeanCategories.Foundation.Mathlib.Sets.{0})
        (@CategoryTheory.coreCategory LeanCategories.Foundation.Mathlib.Sets.{0}
          _).toCategory.toCategoryStruct.toQuiver
        _ _ Foundation.Cardinality.setsCardinality.{0}.toPrefunctor $(← object subset))
  let five ← subset [1, 2, 3, 4, 5]
  let four ← subset [1, 2, 3, 4]
  let denote (k : Nat) : TermElabM Term := do
    `(Foundation.Cardinality.CardinalLiteral.denote $(Syntax.mkNumLit (toString k)))
  expectDecided [
    ← `($union = $five),
    ← `($union ≠ $four),
    ← `($(← card A) = $(← denote 3)),
    ← `($(← prefunctorCard A) = $(← denote 3)),
    ← `($(← coreCard A) = $(← denote 3)),
    ← `($(← card union) = $(← denote 5)),
    ← `($(← prefunctorCard union) = $(← denote 5)),
    ← `($(← coreCard union) = $(← denote 5)),
    ← `($(← card A) ≠ Foundation.Cardinality.CardinalLiteral.denote .aleph0)]
  expectRefused [
    ← `($union = $four),
    ← `($(← card A) = $(← denote 4)),
    ← `($(← prefunctorCard A) = $(← denote 2)),
    ← `($(← card union) = $(← denote 6))]

/-! ## Validation of a registered evaluation -/

/-- Not a proof procedure. -/
meta def probeNotProcedure : Nat := 0

/-- A proof procedure that is not `meta`. -/
def probeNotMeta : Lean.Elab.Tactic.TacticM Unit := pure ()

open Lean Meta in
/- An evaluation is validated as an object's evidence is: a `meta` declaration
`Lean.Elab.Tactic.TacticM Unit` of `lean-categories`. The registered one is accepted; the probes
are refused, on the subset-literal row and on the literal row `lit.cardinals`. Each row is
validated against the registry without itself (one literal form per power object or category). -/
run_meta do
  let state ← semanticState
  let some subset := state.subsetLiterals.find? (·.id.raw == "lit.sets.finite_subsets")
    | throwError "lit.sets.finite_subsets is not registered"
  let some cardinals := state.literals.find? (·.id.raw == "lit.cardinals")
    | throwError "lit.cardinals is not registered"
  let withoutSubset := { state with subsetLiterals := #[] }
  let withoutCardinals := { state with literals := state.literals.filter (·.id != cardinals.id) }
  validateSubsetLiteral withoutSubset subset
  validateLiteral withoutCardinals
    { cardinals with evaluation := some ``Foundation.FiniteSubsetLiterals.evaluation }
  let cases : List (Name × String) :=
    [(``probeNotProcedure, "is not a proof procedure"), (``probeNotMeta, "is not `meta`"),
     (`CasCatalogue.FiniteSubsetLiteralTests.absent, "is not a declaration")]
  for (procedure, fragment) in cases do
    for validate in [validateSubsetLiteral withoutSubset { subset with evaluation := procedure },
        validateLiteral withoutCardinals { cardinals with evaluation := procedure }] do
      let refused ← try validate; pure none
        catch e => pure (some (← e.toMessageData.toString))
      match refused with
      | some message =>
          unless (message.splitOn fragment).length > 1 do
            throwError "evaluation refused for another reason than '{fragment}': {message}"
      | none => throwError "evaluation {procedure} accepted ('{fragment}')"

end CasCatalogue.FiniteSubsetLiteralTests
