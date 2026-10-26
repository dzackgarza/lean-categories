/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Semantic
public import Lean.Util.CollectAxioms

@[expose] public section

set_option backward.privateInPublic true

/-!
# Checked derivations of published computational families

A plan is an ordinary Lean function whose initial arguments are complete published
families. Applying it to those families must equal the entire target family. Thus
Lean owns the dependent parameters, universes, expression language and correctness;
this catalogue only retains their checked publication and exact prerequisite names.

See `computation-derivations.md` for the source comparison and consumer contract.
This is independent of implementations, installation order and computational costs.
-/

namespace CasCatalogue

open Lean Meta Elab Command

/-- An existing published family, retaining the kind of its mathematical owner.
A method denotes its registered functor family, while retaining the method address.
No equality of carrier types identifies two references. -/
inductive ComputationRef
  | operation (id : OperationId)
  | functor (id : FunctorId)
  | method (id : MethodId)
  | construction (id : ConstructionId)
  | morphism (id : MorphismId)
  deriving DecidableEq, Repr

/-- Identity of one derivation, not an order or a preference among derivations. -/
structure ComputationDerivationId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- A published whole-family derivation. If the prerequisites denote `p₁, …, pₙ`,
the initial arguments of `plan` are `(q₁ : typeOf p₁) → … → (qₙ : typeOf pₙ)`.
Its remaining type, after substituting the actual published families, is the
entire target type `T`; `correctness` proves `plan p₁ … pₙ = target : T`.
The remainder may depend on the slots (for example on a functor's object map).

Each slot is used by the plan. Slots are ordered function arguments; this order
assigns no semantic or executable priority. The target's whole dependent type and
all its universe parameters are fixed before checking the other declarations. -/
structure ComputationDerivationEntry where
  id : ComputationDerivationId
  target : ComputationRef
  prerequisites : Array ComputationRef
  plan : Name
  correctness : Name
  deriving Repr

/-- Resolve an exact published address, without selecting an equal-typed family. -/
def ComputationRef.declaration (reference : ComputationRef)
    (state : SemanticState) : MetaM Name := do
  match reference with
  | .operation id =>
      let some entry := state.operations.find? (·.id == id)
        | throwError "unregistered computation operation {id.raw}"
      return entry.declaration
  | .functor id =>
      let some entry := state.functor? id
        | throwError "unregistered computation functor {id.raw}"
      return entry.declaration
  | .method id =>
      let some entry := state.methods.find? (·.id == id)
        | throwError "unregistered computation method {id.raw}"
      let some functorEntry := state.functor? entry.functor
        | throwError "computation method {id.raw} has an unregistered functor"
      return functorEntry.declaration
  | .construction id =>
      let some entry := state.constructions.find? (·.id == id)
        | throwError "unregistered computation construction {id.raw}"
      return entry.declaration
  | .morphism id =>
      let some entry := state.morphisms.find? (·.id == id)
        | throwError "unregistered computation morphism {id.raw}"
      return entry.declaration

/-- One primitive slot, including its actual universe application and complete
dependent type. These expressions are closed; parameters are retained as binders. -/
structure CheckedComputationPrerequisite where
  reference : ComputationRef
  declaration : Name
  family : Expr
  familyType : Expr

/-- Checked mathematical data for a derivation. `template` is the ordinary Lean
lambda expression retaining the primitive slots, in the order of `prerequisites`.
`plan` is that same declaration applied to the actual published families; it has
type `familyType`, and `correctness` has type `plan = target`.

The target's universes remain rigid parameters. Consumers may instantiate this
entire package, but cannot specialize before validating or infer an operation's
identity from a type, an operand, a returned value, or installed implementations. -/
structure CheckedComputationDerivation where
  entry : ComputationDerivationEntry
  universeParams : List Name
  targetDeclaration : Name
  target : Expr
  familyType : Expr
  prerequisites : Array CheckedComputationPrerequisite
  template : Expr
  plan : Expr
  correctness : Expr

private def requireClosedComputationExpr (id : ComputationDerivationId)
    (label : String) (expression : Expr) : MetaM Unit := do
  if expression.hasFVar || expression.hasLooseBVars || expression.hasExprMVar ||
      expression.hasLevelMVar then
    throwError "computation derivation {id.raw}: {label} has unresolved or free parameters"

private def requireCheckedComputationDeclaration (id : ComputationDerivationId)
    (name : Name) : MetaM Unit := do
  let info ← getConstInfo name
  if info.isUnsafe then
    throwError "computation derivation {id.raw}: {name} is unsafe"
  -- This is the existing release axiom budget (Tools/AxiomAudit.lean), without
  -- importing the root aggregate into the registry that it imports.
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  for assumption in ← collectAxioms name do
    unless permitted.contains assumption do
      throwError "computation derivation {id.raw}: {name} depends on {assumption}"

/-- Inspect term occurrences after administrative reduction. Binder types and
proofs do not create computational prerequisites. The plan remains a Lean term;
this traversal introduces no second expression language. -/
private partial def computationUsesSlot (slot : FVarId) (expression : Expr) : MetaM Bool := do
  let expression := expression.headBeta
  if ← isType expression then return false
  if ← isProof expression then return false
  match expression with
  | .fvar id => return id == slot
  | .app function argument =>
      computationUsesSlot slot function <||> computationUsesSlot slot argument
  | .lam .. => lambdaTelescope expression fun _ body => computationUsesSlot slot body
  | .letE .. => computationUsesSlot slot (← zetaReduce expression)
  | .mdata _ body => computationUsesSlot slot body
  | .proj _ _ value => computationUsesSlot slot value
  | _ => return false

/-- Validate a derivation against its actual published declarations. The target is
made at rigid universe parameters first. Only the plan, prerequisite and proof
universe applications are inferred; an undetermined application is rejected.

No graph acyclicity condition occurs here: mutually dependent correct identities
remain mathematics. A consumer obtains executable availability only from a finite
derivation tree whose leaves have computations. -/
def validateComputationDerivation (state : SemanticState)
    (entry : ComputationDerivationEntry) : MetaM CheckedComputationDerivation := do
  if entry.id.raw.isEmpty then
    throwError "a computation derivation has an empty identity"
  let targetDeclaration ← entry.target.declaration state
  let targetInfo ← getConstInfo targetDeclaration
  let target := mkConst targetDeclaration (targetInfo.levelParams.map Level.param)
  let familyType ← inferType target
  requireCheckedComputationDeclaration entry.id entry.plan
  requireCheckedComputationDeclaration entry.id entry.correctness
  let .defnInfo planInfo ← getConstInfo entry.plan
    | throwError "computation derivation {entry.id.raw}: its plan must be a transparent definition"
  let planConstant ← mkConstWithFreshMVarLevels entry.plan
  let mut planType ← inferType planConstant
  let mut prerequisites : Array CheckedComputationPrerequisite := #[]
  for reference in entry.prerequisites do
    let declaration ← reference.declaration state
    let family ← mkConstWithFreshMVarLevels declaration
    let actualType ← inferType family
    let .forallE _ slotType body _ ← whnf planType
      | throwError "computation derivation {entry.id.raw}: missing prerequisite slot"
    unless ← withTransparency .all <| isDefEq slotType actualType do
      throwError "computation derivation {entry.id.raw}: prerequisite {repr reference} \
        does not have its entire published family type"
    prerequisites := prerequisites.push { reference, declaration, family, familyType := actualType }
    planType := body.instantiate1 family
  unless ← withTransparency .all <| isDefEq planType familyType do
    throwError "computation derivation {entry.id.raw}: the plan does not return the entire \
      target family with all its dependent parameters and universes"
  let plan := mkAppN planConstant (prerequisites.map (·.family))
  let expected ← mkEq plan target
  let correctness ← mkConstWithFreshMVarLevels entry.correctness
  unless ← withTransparency .all <| isDefEq (← inferType correctness) expected do
    throwError "computation derivation {entry.id.raw}: correctness does not prove equality \
      of the entire plan and target families"
  let planConstant ← instantiateMVars planConstant
  let template := planInfo.value.instantiateLevelParams planInfo.levelParams
    planConstant.constLevels!
  let template ← instantiateMVars template
  let plan ← instantiateMVars plan
  let correctness ← instantiateMVars correctness
  prerequisites ← prerequisites.mapM fun prerequisite => do
    return { prerequisite with
      family := ← instantiateMVars prerequisite.family
      familyType := ← instantiateMVars prerequisite.familyType }
  for (label, expression) in #[
      ("target", target), ("target type", familyType), ("template", template),
      ("plan", plan), ("correctness", correctness)] do
    requireClosedComputationExpr entry.id label expression
  for prerequisite in prerequisites do
    requireClosedComputationExpr entry.id "prerequisite" prerequisite.family
    requireClosedComputationExpr entry.id "prerequisite type" prerequisite.familyType
  -- Opening only the primitive prefix preserves the complete target telescope.
  -- Occurrence is checked before substituting the published families, so two
  -- equal definitions cannot obscure which slot supplies a call.
  forallBoundedTelescope (← inferType planConstant) (some prerequisites.size)
      fun slots _ => do
    unless slots.size == prerequisites.size do
      throwError "computation derivation {entry.id.raw}: missing prerequisite slot"
    let openPlan ← zetaReduce (mkAppN template slots).headBeta
    for slot in slots do
      unless ← computationUsesSlot slot.fvarId! openPlan do
        throwError "computation derivation {entry.id.raw}: unused prerequisite slot"
  check plan
  check correctness
  return {
    entry := entry
    universeParams := targetInfo.levelParams
    targetDeclaration := targetDeclaration
    target := target
    familyType := familyType
    prerequisites := prerequisites
    template := template
    plan := plan
    correctness := correctness }

private initialize computationDerivationExt : SimplePersistentEnvExtension
    ComputationDerivationEntry (Array ComputationDerivationEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

/-- All published alternatives. Array position does not choose a meaning or a plan. -/
def computationDerivations : CoreM (Array ComputationDerivationEntry) :=
  do
    let entries := computationDerivationExt.getState (← getEnv)
    let mut seen : Array ComputationDerivationId := #[]
    for entry in entries do
      if seen.contains entry.id then
        throwError "duplicate computation derivation identity {entry.id.raw}"
      seen := seen.push entry.id
    return entries

/-- Resolve every derivation of this exact published target. Metadata is not
returned as mathematical evidence: each result retains the checked family proof. -/
def checkedComputationDerivations (target : ComputationRef) :
    MetaM (Array CheckedComputationDerivation) := do
  let state ← semanticState
  let entries ← computationDerivations
  (entries.filter (·.target == target)).mapM (validateComputationDerivation state)

/-- The only write path. It is governed by the existing semantic-author boundary. -/
def addComputationDerivationChecked (entry : ComputationDerivationEntry) : MetaM Unit := do
  let module := (← getEnv).mainModule
  unless semanticAuthorRoots.contains module.getRoot do
    throwError "computation derivation {entry.id.raw}: {module} is not a lean-categories module"
  if (← computationDerivations).any (·.id == entry.id) then
    throwError "duplicate computation derivation identity {entry.id.raw}"
  let _ ← validateComputationDerivation (← semanticState) entry
  modifyEnv (computationDerivationExt.addEntry · entry)

/-- Publish a checked whole-family computational derivation. -/
syntax (name := normalizedComputationDerivation)
  "normalized_computation_derivation " term : command

elab_rules : command
  | `(normalized_computation_derivation $entry) => do
      let command ← `(run_cmd liftTermElabM do addComputationDerivationChecked $entry)
      elabCommand command

end CasCatalogue
