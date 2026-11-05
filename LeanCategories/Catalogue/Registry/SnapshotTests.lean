/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue
public meta import LeanCategories.Catalogue

@[expose] public section

/-!
# The registry snapshot contract (#49)

Checks the three things a downstream consumer relies on: a stable ID resolves to the checked
row and its Lean declaration; the fold accepts rows it has not seen; and the fold is fail-loud
on a re-registered ID or an unresolved reference, so a consumer cannot silently overwrite
checked meaning or invent a dangling route.

Every reference probe folds a **fresh** row onto the full snapshot, and that row differs from a
checked row only in the one field under test: a freshly identified copy keeps all of its other
references resolvable, so a refusal can only come from the mutated field. The refusal is also
required to *be* a reference refusal. A probe built from an isolated row, or one reusing a
checked ID, would be refused for the wrong reason and would prove nothing.
-/

namespace CasCatalogue.RegistrySnapshotTests

open CasCatalogue

open Lean Meta in
run_meta do
  let snap ← RegistrySnapshot.snapshot
  unless snap.entries.size > 0 do
    throwError "the registry snapshot is empty; a consumer would read no rows"
  -- Stage 1: registry rows resolve by stable ID, and the row names a real declaration.
  let some names := snap.declarationNames? "cat.sets"
    | throwError "the snapshot does not resolve the stable ID cat.sets"
  unless names.size > 0 do
    throwError "cat.sets names no declaration"
  for name in names do
    unless (← getEnv).contains name do
      throwError "cat.sets names the absent declaration {name}"
  let some functorNames := snap.declarationNames? "fun.sets.list"
    | throwError "the snapshot does not resolve the stable ID fun.sets.list"
  unless functorNames.size > 0 do
    throwError "fun.sets.list names no declaration"
  -- A consumer resolves by ID alone, without a generated mapping or a seed file.
  unless (snap.idsWithPrefix "fun.").size > 0 do
    throwError "the snapshot exposes no functor rows by prefix"
  -- An empty fold is accepted: the snapshot is internally consistent.
  match snap.validateDerived #[] with
  | .ok () => pure ()
  | .error message => throwError "the checked snapshot fails its own fold check: {message}"
  -- Fail-loud: a derived row may not re-register a checked stable ID.
  let some checked := snap.findEntry? "cat.sets"
    | throwError "the snapshot does not expose cat.sets"
  match snap.validateDerived #[checked] with
  | .ok () => throwError "the fold accepted a re-registration of cat.sets"
  | .error _ => pure ()
  -- The fold must refuse `label`, and must refuse it as a reference failure.
  let expectReferenceRefusal (label : String) (entry : SemanticEntry) : MetaM Unit := do
    match snap.validateDerived #[entry] with
    | .ok () => throwError "the fold accepted {label}"
    | .error message =>
      unless message.contains "unresolved" || message.contains "unregistered" do
        throwError "the fold refused {label} for an unrelated reason: {message}"
  -- Rows of each kind under test, freshly identified and otherwise copied from a checked row.
  let some (.cell cell) := snap.findEntry? "cell.sets.list.unit"
    | throwError "cell.sets.list.unit is not a cell row"
  let some inc := snap.entries.findSome? (fun e => match e with
      | .inclusion x => some x
      | _ => none)
    | throwError "no inclusion row to probe"
  let some power := snap.entries.findSome? (fun e => match e with
      | .powerObject x => some x
      | _ => none)
    | throwError "no power-object row to probe"
  let some operation := snap.entries.findSome? (fun e => match e with
      | .operation x => some x
      | _ => none)
    | throwError "no operation row to probe"
  let some object := snap.entries.findSome? (fun e => match e with
      | .object x => some x
      | _ => none)
    | throwError "no object row to probe"
  let some subset := snap.entries.findSome? (fun e => match e with
      | .subsetLiteral x => some x
      | _ => none)
    | throwError "no subset-literal row to probe"
  let some presentation := snap.entries.findSome? (fun e => match e with
      | .presentation x => some x
      | _ => none)
    | throwError "no presentation row to probe"
  let some numeral := snap.entries.findSome? (fun e => match e with
      | .numeral x => some x
      | _ => none)
    | throwError "no numeral row to probe"
  let some morphism := snap.entries.findSome? (fun e => match e with
      | .morphism x => some x
      | _ => none)
    | throwError "no morphism row to probe"
  let some binder := snap.entries.findSome? (fun e => match e with
      | .binder x => some x
      | _ => none)
    | throwError "no binder row to probe"
  let some method := snap.entries.findSome? (fun e => match e with
      | .method x => some x
      | _ => none)
    | throwError "no method row to probe"
  let some limit := snap.entries.findSome? (fun e => match e with
      | .limit x => some x
      | _ => none)
    | throwError "no limit row to probe"
  -- One builder per mutated field: every other reference stays that of the checked row.
  let cellLeft (id : String) (left : Array EdgeRef) : SemanticEntry :=
    .cell { cell with id := ⟨id⟩, left := left }
  let cellSource (id : String) (source : CategoryExpr) : SemanticEntry :=
    .cell { cell with id := ⟨id⟩, source := source }
  let inclSuper (id : String) (super : ObjectId) : SemanticEntry :=
    .inclusion { inc with id := ⟨id⟩, super := super }
  let inclSub (id : String) (sub : ObjectId) : SemanticEntry :=
    .inclusion { inc with id := ⟨id⟩, sub := sub }
  let inclCat (id : String) (cat : CategoryId) : SemanticEntry :=
    .inclusion { inc with id := ⟨id⟩, category := cat }
  let powerObject (id : String) (obj : ObjectId) : SemanticEntry :=
    .powerObject { power with id := ⟨id⟩, object := obj }
  let powerOmega (id : String) (omega : ObjectId) : SemanticEntry :=
    .powerObject { power with id := ⟨id⟩, omega := omega }
  let opCat (id : String) (cat : CategoryId) : SemanticEntry :=
    .operation { operation with id := ⟨id⟩, category := cat }
  let opRefines (id : String) (refines : OperationRefinement) : SemanticEntry :=
    .operation { operation with id := ⟨id⟩, refines := some refines }
  let objCat (id : String) (cat : CategoryId) : SemanticEntry :=
    .object { object with id := ⟨id⟩, category := cat }
  let objRefines (id : String) (refines : ObjectRefinement) : SemanticEntry :=
    .object { object with id := ⟨id⟩, refines := some refines }
  let objPres (id : String) (pres : ObjectFunctorPresentation) : SemanticEntry :=
    .object { object with id := ⟨id⟩, functorPresentation := some pres }
  let subsetPower (id : String) (pow : PowerObjectId) : SemanticEntry :=
    .subsetLiteral { subset with id := ⟨id⟩, powerObject := pow }
  let presSource (id : String) (src : ObjectId) : SemanticEntry :=
    .presentation { presentation with id := ⟨id⟩, source := src }
  let presTarget (id : String) (tgt : ObjectId) : SemanticEntry :=
    .presentation { presentation with id := ⟨id⟩, target := tgt }
  let numeralOver (id : String) (over : CategoryId) : SemanticEntry :=
    .numeral { numeral with id := ⟨id⟩, over := some over }
  let morCat (id : String) (cat : CategoryId) : SemanticEntry :=
    .morphism { morphism with id := ⟨id⟩, category := cat }
  let binderCat (id : String) (cat : CategoryId) : SemanticEntry :=
    .binder { binder with id := ⟨id⟩, category := cat }
  let methodOwner (id : String) (owner : CategoryExpr) : SemanticEntry :=
    .method { method with id := ⟨id⟩, owner := owner }
  let limitCat (id : String) (cat : CategoryId) : SemanticEntry :=
    .limit { limit with id := ⟨id⟩, category := cat }
  let missingCat : CategoryId := ⟨"cat.missing"⟩
  let missingObj : ObjectId := ⟨"obj.missing"⟩
  let missingFun : FunctorId := ⟨"fun.missing"⟩
  -- Cells: a route step is a functor reference; the endpoints are category references.
  expectReferenceRefusal "a cell row naming an unregistered functor"
    (cellLeft "p.cell.left" #[.functor missingFun])
  expectReferenceRefusal "a cell row with an unregistered source category"
    (cellSource "p.cell.src" (.atom missingCat))
  -- Inclusions own their category and both endpoints.
  expectReferenceRefusal "an inclusion over an unregistered superobject"
    (inclSuper "p.incl.super" missingObj)
  expectReferenceRefusal "an inclusion over an unregistered subobject"
    (inclSub "p.incl.sub" missingObj)
  expectReferenceRefusal "an inclusion in an unregistered category"
    (inclCat "p.incl.cat" missingCat)
  -- Power objects own their object and their truth object.
  expectReferenceRefusal "a power object over an unregistered object"
    (powerObject "p.power.obj" missingObj)
  expectReferenceRefusal "a power object over an unregistered truth object"
    (powerOmega "p.power.omega" missingObj)
  -- Operations own their category, refined operation and refinement route.
  expectReferenceRefusal "an operation in an unregistered category"
    (opCat "p.op.cat" missingCat)
  let opRefinesTo : OperationRefinement :=
    { base := ⟨"op.missing"⟩, route := #[], identification := operation.declaration }
  expectReferenceRefusal "an operation refining an unregistered operation"
    (opRefines "p.op.refines" opRefinesTo)
  let opRoute : OperationRefinement :=
    { base := operation.id, route := #[.functor missingFun],
      identification := operation.declaration }
  expectReferenceRefusal "an operation whose refinement route has a missing edge"
    (opRefines "p.op.route" opRoute)
  -- Objects own their category, refined base, refinement route, and functorial presentation.
  expectReferenceRefusal "an object in an unregistered category"
    (objCat "p.obj.cat" missingCat)
  let objRefinesTo : ObjectRefinement :=
    { base := missingObj, route := #[], identification := object.declaration }
  expectReferenceRefusal "an object refining an unregistered base"
    (objRefines "p.obj.refines" objRefinesTo)
  let objRoute : ObjectRefinement :=
    { base := object.id, route := #[.functor missingFun],
      identification := object.declaration }
  expectReferenceRefusal "an object whose refinement route has a missing edge"
    (objRefines "p.obj.route" objRoute)
  -- `ObjectEntry.functorPresentation` carries a functor ID *and* a route of edges; the
  -- persisted-state gate covers neither, which is the defect these two probes pin down.
  let presentationOf (functor : FunctorId) (route : Array EdgeRef) : ObjectFunctorPresentation :=
    { functor := functor, argument := object.declaration, route := route,
      identification := object.declaration }
  expectReferenceRefusal "an object presented by an unregistered functor"
    (objPres "p.obj.pres.fun" (presentationOf missingFun #[]))
  expectReferenceRefusal "an object whose presentation route has a missing edge"
    (objPres "p.obj.pres.rt" (presentationOf ⟨"fun.sets.list"⟩ #[.functor missingFun]))
  -- Subset literals, presentations, numerals, morphisms, binders, methods and limits.
  expectReferenceRefusal "a subset literal over an unregistered power object"
    (subsetPower "p.subset.power" ⟨"pow.missing"⟩)
  expectReferenceRefusal "a presentation over an unregistered source object"
    (presSource "p.pres.src" missingObj)
  expectReferenceRefusal "a presentation over an unregistered target object"
    (presTarget "p.pres.tgt" missingObj)
  expectReferenceRefusal "a numeral over an unregistered category"
    (numeralOver "p.num.over" missingCat)
  expectReferenceRefusal "a morphism in an unregistered category"
    (morCat "p.mor.cat" missingCat)
  expectReferenceRefusal "a binder in an unregistered category"
    (binderCat "p.binder.cat" missingCat)
  expectReferenceRefusal "a method owned by an unregistered category"
    (methodOwner "p.method.owner" (.atom missingCat))
  expectReferenceRefusal "a limit in an unregistered category"
    (limitCat "p.limit.cat" missingCat)
  -- A nonempty derived fold whose references all resolve is accepted: the check is reference
  -- completeness, not a blanket refusal of consumer rows.
  let derivedRow : MorphismEntry :=
    { id := ⟨"mor.sets.snapshot_probe"⟩, category := ⟨"cat.sets"⟩,
      name := "snapshot_probe", declaration := `id }
  let derived : SemanticEntry := .morphism derivedRow
  match snap.validateDerived #[derived] with
  | .ok () => pure ()
  | .error message => throwError "the fold refused a well-referenced derived row: {message}"
  -- Two derived rows with the same stable ID are refused, even though neither is in the
  -- snapshot: the fold is fail-loud within itself as well as against the registry.
  match snap.validateDerived #[derived, derived] with
  | .ok () => throwError "the fold accepted two derived rows with the same stable ID"
  | .error _ => pure ()

end CasCatalogue.RegistrySnapshotTests
