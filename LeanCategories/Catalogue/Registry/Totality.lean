/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Entry
public import Mathlib.Algebra.Group.Defs

@[expose] public section

/-!
# The totality gate (LC-14, LC-16)

An operation is a total morphism out of its domain object, and exists only where its structure
exists. A row whose declaration is built from any of the following is refused when it is
registered, so an ill-defined specification cannot enter the catalogue:

* a partial or optional result: `Option`, `Part`, `PFun` (LC-14);
* a total convention off the domain: `Ring.inverse`, `Matrix.nonsing_inv`, `Matrix.inv` (LC-14);
* an inverse or a division `⁻¹`, `/` on a type that is not a group (LC-16). Inverses are group
  structure: of `Mˣ`, `Aut(X)`, `GLₙ(K)`, `K^×`, never of a monoid, of `End(X)`, of `Matₙ(K)`, or
  of a field, whose `x⁻¹` and `x / y` are Lean's total conventions at `0`.

The check reads the declaration and every definition of this repository (`CasCatalogue.*`,
`LeanCategories.*`) that it is built from, and it does not read Mathlib's internals. It is a gate,
not a proof. It refuses the encodings that the catalogue has used for partiality; it does not
certify that a row is well defined.
-/

open Lean Meta

namespace CasCatalogue

/-- Constants whose use makes a declaration partial, or total only by a convention off its
domain. -/
def partialityConstants : List Name :=
  [`Option, `Part, `PFun, `Ring.inverse, `Matrix.nonsing_inv, `Matrix.inv]

/-- The roots of this repository's definitions. -/
def totalityProjectRoots : List Name := [`CasCatalogue, `LeanCategories]

/-- `root` with every definition of this repository that it is built from. -/
def totalityClosure (root : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut seen : Array Name := #[root]
  let mut frontier : Array Name := #[root]
  while !frontier.isEmpty do
    let mut next := #[]
    for n in frontier do
      let some info := env.find? n | continue
      let used := info.type.getUsedConstants ++ (info.value?.map (·.getUsedConstants)).getD #[]
      for c in used do
        if totalityProjectRoots.contains c.getRoot && !seen.contains c then
          if let some (.defnInfo _) := env.find? c then
            seen := seen.push c
            next := next.push c
    frontier := next
  return seen

/-- The violations of LC-14 and LC-16 in the definition `n` itself. -/
def totalityViolationsAt (n : Name) : MetaM (Array MessageData) := do
  let some info := (← getEnv).find? n | return #[]
  let mut out : Array MessageData := #[]
  for e in #[info.type] ++ info.value?.toArray do
    for c in partialityConstants do
      if e.getUsedConstants.contains c then
        out := out.push m!"{n} is built from {c}: a partial or conventional result (LC-14)"
    let found ← IO.mkRef (#[] : Array MessageData)
    let _ ← Meta.transform e (pre := fun x => do
      if x.isAppOfArity ``Inv.inv 3 || x.isAppOfArity ``HDiv.hDiv 6 then
        let α := x.getAppArgs[0]!
        unless α.hasLooseBVars do
          let group ← try some <$> mkAppM ``Group #[α] catch _ => pure none
          let isGroup ← match group with
            | some g => pure (← synthInstance? g).isSome
            | none => pure false
          unless isGroup do
            found.modify (·.push m!"{n} applies {x.getAppFn.constName!} on {α}, which is not a \
              group: inverses and division exist on units and automorphisms only (LC-16)")
      return .continue)
    out := out ++ (← found.get)
  return out

/-- The violations of LC-14 and LC-16 in `declaration` and everything of this repository it is
built from. -/
def totalityViolations (declaration : Name) : MetaM (Array MessageData) := do
  let mut out := #[]
  for n in ← totalityClosure declaration do
    out := out ++ (← totalityViolationsAt n)
  return out

/-- Refuse the declarations of a row that violate LC-14 or LC-16. -/
def ensureTotal (row : String) (declarations : Array Name) : MetaM Unit := do
  let mut out : Array MessageData := #[]
  for declaration in declarations do
    out := out ++ (← totalityViolations declaration)
  unless out.isEmpty do
    let reasons := MessageData.joinSep out.toList "\n"
    throwError "registry row {row} is refused by the totality gate:{indentD reasons}\nAn \
      operation is a total morphism out of its domain object, and exists only where its \
      structure exists (CONTRIBUTING LC-14, LC-16)."

end CasCatalogue
