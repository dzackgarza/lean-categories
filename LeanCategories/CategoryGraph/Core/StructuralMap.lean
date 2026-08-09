/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryGraph.Core.Normalize

@[expose] public section

/-!
# Structural projection

`project` returns an indexed `FunctorExpr` with normalized endpoints.

Ordinary ancestry is recovered by structural recursion through the category's
definition — not by searching all functors in a graph.

Equations:
* `project(C, C) = id`
* `project(C.A, C) = π_{C.A,C}`
* `project(C.A, H) = π_{C.A,C} ; project(C, H)` when `H` is an ancestor of `C`
* `project(Name(C), H) = project(C, H)` via reference unfolding (registry)
-/

namespace CategoryGraph

/-- Named-expression unfolding: registry resolves a category id to its body. -/
structure NamedExpressionTable where
  bodyOf : CategoryId → Option CategoryExpr

/-- Opaque ports available for projection. -/
structure OpaquePortTable where
  /-- Ports from an opaque source toward a target, keyed by route. -/
  port :
    CategoryId → CategoryId → RouteSelector → Option OpaquePortId

/-- Registered projections from a parameterized category-family application. -/
structure CategoryFamilyPortTable where
  port :
    CategoryFamilyId → Array ParameterExpr → CategoryExpr → RouteSelector → Option OpaquePortId

/-- Typed arities of registered category-family applications. -/
structure CategoryFamilySignatureTable where
  arity : CategoryFamilyId → Option Nat

/-- Classifier ownership + refinement ids for certificate references. -/
structure ProjectionContext where
  hosts : ClassifierHostTable
  aliases : AliasTable
  named : NamedExpressionTable
  opaquePorts : OpaquePortTable
  familyPorts : CategoryFamilyPortTable
  familySignatures : CategoryFamilySignatureTable
  /-- Assign a stable refinement id for `(baseExpr, classifier, route)`. -/
  refinementId : CategoryExpr → ClassifierId → Option RouteId → RefinementId

/-- Equality of category expressions up to the normalizer. -/
def categoryExprEq
    (ctx : ProjectionContext) (a b : CategoryExpr) : Bool :=
  let na := normalizeCategory ctx.hosts ctx.aliases a
  let nb := normalizeCategory ctx.hosts ctx.aliases b
  na.syntacticEq nb

/-- Core structural projection (partial: returns `none` when unreachable). -/
partial def projectNormalized
    (ctx : ProjectionContext) (src tgt : CategoryExpr) (route : RouteSelector) :
    Option (FunctorExpr src tgt) :=
  if categoryExprEq ctx src tgt then
    some (.normalizedIdentity src tgt)
  else
    match src with
    | .refine base clf r =>
        let refinement := RefinementExpr.mk (ctx.refinementId base clf r) base clf r
        let projection := FunctorExpr.baseProjection refinement
        if categoryExprEq ctx base tgt then
          some (.compose projection (.normalizedIdentity base tgt))
        else
          match projectNormalized ctx base tgt route with
          | some rest => some (.compose projection rest)
          | none => none
    | .classifierTotal clf =>
        match ctx.hosts.hostOf clf with
        | none => none
        | some host =>
            let hostE : CategoryExpr := .atom host
            let projection := FunctorExpr.classifierForget clf host
            if categoryExprEq ctx hostE tgt then
              some (.compose projection (.normalizedIdentity hostE tgt))
            else
              match projectNormalized ctx hostE tgt route with
              | some rest => some (.compose projection rest)
              | none => none
    | .atom id =>
        match ctx.named.bodyOf id with
        | some body =>
            if categoryExprEq ctx body (.atom id) then
              match tgt with
              | .atom target =>
                  match ctx.opaquePorts.port id target route with
                  | some port => some (.opaquePort port)
                  | none => none
              | _ => none
            else
              let expansion := FunctorExpr.unfoldAtom id body
              if categoryExprEq ctx body tgt then
                some (.compose expansion (.normalizedIdentity body tgt))
              else
                match projectNormalized ctx body tgt route with
                | some rest => some (.compose expansion rest)
                | none => none
        | none =>
            match tgt with
            | .atom target =>
                match ctx.opaquePorts.port id target route with
                | some port => some (.opaquePort port)
                | none => none
            | _ => none
    | .opaque id =>
        match tgt with
        | .atom target | .opaque target | .reference target =>
            match ctx.opaquePorts.port id target route with
            | some port => some (.opaquePort port)
            | none => none
        | _ => none
    | .reference id =>
        match ctx.named.bodyOf id with
        | some body =>
            let expansion := FunctorExpr.unfoldReference id body
            if categoryExprEq ctx body tgt then
              some (.compose expansion (.normalizedIdentity body tgt))
            else
              match projectNormalized ctx body tgt route with
              | some rest => some (.compose expansion rest)
              | none => none
        | none => none
    | .familyApp family args =>
        match ctx.familySignatures.arity family with
        | some arity =>
            if args.size == arity then
              match ctx.familyPorts.port family args tgt route with
              | some port => some (.opaquePort port)
              | none => none
            else
              none
        | none => none
    | .pullback .. | .constructor .. => none

/-- Compute a typed structural projection between normalized category expressions. -/
def project
    (ctx : ProjectionContext) (src tgt : CategoryExpr) (route : RouteSelector) :
    Option SomeFunctorExpr :=
  let source := normalizeCategory ctx.hosts ctx.aliases src
  let target := normalizeCategory ctx.hosts ctx.aliases tgt
  (projectNormalized ctx source target route).map fun expression =>
    ⟨source, target, expression⟩

end CategoryGraph
