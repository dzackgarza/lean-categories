/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Entry
public import Lean.Data.Json

@[expose] public section

/-!
# Shared JSON serialization for registry snapshots

The exporter constructs `Lean.Json` values directly.  In particular, symbolic
expressions and parameter-family metadata are structured JSON rather than
rendered `repr` text.
-/

namespace LeanCategories.Tools

open Lean
open LeanCategories

def object (fields : List (String × Json)) : Json := Json.mkObj fields

def parameterJson : ParameterExpr → Json
  | .variable id => object [("tag", "variable"), ("id", id.raw)]
  | .apply operation argument =>
      object [
        ("tag", "apply"),
        ("operation", operation.raw),
        ("argument", parameterJson argument),
]
  | .apply2 operation left right =>
      object [
        ("tag", "apply2"),
        ("operation", operation.raw),
        ("left", parameterJson left),
        ("right", parameterJson right),
]
  | .apply3 operation first second third =>
      object [
        ("tag", "apply3"),
        ("operation", operation.raw),
        ("first", parameterJson first),
        ("second", parameterJson second),
        ("third", parameterJson third),
]

def categoryExprJson : CategoryExpr → Json
  | .atom id => object [("tag", "atom"), ("id", id.raw)]
  | .familyApp family args =>
      object [
        ("tag", "familyApp"),
        ("family", family.raw),
        ("args", .arr (args.map parameterJson)),
]
  | .classifierTotal classifier =>
      object [("tag", "classifierTotal"), ("classifier", classifier.raw)]
  | .refine base classifier route =>
      object [
        ("tag", "refine"),
        ("base", categoryExprJson base),
        ("classifier", classifier.raw),
        ("route", match route with | some r => r.raw | none => Json.null),
]
  | .opaque id => object [("tag", "opaque"), ("id", id.raw)]

def parameterKindJson (kind : ParameterKindId) : Json := kind.raw

def varianceJson (variance : VarianceId) : Json := variance.raw

def categoryFamilySchemaJson : CategoryFamilySchema → Json
  | .ring => "ring"
  | .commRing => "commRing"
  | .commRingModule => "commRingModule"

def functorExprJson {source target : CategoryExpr} : FunctorExpr source target → Json
  | .identity category => object [("tag", "identity"), ("category", categoryExprJson category)]
  | .atomic id => object [("tag", "atomic"), ("id", id.raw)]
  | .classifierForget classifier host =>
      object [("tag", "classifierForget"), ("classifier", classifier.raw),
        ("host", categoryExprJson host)]
  | .opaquePort id => object [("tag", "opaquePort"), ("id", id.raw)]

def categoryJson (e : NamedCategoryEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("canonicalName", e.canonicalName),
    ("declaration", e.declaration.toString),
    ("realization", e.realization.toString),
    ("refinementRealization", match e.refinementRealization with
      | some realization => realization.toString
      | none => ""),
    ("expression", categoryExprJson e.expression),
]

def categoryFamilyJson (e : CategoryFamilyEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("canonicalName", e.canonicalName),
    ("schema", categoryFamilySchemaJson e.schema),
    ("realization", e.realization.toString),
    ("transport", e.transport.toString),
    ("parameters", Json.arr <| e.schema.parameterMetadata.map fun parameter => object [
      ("variables", Json.arr <| parameter.ids.toArray.map (·.raw)),
      ("name", parameter.name),
      ("kind", parameterKindJson parameter.kind),
      ("dependency", match parameter.dependency with
        | some index => Json.num index
        | none => Json.null),
]),
    ("variance", varianceJson e.transportSemantics.variance),
]

def aliasJson (e : AliasEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("spelling", e.spelling),
    ("aliasOf", e.aliasOf.raw),
    ("declaration", e.declaration.toString),
    ("realization", e.realization.toString),
]

def classifierJson (e : ClassifierEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("canonicalName", e.canonicalName),
    ("host", categoryExprJson e.host),
    ("declaration", e.declaration.toString),
    ("realization", e.realization.toString),
]

def functorJson (e : FunctorEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("canonicalName", e.canonicalName),
    ("source", categoryExprJson e.source),
    ("target", categoryExprJson e.target),
    ("declaration", e.declaration.toString),
    ("realization", e.realization.toString),
    ("expression", functorExprJson e.expression),
]

def opaqueJson (e : OpaqueCategoryEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("declaration", e.declaration.toString),
    ("realization", e.realization.toString),
    ("reason", e.reason),
    ("ports", .arr <| e.ports.map fun p => object [
      ("id", p.id.raw),
      ("source", categoryExprJson p.source),
      ("target", categoryExprJson p.target),
      ("declaration", p.declaration.toString),
      ("realization", p.realization.toString),
      ("provenance", p.provenance),
]),
]

/-- Deterministic manifest JSON from a registry snapshot. -/
def snapshotManifestJson (snap : RegistrySnapshot) : Json :=
  let cats := snap.categories.qsort (fun a b => a.id.raw < b.id.raw)
  let families := snap.categoryFamilies.qsort (fun a b => a.id.raw < b.id.raw)
  let clfs := snap.classifiers.qsort (fun a b => a.id.raw < b.id.raw)
  let functors := snap.functors.qsort (fun a b => a.id.raw < b.id.raw)
  let als := snap.aliases.qsort (fun a b => a.id.raw < b.id.raw)
  let ops := snap.opaqueCategories.qsort (fun a b => a.id.raw < b.id.raw)
  object [
    ("schemaVersion", snap.schemaVersion),
    ("universes", object []),
    ("categories", .arr (cats.map categoryJson)),
    ("classifiers", .arr (clfs.map classifierJson)),
    ("functors", .arr (functors.map functorJson)),
    ("aliases", .arr (als.map aliasJson)),
    ("opaqueCategories", .arr (ops.map opaqueJson)),
    ("categoryFamilies", .arr (families.map categoryFamilyJson)),
    ("namedExpressions", .arr #[]),
    ("structuralPorts", .arr #[]),
    ("source", "lean-registry"),
]

/-- Serialize a snapshot using Lean's JSON printer. -/
def snapshotManifestString (snap : RegistrySnapshot) : String :=
  (snapshotManifestJson snap).compress

end LeanCategories.Tools
