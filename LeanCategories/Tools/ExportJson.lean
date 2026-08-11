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
  | .pullback left right over =>
      object [
        ("tag", "pullback"),
        ("left", left.raw),
        ("right", right.raw),
        ("over", categoryExprJson over),
      ]
  | .constructor constructor args =>
      object [
        ("tag", "constructor"),
        ("constructor", constructor.raw),
        ("args", .arr (args.map categoryExprJson)),
      ]
  | .opaque id => object [("tag", "opaque"), ("id", id.raw)]
  | .reference id => object [("tag", "reference"), ("id", id.raw)]

def originJson : CategoryOrigin → Json
  | .root => "root"
  | .atomicClassifierTotal => "atomicClassifierTotal"
  | .derivedNamed => "derivedNamed"
  | .constructorValue => "constructorValue"
  | .opaqueCategory => "opaqueCategory"
  | .alias => "alias"

def visibilityJson : Visibility → Json
  | .present => "present"
  | .semanticOnly => "semanticOnly"
  | .presentationHidden => "presentationHidden"

def parameterKindJson (kind : ParameterKindId) : Json := kind.raw

def varianceJson (variance : VarianceId) : Json := variance.raw

def functorRoleJson : FunctorRole → Json
  | .generatedStructural => "generatedStructural"
  | .opaqueStructuralPort => "opaqueStructuralPort"
  | .theoremBacked => "theoremBacked"
  | .finiteLimit => "finiteLimit"
  | .constructorAction => "constructorAction"
  | .presentationOnly => "presentationOnly"

def admissibilityJson : StructuralAdmissibility → Json
  | .generated => "generated"
  | .declared => "declared"
  | .excluded => "excluded"

def functorExprJson {source target : CategoryExpr} : FunctorExpr source target → Json
  | .identity category => object [("tag", "identity"), ("category", categoryExprJson category)]
  | .normalizedIdentity source target =>
      object [("tag", "normalizedIdentity"), ("source", categoryExprJson source),
        ("target", categoryExprJson target)]
  | .named id => object [("tag", "named"), ("id", id.raw)]
  | .baseProjection (.mk id _ _ _) => object [("tag", "baseProjection"), ("id", id.raw)]
  | .classifierProjection (.mk id _ _ _) =>
      object [("tag", "classifierProjection"), ("id", id.raw)]
  | .classifierForget classifier host =>
      object [("tag", "classifierForget"), ("classifier", classifier.raw),
        ("host", host.raw)]
  | .unfoldAtom id body =>
      object [("tag", "unfoldAtom"), ("id", id.raw), ("body", categoryExprJson body)]
  | .unfoldReference id body =>
      object [("tag", "unfoldReference"), ("id", id.raw),
        ("body", categoryExprJson body)]
  | .opaquePort id => object [("tag", "opaquePort"), ("id", id.raw)]
  | .theoremInclusion id => object [("tag", "theoremInclusion"), ("id", id.raw)]
  | .finiteLimitLift id => object [("tag", "finiteLimitLift"), ("id", id.raw)]
  | .constructorMap id => object [("tag", "constructorMap"), ("id", id.raw)]
  | .compose first second =>
      object [("tag", "compose"), ("first", functorExprJson first),
        ("second", functorExprJson second)]

def categoryJson (e : NamedCategoryEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("canonicalName", e.canonicalName),
    ("declaration", e.declaration.toString),
    ("realization", e.realization.toString),
    ("origin", originJson e.origin),
    ("visibility", visibilityJson e.visibility),
    ("expression", categoryExprJson e.expression),
  ]

def categoryFamilyJson (e : CategoryFamilyEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("canonicalName", e.canonicalName),
    ("realization", e.realization.toString),
    ("parameters", Json.arr <| e.parameters.map fun parameter => object [
      ("name", parameter.name),
      ("kind", parameterKindJson parameter.kind),
    ]),
    ("variance", varianceJson e.variance),
  ]

def aliasJson (e : AliasEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("spelling", e.spelling),
    ("aliasOf", e.aliasOf.raw),
    ("declaration", e.declaration.toString),
  ]

def classifierJson (e : ClassifierEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("canonicalName", e.canonicalName),
    ("host", categoryExprJson e.host),
    ("declaration", e.declaration.toString),
    ("realization", e.realization.toString),
    ("visibility", visibilityJson e.visibility),
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
    ("role", functorRoleJson e.role),
    ("admissibility", admissibilityJson e.admissibility),
    ("port", match e.port with | some port => port.raw | none => Json.null),
    ("origin", e.origin),
    ("coherenceClass", match e.coherenceClass with | some id => id.raw | none => Json.null),
    ("preferredPresentation", e.preferredPresentation),
  ]

def constructorJson (e : ConstructorEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("canonicalName", e.canonicalName),
    ("declaration", e.declaration.toString),
    ("sourcePosition", e.sourcePosition),
  ]

def finiteLimitConeJson (e : FiniteLimitConeEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("apex", categoryExprJson e.apex),
    ("declaration", e.declaration.toString),
    ("sourcePosition", e.sourcePosition),
  ]

def coherenceJson (e : CoherenceEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("source", e.source.raw),
    ("target", e.target.raw),
    ("declaration", e.declaration.toString),
    ("sourcePosition", e.sourcePosition),
  ]

def theoremInclusionJson (e : TheoremInclusionEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("source", categoryExprJson e.source),
    ("target", categoryExprJson e.target),
    ("declaration", e.declaration.toString),
    ("sourcePosition", e.sourcePosition),
  ]

def presentationJson (e : PresentationMetadataEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("category", e.category.raw),
    ("declaration", e.declaration.toString),
    ("visibility", visibilityJson e.visibility),
    ("sourcePosition", e.sourcePosition),
  ]

def opaqueJson (e : OpaqueCategoryEntry) : Json :=
  object [
    ("id", e.id.raw),
    ("declaration", e.declaration.toString),
    ("visibility", visibilityJson e.visibility),
    ("reason", e.reason),
    ("ports", .arr <| e.ports.map fun p => object [
      ("id", p.id.raw),
      ("source", p.source.raw),
      ("target", p.target.raw),
      ("role", p.role.raw),
      ("declaration", p.declaration.toString),
      ("provenance", p.provenance),
    ]),
  ]

/-- Deterministic manifest JSON from a registry snapshot. -/
def snapshotManifestJson (snap : RegistrySnapshot) : Json :=
  let cats := snap.categories.qsort (fun a b => a.id.raw < b.id.raw)
  let families := snap.categoryFamilies.qsort (fun a b => a.id.raw < b.id.raw)
  let clfs := snap.classifiers.qsort (fun a b => a.id.raw < b.id.raw)
  let functors := snap.functors.qsort (fun a b => a.id.raw < b.id.raw)
  let constructors := snap.constructors.qsort (fun a b => a.id.raw < b.id.raw)
  let cones := snap.finiteLimitCones.qsort (fun a b => a.id.raw < b.id.raw)
  let coherences := snap.coherences.qsort (fun a b => a.id.raw < b.id.raw)
  let inclusions := snap.theoremInclusions.qsort (fun a b => a.id.raw < b.id.raw)
  let als := snap.aliases.qsort (fun a b => a.id.raw < b.id.raw)
  let ops := snap.opaqueCategories.qsort (fun a b => a.id.raw < b.id.raw)
  let presentations := snap.presentations.qsort (fun a b => a.id.raw < b.id.raw)
  object [
    ("schemaVersion", snap.schemaVersion),
    ("universes", object []),
    ("categories", .arr (cats.map categoryJson)),
    ("classifiers", .arr (clfs.map classifierJson)),
    ("functors", .arr (functors.map functorJson)),
    ("constructors", .arr (constructors.map constructorJson)),
    ("finiteLimitCones", .arr (cones.map finiteLimitConeJson)),
    ("coherences", .arr (coherences.map coherenceJson)),
    ("theoremInclusions", .arr (inclusions.map theoremInclusionJson)),
    ("aliases", .arr (als.map aliasJson)),
    ("opaqueCategories", .arr (ops.map opaqueJson)),
    ("categoryFamilies", .arr (families.map categoryFamilyJson)),
    ("namedExpressions", .arr #[]),
    ("structuralPorts", .arr #[]),
    ("presentationDispositions", .arr (presentations.map presentationJson)),
    ("source", "lean-registry"),
  ]

/-- Serialize a snapshot using Lean's JSON printer. -/
def snapshotManifestString (snap : RegistrySnapshot) : String :=
  (snapshotManifestJson snap).compress

end LeanCategories.Tools
