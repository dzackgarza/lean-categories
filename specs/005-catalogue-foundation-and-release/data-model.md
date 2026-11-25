# Data model: foundation and registry additions

The schema is `Catalogue/Registry/Entry.lean`, `Catalogue/Syntax.lean` and
`CategoryTheory/OneCat/`. Feature 001 owns the additions of its
[data model](../001-catalogue-inputs-for-the-cas/data-model.md); this table adds only fields
that 001 does not add, and no field copies a meaning that another holds (constitution M7).

| Entity | Change | Fields | Validation | Requirement |
| --- | --- | --- | --- | --- |
| `Classifier` | parameterized by the ambient model | `model : AmbientModel`, `total`, `forget` | `total` and `forget` live in `model` | FR-001 |
| `PropertyClassifier` | abbreviation | `Classifier` with `full`, `faithful`, `replete : (Functor.essImage forget).IsClosedUnderIsomorphisms` | theorem for `Classifier.ofProperty` | FR-002 |
| `ClassifierSquare` | new | `base`, `total`, `iso : CatCommSq …` | the 2-cell is data, never `Nonempty` | FR-003 |
| `ClassifierEntry` | new fields | `total : CategoryExpr`, `leg : FunctorId` | the leg's source is `total`, its target `host` | FR-010 |
| category and functor rows | new field | `denotation : Lean.Name` naming `eval e ≌ C` (or `≅` of functors) | elaborates; generic evaluator only | FR-007 |
| `CategoryExpr`, `FunctorExpr` | new constructors | `cell`, `diagram`, `filler`, `equivalence`, `operadicAlgebra` | evaluated relative to a model | FR-009 |
| `ConstructorEntry` | new fields | `parameters : Array ParameterKindId`, `hypotheses : Array Lean.Name`, `onMorphisms : Lean.Name`, `evaluator : Lean.Name` | every field elaborates; export carries all | FR-011 |
| `CategoryFamilyEntry` | new fields | `base : CategoryExpr`, `variance : VarianceId`, `fibration : Lean.Name` | a Grothendieck construction over `base` | FR-012 |
| `MethodEntry` | field type | `semantic : NormalizedFunctorExpr` | typechecks; no independent declaration | FR-015 |
| `AdjunctionEntry` | new fields | `unit`, `counit`, `triangles : Lean.Name` | an actual Mathlib `Adjunction` | FR-016 |
| `ReflectiveLocalizationEntry` | new | `inclusion : FunctorId`, `adjunction : AdjunctionId`, `recognition : Lean.Name` | unit recognition theorem elaborates | FR-016 |
| `ReleaseManifest` | new (export) | `schemaVersion`, `tag`, `revision`, `rows` | canonical order; reproducible | FR-019 |
