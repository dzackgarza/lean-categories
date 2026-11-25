# Data model: registry additions

The schema is `Catalogue/Registry/Entry.lean` and `Catalogue/Registry/Computation.lean`. Each
addition extends an existing entry or adds one; no field copies a meaning that another holds
(constitution M7).

| Entity | Change | Fields | Validation | Requirement |
| --- | --- | --- | --- | --- |
| `ComputationRef` | two constructors | `application (object : ObjectId)`, `binder (id : BinderId)` | the object row has `application`; the binder row exists | FR-003, FR-012 |
| `OperationEntry`, method and morphism rows | new field | `result : ResultKind` | `choice` requires a `ChoiceFibre` | FR-017 |
| `ChoiceFibre` | new | `family` (a family or classifier $p : E \to C$), `admissible` (proposition on a candidate), `continuation` (dependent type of later constructions) | the family is registered; the input lies in its base | FR-017 |
| `NumeralEntry` | new field | `evidence : Option Name` | present exactly when the declaration has a proposition parameter | FR-004 |
| `GraphLiteralEntry` | new field | `evidence : Name` | a registered procedure | FR-004 |
| `LiteralEntry` | new field | `closing : Name` | a registered procedure | FR-004 |
| `PropertyEntry` | new field | `evidence : Name` | a registered procedure | FR-015 |
| `MorphismEntry`, `MethodEntry` | new field | `notation : Option NotationForm` | not the function-call form of `name`; unique per owner | FR-008 |
| `NotationForm` | new | `prefix`, `infix`, `postfix`, `delimited (open close : String)` | tokens are non-empty | FR-008 |
| `LimitEntry` | new field | `objectNames : Array (String × Name)` | each name denotes an object of the shape; names distinct | FR-014 |
| `ConstructorEntry` | new field | `role : ConstructorRole` | one row per role | FR-016 |
| `ConstructorRole` | new | `arrow`, `core`, `slice`, `coslice`, `elements`, `subobjects`, `functorCategory`, `opposite`, each with its universal data | data natural in $C$ | FR-016 |
| `ReadingEntry` | new | `source`, `target`, `map`, `identification` | the map is a registered row or route | FR-011 |
| cells | new rows | `cell.sets.whole_subset.domain`, `cell.rings.additive_monoid.routes`, the order cells, the core naturality cell | invertible where stated | FR-001, FR-002, FR-016, FR-019 |
| structural edges | derived edge | $\mathrm{refine}(B, c) \to B$ for each category row with a `refine` expression | a functor row equal to a derived edge is refused | FR-025 |
| functor rows | new structural rows | the underlying set of crystals and of topological spaces, schemes to spaces, ideals to submodules, forms to their modules, modules over commutative rings to modules over rings, cusps to their lattices, the lattice inclusions | each sends an object to its underlying object | FR-022 to FR-024, FR-026 to FR-031 |
| `PowerObjectEntry` | fields point to morphism rows | `member`, `extent`, `image`, `inverseImage`, `transposeAt` | each names a row | FR-005 |
