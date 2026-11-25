# Contract: what a consumer reads after this feature

A consumer reads the registry at a pinned revision through `RegistrySnapshot`
(`Catalogue/Registry/Snapshot.lean`) and the exported catalogue. This feature adds these read
surfaces. Each is a projection of rows; no consumer keeps its own table.

| Question of the consumer | Answer in the registry | Requirement |
| --- | --- | --- |
| Which row owns `·` (or `+`, `0`, `1`, `-`) on an object? | the owner row and the `refines` chain along the selected structural route | FR-001, FR-018 |
| Are two routes the same? | the registered cell between them | FR-001, FR-002, FR-016, FR-019 |
| What address names an application or a binder operation? | `ComputationRef.application`, `ComputationRef.binder` | FR-003, FR-012 |
| Which procedure settles a literal obligation or a property? | `evidence` or `closing` of the row | FR-004, FR-015 |
| What does membership, transpose, extent, image, inverse image name? | morphism rows of the power object | FR-005 |
| What numerals does an object have? | numeral rows at the generating category and their restrictions | FR-006, FR-007 |
| Which row does a written form denote? | the notation index | FR-008, FR-010 |
| May a term be read as a related one? | a `ReadingEntry` with its data, or no reading | FR-011 |
| Which object of a shape has a written name? | `LimitEntry.objectNames` | FR-014 |
| Is an answer prescribed or chosen? | `result` and its `ChoiceFibre` | FR-017 |
| Which constructor is the arrow (core, slice, ...) constructor? | `ConstructorEntry.role` | FR-016 |
| Which categories must be implemented before a category? | the categories that its structural edges reach, with the derived edges of refinements | FR-022 to FR-031 |
| What is the automorphism group of an object of $\mathcal C$? | the one generic construction $\operatorname{Aut}$ at $\mathcal C$, never the one of an underlying object | FR-051 |
| Is `Units` the underlying set of the units functor's value? | the identification that `obj.sets.units` cites | FR-051 |
| Which procedure admits a written element into a domain? | the `evidence` of the domain's object row | FR-004, FR-049 |
| What is the product of two groups? | `lim.groups.product` | FR-050 |

Outcomes that a consumer must not infer: a reading with no `ReadingEntry`; a point of a structure
classifier from `Holds`; an equality of routes with no cell; a value of a `choice` operation fixed
by its Lean definition.
