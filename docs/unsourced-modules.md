# Modules with no citable source (#59 transformation 5)

A card inherits its `source:` line from its definition module. A module gets one only when a text
that states the result or the construction it realizes actually exists — a corpus catalogue unit
under `corpus/`, cited by id, or a `FOUNDATIONS.md` heading, cited by anchor. A module with neither
is listed here with its owner and a one-line description of the section a source would need. No
citation is invented, and no docstring here claims one.

Card population: **394** cards, after the companion test below.

## Companion rule (460 → 394)

The graph's `theorem`-kind declarations, restricted to those referenced from a module other than
their own, number 460. Sixty-six of those are **generated companions**: class- and structure-field
projections, `@[ext]` lemmas, instance projections and tactic-block auxiliaries. They are
`theorem`-kind in the elaborated environment but have no `theorem`/`lemma` declaration of their own
name in their module, so no signature can be copied and no card can be emitted from them. The test
is by source, not by name pattern: `extract_cards.py` prints every companion it excludes.

## Unsourced modules

| Module | Owner | What a source would need to state |
|---|---|---|
| `LeanCategories.Foundation.Subsets` | Foundation | Subsets as subobjects of a set, the two functors to `Set`, and the ambient equivalence induced by an isomorphism of subobjects; no `corpus/` unit and no `FOUNDATIONS.md` heading covers subobject representations |

| `LeanCategories.Algebra.IntegralGeneralLinearGroup` | Algebra | integral points of the general linear group as a profinite topological group; no `corpus/` unit names this module and `FOUNDATIONS.md` has no matching heading |
| `LeanCategories.Algebra.IntegralAdeleRing` | Algebra | the integral adele ring of a number field as a restricted product; no `corpus/` unit and no `FOUNDATIONS.md` heading states it |
| `LeanCategories.Algebra.IdealProfiniteCompletion` | Algebra | profinite completion of an ideal as an inverse limit of quotients; no `corpus/` unit and no `FOUNDATIONS.md` heading states it |
| `LeanCategories.Modules.Bilinear.Valued.Cokernel` | Modules | cokernel of a morphism of valued bilinear modules; no `corpus/` unit and no `FOUNDATIONS.md` heading states it |
| `LeanCategories.Modules.Bilinear.Valued.Total` | Modules | total space of a valued bilinear module; no `corpus/` unit and no `FOUNDATIONS.md` heading states it |
| `LeanCategories.Modules.Bilinear.Valued.Fixed` | Modules | fixed points of a group action on a valued bilinear module; no `corpus/` unit and no `FOUNDATIONS.md` heading states it |
| `LeanCategories.Modules.Bilinear.Valued.OrthogonalSum` | Modules | orthogonal direct sum of valued bilinear modules; no `corpus/` unit and no `FOUNDATIONS.md` heading states it |
| `LeanCategories.Modules.Bilinear.Valued.TopologicalOrthogonalGroup` | Modules | topological orthogonal group of a valued bilinear module; no `corpus/` unit and no `FOUNDATIONS.md` heading states it |
| `LeanCategories.Modules.Quadratic.Valued.Witt` | Modules | Witt group of valued quadratic modules; no `corpus/` unit and no `FOUNDATIONS.md` heading states it |
| `LeanCategories.Modules.Quadratic.Valued.IsometryClasses` | Modules | isometry classes of valued quadratic modules; no `corpus/` unit and no `FOUNDATIONS.md` heading states it |
| `LeanCategories.Modules.Quadratic.Valued.Fixed` | Modules | fixed points of a group action on a valued quadratic module; no `corpus/` unit and no `FOUNDATIONS.md` heading states it |
| `LeanCategories.Modules.Quadratic.Valued.Total` | Modules | total space of a valued quadratic module; no `corpus/` unit and no `FOUNDATIONS.md` heading states it |
