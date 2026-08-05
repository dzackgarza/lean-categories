# lean-categories

The centralized Lean baseline of categorical constructions. Downstream projects require
this package and import the trees they need; no construction is duplicated downstream.

`LeanCategories` holds the categories themselves, organized into top-level trees that
follow subcategory containment. Lattices are one such tree, on the same footing as every
other:

```text
LeanCategories/
  Modules/           FiniteFreeZ, Bilinear, Quadratic
  Lattices/          Integral (+ Integral/Unbundled), Discriminant
  Groups/            Reflection
  Schemes/           Objects, Morphisms, Functors, Surface, Divisor, Pair
  Stacks/
  ComplexManifolds/
  Fans/
  Util/
```

Each category tree carries `Objects/`, `Morphisms/`, and `Functors/`. Directory names are
plural so the namespaces do not shadow the Mathlib identifiers `Module`, `Group`, and
`Scheme`.

`Lattices/Integral/Unbundled/` is the pre-migration monolithic layer: one namespace
holding an unbundled `IntegralLattice` (a form on a fixed carrier, no nondegeneracy) plus
Enriques-surface and fan material that belongs in `Schemes/` and `Fans/`. It duplicates
parts of `Lattices/Integral/` and is scheduled for reconciliation.

`CategoryGraph` is the neutral normalized-category-graph library migrated from the
research prototype. It owns the generic expression language, classifier machinery,
Mathlib realization, registry reflection, and JSON exporter. Sage observations and the
Sage-to-normalized correspondence remain in the research repository.

The current catalogue is a deliberately incomplete specimen. It establishes a
Lean-authoritative registry/export path but does not claim the complete normalized
catalogue or the research repository's 179-row Sage correspondence.

```bash
just cache
just build
lake exe category-graph-export
```

## Mathematical design

This repository builds one higher-categorical mathematical language, its Lean
formalization, a Sage correspondence into it, and the foundation for a computational DSL
whose users see only ordinary mathematics. The programme's three coupled outputs:

1. **A Lean-owned mathematical foundation** in which categories, higher categories,
   classifiers, functors, higher cells, limits, and categories of structured objects have
   principled definitions.
2. **A Sage correspondence** mapping Sage's empirical category system and algorithms into
   that normalized universe — without making Sage's labels, parent graph, or
   implementation accidents authoritative.
3. **A computational mathematics DSL** in which a mathematician introduces and
   interrogates objects by ordinary membership and notation, while formalization and
   backend routing remain invisible.

The conceptual compression: structures and axioms are **classifier morphisms**; an
assertion of structure is a **lift**; transport is **(homotopy) pullback**; compatible
structures are imposed by a **limit**; comparisons are **higher cells**; equations and
coherence come from **operation-built diagrams and fillers**; a named special object is
usually a **value of a generic functor**; a theorem is a **factorization, lift, or
comparison** — never data baked into a definition; computation is inherited along the
same functorial structure. The current code is a 1-/2-truncated *realization* of that
foundation, never the foundation itself.

Work is aligned when it is stated at the lowest level at which it is generated, in
standard mathematics auditable by a working mathematician, such that later domains
(monoidal categories, stacks, spectra, derived objects, general limits) become instances
rather than refactors.

The full orientation — including the anatomy of agent drift and the alignment lens every
task should pass through — is [AGENTS.md](AGENTS.md). The **mathematical constitution** —
the definitions, variance conventions, truncations, exact sequences, and settled
conventions this repository formalizes — is [FOUNDATIONS.md](FOUNDATIONS.md)
("Mathematical Foundations of the Categorical Research Language", 66 sections: the
(∞,2)-ambient, classifiers and lifts, operation and diagram-extension classifiers, forms
and intrinsic lattices, discriminant theory, sites/stacks/deformation theory, the SageCat
comparison category, the computational-language semantics, categorical presentations,
exact packages, and convex/reflection/period/degeneration geometry). AGENTS.md governs
*how* agents work; FOUNDATIONS.md governs *what* the mathematics is. The governing
execution state is the issue ledger
([#1](https://github.com/dzackgarza/lean-categories/issues/1): north star, decision
records) and the consolidated work units (#30–#40, #21–#29).
