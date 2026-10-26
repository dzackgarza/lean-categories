# Whole-family computational derivations

## Mathematical scope and source decision

This is an interface completion for the already formalized catalogue, outside the
foundational textbook sweep. It introduces no algebraic operation or alternative
category calculus. The mathematical construction is ordinary substitution of
functions into a Lean function, with a proof that the resulting **entire dependent
family** equals an existing published family. Lean's dependent function types,
application, conversion, and propositional equality already supply this construction.

The [Lean reference on propositional equality](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Propositional-Equality/)
gives the governing equality and substitution rules. The existing catalogue
[operation agreement contract](operation-agreement.md) already requires complete
families, rigid parameters, and retained selected structures. A computation
derivation applies that same requirement to a plan built from published operations.
It does not identify two operation bindings by their types or by particular values.

[CAP, Managing Derived Methods, chapter 8](https://homalg-project.github.io/CAP_project/CAP/doc/chap8_mj.html)
is computational prior art: derivations declare a target, prerequisite operations,
and a function; derived methods become usable from installed primitives. Its
applicability condition must be independent of `CanCompute`. This interface uses
that separation and dependency closure. CAP's weights and optimization are not
mathematical data here and are outside this contract.

## Exact published references

`ComputationRef` addresses an existing operation, functor, method, construction,
or named morphism. The reference kind and existing ID are retained. A method
resolves to its registered functor family, while its method address remains
available to the consumer. A reference cannot be reconstructed from a carrier,
endpoint type, surface name, computational answer, or installation order.

The declaration at the referenced owner supplies its entire type. Parameters are
the declaration's Lean binders, not a separately authored argument schema. Their
order, dependency, implicitness, selected categories, and selected structures are
preserved. Universe arguments are actual Lean levels, not strings.

## Plans are ordinary Lean functions

For a target declaration `t : T`, a row supplies prerequisite references resolving
to families `p₁, …, pₙ`, a transparent definition `plan`, and `correctness`.
The plan's first `n` binders have exactly the complete types of those families.
Its remaining type, **after substitution of those actual families**, is `T`.
The remainder may depend on the primitive slots: a supplied functor's object map
determines an intermediate carrier, so the carrier is retained until the selected
functor is substituted.

The required proposition is exactly

```lean
plan p₁ ... pₙ = t
```

at the complete type `T`. If `T` is a dependent function type, this is equality
of the functions before any parameters, objects, numerals, or operands are
selected. Ordinary `Eq.refl` can prove a definitional equation; other existing
checked equalities can prove nondefinitional equations. A proposition about one
selected object or one returned value does not have this type.

The target is first constructed with all its universe parameters rigid. Inference
may then determine the universe applications of the plan, primitives and proof.
It cannot specialize the target to make the check succeed. Any remaining
metavariable, loose bound variable, or free term parameter is rejected. Correctness
is checked as a closed proof of the exact equality, with no extra assumptions.
The standard release axiom budget is enforced; an unsafe declaration, `sorry`,
or an additional axiom cannot establish a derivation.

The primitive prefix is opened with fresh locals before substitution. Every slot
must occur in the computational term after beta and let reduction; occurrences
only in types or proofs do not invent prerequisites. The original slot order and
reference are retained even if two referenced declarations happen to be
definitionally equal. Slot order is function argument order, not plan priority.

`CheckedComputationDerivation` retains the target, its complete type, the primitive
families and their complete types, the lambda template, the applied closed plan,
the proof and rigid universe parameters. This is an in-memory checked interface.
There is no JSON parser, backend identifier, session handle, answer or policy
weight in the mathematical contract.

## Registry and consumer API

`Registry/Computation.lean` owns a separate persistent environment extension.
It reuses the semantic registry's author boundary and exact declaration owners.
Only `LeanCategories` modules may publish a row with
`normalized_computation_derivation`. Duplicate derivation identities and unknown
published references are rejected. Multiple different derivation IDs may have the
same exact target.

The public entry points are:

| Declaration | Purpose |
| --- | --- |
| `ComputationRef.declaration` | Resolve the exact existing published address. |
| `validateComputationDerivation` | Check a row and return its full typed expressions and proof. |
| `computationDerivations` | Read all persistent rows; these names alone are not proof. |
| `checkedComputationDerivations` | Resolve and check every alternative for one exact target. |
| `addComputationDerivationChecked` | Validate and publish a row at the upstream author boundary. |

Consumers instantiate the checked package at the original complete parameters and
interpret the existing Lean expression. Primitive applications retain their slot's
exact reference. Ordinary application, beta/let reduction, pairing, categorical
composition, and registered functor or constructor actions keep their existing
owners. This catalogue creates no second execution language. A consumer that
cannot interpret an expression reports that computational gap explicitly; it may
not calculate a mathematical answer as a substitute or alter the target's meaning.

Executable availability is the closure of installed primitive computations under
these checked plans. A plan is usable when all its required calls have usable
computations, which may themselves use other checked plans. The consumer must
consider alternatives; choosing the first failing alternative does not establish
that the target has no implementation. A finite derivation tree must terminate at
available primitives. Cycles without such a grounding supply no computation.

Cyclicity is **not** a defect in a proved mathematical equation, so this upstream
catalogue does not ban it. Availability, cycle detection, and execution belong to
the consumer. Mathematical operation resolution and ambiguity are completed
independently of installed primitives. Adding or removing a primitive must not
change which operation was asked for.

## Existing multiplication supplies the concrete chain

`Semantics/Algebra/ComputationDerivations.lean` reuses the two Mathlib forgetful
functors already composed by `Ports.ringsMultiplicative`:

1. `forget₂ RingCat SemiRingCat`, from `RingCat.hasForgetToSemiRingCat`;
2. `forget₂ SemiRingCat MonCat`, from `SemiRingCat.hasForgetToMonCat`.

Their publications retain the existing selected structures, and identity natural
isomorphisms compare their new paths with the existing monoid port and underlying
set path. No automatic structural route is introduced without that comparison.

Ring multiplication has two plans. One applies the published monoid multiplication
at its multiplicative monoid. The other applies published semiring multiplication
at the underlying semiring. Semiring multiplication in turn applies the same
published monoid multiplication. The monoid port itself has the plan given by the
ordinary composite of its two factors. The resulting dependency graph has multiple
prerequisites, a chain, and alternatives, without a preferred semantic route.

The ring-to-monoid whole-family equation is the already accepted
`MonoidOperationAgreement.ring_mul`. The other equations unfold exactly the
existing Mathlib forgetful functors and the already published operation
definitions. They are proved by `rfl`, before selecting rings or operands. There
are no computational expected answers in this module.

## Reuse record, 2026-10-26

The pinned Mathlib source is `db584cd6d46c92f209a44c0f1c829460d327499d`,
Apache-2.0, with Lean 4.33.0. Inspected owners were
`Mathlib/Algebra/Category/Ring/Basic.lean` (the two `HasForget₂` instances),
`Mathlib/Algebra/Category/MonCat/Basic.lean`, and the existing upstream
`Ports`, `MonoidOperations`, `NamedRings`, `Semirings`, and
`MonoidOperationAgreement`. The registry retains those exact constructions.

Required live formalization-corpus searches used
`scripts/formalization_corpus.py` and its live OpenAPI discovery:

| Query | Observed result and use |
| --- | --- |
| `"Eq.refl" "funext"` | Existing dependent-function equality implementations; Lean's native equality rules remain the direct owner. |
| `"derived operation"` | LeanCert's expression-level subtraction/division and Isabelle Word_Lib hits; neither is an exact published dependent-family registry, and no alternative expression calculus was imported. |
| `"forallTelescope" "mkEq"` | Mathlib `Mathlib/Lean/Meta/Simp.lean::simpEq`; inspected its use of rigid telescope opening and retained equality proofs, then reused Lean's own APIs directly. |
| `"MonoidOperationAgreement"` | No live indexed hit; the pinned local declaration was inspected directly and is reused. |
| `hasForgetToSemiRingCat OR hasForgetToMonCat` | No live indexed hit; the exact pinned Mathlib instances were inspected directly. |

The first sandboxed API attempts failed for lack of network permission. The
authorized read-only queries then succeeded. An absent index hit is not treated
as evidence that the mathematical construction is missing: the inspected native
Lean and pinned Mathlib owners supply all the mathematics. Only catalogue metadata,
validation, and the publication of their checked compositions are authored here.

## Author verification, 2026-10-26

Focused Lean checks succeeded for `Registry.Computation`,
`Semantics.Algebra.ComputationDerivations`, and `Registry.ComputationProbes`.
The changed public aggregates `Catalogue.Semantics` and `Catalogue` also succeeded,
so ordinary public catalogue imports expose the concrete derivations. These are
formal interface checks, not an independent computational acceptance verdict.

`ComputationProbes` checks both alternatives and the recursive chain; exact
whole-family proof retention; full ring/exponent parameters and rigid functor
universes; and all published reference kinds. It rejects unknown references,
omitted and wrong primitive families, a proof about addition in place of
multiplication, an unrelated proposition, discarded or proof-only primitives,
and object/exponent/universe specialization. A correct self-dependent identity
is accepted without claiming computational availability. The discarded-let probe
caught and fixed an initial traversal error: Lean's `zetaReduce` does not itself
beta-reduce a direct lambda application, so explicit `headBeta` is required before
counting primitive calls.

Checks used the pinned Lean 4.33.0 executable, one process at a time, with
`LEAN_NUM_THREADS=1`. Each invocation was `lean --root=<isolated-worktree> -o
<isolated-olean> -i <isolated-ilean> <module.lean>`. The upstream base was
`82d1370de372a00a86391b74fc2566c9547dfcb6`. Its immutable `lib/lean` artifacts were
copied to the isolated worktree; all new outputs were written there. No shared
source, dependency checkout, C object or native-build artifact was modified.
The inherited registry's `backward.privateInPublic` convention produces visibility
warnings for private extension/helpers; the five checks exit successfully.

The main shared compiled import boundaries had these SHA-256 hashes:

| Imported `.olean` | SHA-256 |
| --- | --- |
| `LeanCategories.Catalogue.Registry.Semantic` | `8da6eb2683ac1d53ad38903edc7014e20dd4fa140f2b8a52413e2e83bf135460` |
| `LeanCategories.Catalogue.Semantics.Algebra.MonoidOperationAgreement` | `93e606e94088302f4812d712ad5618c787ab436b09600c990f7c2ea0e1493e14` |
| `LeanCategories.Catalogue.Semantics.Algebra.Semirings` | `67804af8e9487fbc34ca2b1c2aa2d24dab74beb812f5cf08d2e2c2f8589e7ff3` |
| `Lean.Util.CollectAxioms` | `852c1b26920c4aa9a451d6fa466245a3a8a6b3ae597592c785d7f767234ff4de` |
