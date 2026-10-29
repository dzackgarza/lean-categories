# Agreement of inherited element operations

`OperationEntry` binds a surface name on its complete selected owner. The first
binding on each structural path remains the lookup rule described in
`Entry.lean` and `SemanticState.isFirstOperationBindingRoute`. This document
specifies the comparison of the surviving bindings. It gives no priority to an
owner, declaration, route length, or registration position.

## The comparison is a universal family of whole maps

Let `C(p)` be the complete source category, including its chosen category
structure and all dependent parameters `p`. For each surviving binding retain:

- its registered operation ID and declaration;
- its ordered structural route from `C(p)` to the registered owner;
- every declaration and structural parameter, including the selected base,
  constructor arguments, and any numeral parameters;
- the complete typed operation, with its actual operand domain and result.

Introduce `p`, any further independent route or declaration parameters `q`, and
`X : C(p)` as **rigid universally quantified variables**. Construct the two
operations from the registered declarations at their actual routed images of
this same `X`. These are whole morphisms `P(p,q,X) ⟶ A(p,q,X)`, not their values
on operands. Abstract the complete dependent context, in its declared order.
The comparison is an equality of these entire dependent functions. Equivalently,
it is a theorem universally quantified over that context equating the whole
morphisms. No selected source object or operand has been substituted yet.

The endpoint types include all selected structures. If registered comparisons
are needed to place the two maps at common endpoints, their actual directed
components must first be composed into these families. A carrier equality alone
does not perform that transport. Both the original routes and every comparison
used remain part of the interpreted operation.

The context must be complete. Unresolved metavariables cannot stand for universal
parameters; unification must not choose an object, a scalar structure, a route
parameter, or an operand to make the equality hold. An independently chosen
owner is a different variable and cannot be replaced by the other one merely
because their carriers agree. Let-bound selected values and omitted declaration
parameters do not establish a universally quantified agreement.

## Definitional equality is a generic discharge

If these complete families, including their full dependent types, are
definitionally equal in Lean, `Eq.refl` checked at their exact equality type is
accepted agreement evidence. This is the identity comparison supplied by the
existing formal definitions. It needs no additional operation-agreement registry
row and no list of privileged category pairs. The consumer must retain the
typed equality and the two original operation/route descriptions; a Boolean
comparison of normalized values is insufficient.

This rule uses Lean's ordinary conversion and equality introduction rules. It
does not permit comparison of two partially applied declarations after choosing
`X`, specializing numeral parameters, erasing an owner bundle, applying operands,
or computing a leaf answer. It does not equate the operation owners themselves,
change the first-binding rule, erase routes, or select a representative by order.

For nondefinitional agreement, an existing accepted comparison must establish
this same entire family equation with its actual transports. Absence of such
data leaves the surviving bindings ambiguous. A malformed or ill-typed supplied
comparison is invalid evidence, not successful agreement or an absent comparison.
Several possible transports are not identified by enumeration order: they remain
distinct unless existing coherence or a checked whole-family equality identifies
their resulting operations. This rule introduces no new search over unregistered
theorems or carrier isomorphisms.

After verification, equality substitution may instantiate the universal witness
at the exact selected context. Precomposition with any retained structural
functor is ordinary congruence on that equality, so named categories, classifier
totals, parameterized categories, and constructed categories obey the same rule.
The functor and every one of its parameters must remain in the precomposed
family. Equality does not authorize dropping a nonidentity presentation or
replacing a prescribed structural map.

## Existing ring multiplication

For every complete ring `R`, the two complete maps

```lean
MonoidOperations.mul (Ports.ringsMultiplicative.toFunctor.obj R)
NamedRings.mul R
```

are definitionally equal. The first reads the multiplication field of the
selected multiplicative monoid, which the existing forgetful functor obtains
from that same `R`. On commutative rings the existing
`cell.commutative_rings.multiplicative_monoid` also compares the routes through
`Rings` and through `CommutativeMonoids` at the structured monoid, with identity
components. Thus the direct ring operation and the monoid operation reached by
the second route agree as a universal family. Precomposing with the field
classifier's forgetful functor or a parameterized algebra's forgetful functor
preserves this exact equation.

`Semantics/Algebra/MonoidOperationAgreement.lean` supplies the closed family
equalities. Its focused source tests include the actual field and algebra
precompositions. No new comparison row is required for these reflexive
equalities, and no selected finite field or integer operands occur in their
proofs.

The additive monoid obtained from a ring's additive group has multiplication
equal to the ring's **addition**. It is a different whole operation. Over the
integers, addition and multiplication agree at `(2,2)` but differ at `(2,3)`.
Likewise, two independent monoid structures on the same carrier, two source
objects that coincide only after substitution, or two exponent parameters
specialized to the same numeral cannot be merged by this rule. The source tests
check these separating cases before any computational implementation is involved.

## Sources and scope

The equality rules are Lean's `Eq.refl`, equality substitution, and congruence;
see the [Lean reference, Propositional Equality](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Propositional-Equality/).
The checked source uses Lean 4.33.0. The ring/monoid structures and forgetful
functors are Mathlib's `RingCat`, `CommRingCat`, `MonCat`, and `forget₂`, at the
repository's pinned Mathlib revision. The existing upstream owners are
`Ports.lean`, `CommutativeMonoids.lean`, `NamedRings.lean`, and
`MonoidOperations.lean`. The 2026-10-24 formalization-corpus searches `Eq.refl`
and `commutativeRingsMonoidsCell` were followed by inspection of these declarations;
the latter comparison is already present locally. This is an interface completion
for existing formal equalities, not a new algebraic identification.
