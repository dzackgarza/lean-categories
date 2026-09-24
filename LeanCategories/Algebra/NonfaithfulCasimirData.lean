/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.TraceForm

/-!
# Casimir data for a nonfaithful semisimple representation

Definition-level realization of Humphreys FC14-C02-U039.

For a representation of a semisimple Lie algebra, Humphreys discards the
simple ideals contained in the representation kernel, restricts to the sum of
the remaining simple ideals, and performs the ordinary trace-form Casimir
construction there.

This file records exactly that data-level reduction.  The facts that the
displayed ideal complements the kernel, that the restricted action is
faithful, that its trace form is nondegenerate, and that the resulting Casimir
operator is independent of the chosen trace-dual bases are result content.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanCategories.Algebra

universe u v w x

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The sum of the simple summands on which the representation is nontrivial.

For a semisimple Lie algebra these are precisely the atomic ideals not
contained in the kernel of the action.  Identifying this supremum as a direct
complement of the kernel is deliberately not part of the definition. -/
def nonfaithfulCasimirSupportIdeal : LieIdeal R L :=
  sSup {I : LieIdeal R L | IsAtom I ∧ ¬ I ≤ LieModule.ker R L M}

/-- The trace form of the representation after restriction to its Casimir
support ideal. -/
def nonfaithfulCasimirTraceForm :
    LinearMap.BilinForm R (nonfaithfulCasimirSupportIdeal R L M) :=
  LieModule.traceForm R (nonfaithfulCasimirSupportIdeal R L M) M

/-- Humphreys' Casimir finite sum after restricting a possibly nonfaithful
representation to the sum of simple ideals on which it is nontrivial.

The supplied families are the source's chosen trace-dual bases.  Duality and
basis-independence are hypotheses/results surrounding this formula, not new
construction clauses here. -/
def nonfaithfulCasimirOperatorFromDualFamilies
    {ι : Type x} [Fintype ι]
    (a b : ι → nonfaithfulCasimirSupportIdeal R L M) : Module.End R M :=
  ∑ i, LieModule.toEnd R (nonfaithfulCasimirSupportIdeal R L M) M (a i) *
    LieModule.toEnd R (nonfaithfulCasimirSupportIdeal R L M) M (b i)

end LeanCategories.Algebra
