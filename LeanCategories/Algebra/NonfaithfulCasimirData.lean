/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.TraceForm
public import Mathlib.LinearAlgebra.Basis.Basic

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

/-- Source data for the trace-dual bases used in the Casimir construction. -/
structure NonfaithfulCasimirDualBasisData
    (ι : Type x) [Fintype ι] [DecidableEq ι] where
  left : Basis ι R (nonfaithfulCasimirSupportIdeal R L M)
  right : Basis ι R (nonfaithfulCasimirSupportIdeal R L M)
  dual (i j : ι) :
    nonfaithfulCasimirTraceForm R L M (left i) (right j) =
      if i = j then 1 else 0

/-- Humphreys' Casimir finite sum after restricting a possibly nonfaithful
representation to the sum of simple ideals on which it is nontrivial.

The input is the source's chosen pair of trace-dual bases, rather than two
arbitrary families. Basis-independence is result content. -/
def nonfaithfulCasimirOperatorFromDualFamilies
    {ι : Type x} [Fintype ι] [DecidableEq ι]
    (D : NonfaithfulCasimirDualBasisData R L M ι) : Module.End R M :=
  ∑ i, LieModule.toEnd R (nonfaithfulCasimirSupportIdeal R L M) M (D.left i) *
    LieModule.toEnd R (nonfaithfulCasimirSupportIdeal R L M) M (D.right i)

end LeanCategories.Algebra
