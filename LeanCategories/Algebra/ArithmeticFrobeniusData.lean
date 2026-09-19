/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Frobenius

/-!
# Arithmetic Frobenius data

Serre, *Local Fields*, Chapter I (FC10-C01-U079).

Pinned Mathlib already constructs an arithmetic Frobenius element for a prime
with finite residue field in a finite invariant action.  This file gives that
chosen element the source-level name used by Serre.

Membership in the decomposition group, uniqueness at an unramified prime, and
generation of that decomposition group are result statements and are not
bundled into this Sweep-III construction.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v w

variable {R : Type u} {S : Type v} {G : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
variable [Finite G] [Algebra.IsInvariant R S G]

/-- Serre's Frobenius substitution at a prime with finite residue field
(FC10-C01-U079), as the ambient Galois-action element.

Pinned Mathlib's `arithFrobAt` is the chosen element satisfying the defining
arithmetic-Frobenius congruence. -/
noncomputable abbrev serreFrobeniusSubstitution
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] : G :=
  arithFrobAt R G Q

end LeanCategories.Algebra
