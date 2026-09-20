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

/-- Serre's chosen-prime representative for the Artin symbol
(FC10-C01-U081).

In an abelian extension the independence from the chosen prime above the base
prime is a theorem; the Sweep-III datum is the same arithmetic Frobenius
element already named in U079. -/
noncomputable abbrev serreArtinRepresentative
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] : G :=
  serreFrobeniusSubstitution (R := R) (S := S) (G := G) Q

/-- Neukirch's chosen-prime representative for the unramified Frobenius / Artin
element (FC09-C06-U074).

In an abelian extension the representative is independent of the chosen prime
above the base prime.  That independence, the decomposition-group generation
statement, and the residue-congruence characterization are result-layer facts;
the Sweep-III datum is just the chosen arithmetic Frobenius element itself. -/
noncomputable abbrev neukirchArtinRepresentative
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] : G :=
  serreFrobeniusSubstitution (R := R) (S := S) (G := G) Q

end LeanCategories.Algebra
