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

section Abelian

variable {G₀ : Type w} [CommGroup G₀] [MulSemiringAction G₀ S]
  [SMulCommClass G₀ R S] [Finite G₀] [Algebra.IsInvariant R S G₀]

/-- The coherent family of arithmetic Frobenius elements over one base prime.

Mathlib constructs this family so that every value is an arithmetic Frobenius
at the corresponding prime above `P`, and any two values are conjugate. -/
noncomputable def serreArtinFamilyAtPrime
    (P : Ideal R)
    (hP : ∃ Q : Ideal.primesOver P S, Finite (S ⧸ Q.1)) :
    Ideal.primesOver P S → G₀ :=
  (IsArithFrobAt.exists_primesOver_isConj S G₀ P hP).choose

/-- In the abelian case, the coherent Frobenius family is independent of the
prime above `P`. -/
lemma serreArtinFamilyAtPrime_eq
    (P : Ideal R)
    (hP : ∃ Q : Ideal.primesOver P S, Finite (S ⧸ Q.1))
    (Q₁ Q₂ : Ideal.primesOver P S) :
    serreArtinFamilyAtPrime (R := R) (S := S) (G₀ := G₀) P hP Q₁ =
      serreArtinFamilyAtPrime (R := R) (S := S) (G₀ := G₀) P hP Q₂ := by
  have hconj :=
    (IsArithFrobAt.exists_primesOver_isConj S G₀ P hP).choose_spec.2 Q₁ Q₂
  rcases isConj_iff.mp hconj with ⟨c, hc⟩
  change
    (IsArithFrobAt.exists_primesOver_isConj S G₀ P hP).choose Q₁ =
      (IsArithFrobAt.exists_primesOver_isConj S G₀ P hP).choose Q₂
  simpa [mul_comm] using hc

/-- Serre's Artin symbol of a base prime in a finite abelian invariant
extension. The witness prime above `P` is chosen internally, and the preceding
lemma proves that the result is independent of that choice. -/
noncomputable def serreArtinSymbolAtPrime
    (P : Ideal R)
    (hP : ∃ Q : Ideal.primesOver P S, Finite (S ⧸ Q.1)) : G₀ :=
  serreArtinFamilyAtPrime (R := R) (S := S) (G₀ := G₀) P hP hP.choose

/-- The base-prime Artin symbol agrees with the arithmetic Frobenius at every
prime in the coherent family above it. -/
lemma serreArtinSymbolAtPrime_eq
    (P : Ideal R)
    (hP : ∃ Q : Ideal.primesOver P S, Finite (S ⧸ Q.1))
    (Q : Ideal.primesOver P S) :
    serreArtinSymbolAtPrime (R := R) (S := S) (G₀ := G₀) P hP =
      serreArtinFamilyAtPrime (R := R) (S := S) (G₀ := G₀) P hP Q :=
  serreArtinFamilyAtPrime_eq (R := R) (S := S) (G₀ := G₀) P hP hP.choose Q

end Abelian

end LeanCategories.Algebra
