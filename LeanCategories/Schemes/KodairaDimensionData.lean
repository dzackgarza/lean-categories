/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Kodaira-dimension definition data

Definition-level realization of Hartshorne FC06-C05-U139.

For a projective variety with canonical divisor K, Hartshorne forms the
pluricanonical section algebra

  R(K) = direct sum over n>=0 of H^0(X, L(nK))

and defines

  kappa(X) = trdeg_k R(K) - 1,

with the convention kappa(X) = -1 when every positive pluricanonical linear
system |nK| is empty.

The canonical sheaf/divisor, tensor powers, global sections, graded direct sum,
and multiplication are earlier inputs. Sweep III does not reprove that
assembly. This file records precisely the data from that assembly used by the
definition.  Before the geometric finiteness theorem is available, the
definition is stored canonically as an optional cardinal: `none` is
Hartshorne's value `-1`, while `some c` records `κ + 1 = c`.  For the
projective varieties in Hartshorne, later result work proves that `c` is a
positive finite cardinal and therefore recovers the usual integer value.

The equivalent maximal-image-dimension description and birational invariance
are comparison/result statements and are deliberately not included here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Schemes

universe u v

/-- The already-assembled pluricanonical section algebra together with the
source predicate recording whether each positive pluricanonical system is
nonempty.

In the Hartshorne application, sectionRing is the graded direct sum of the
spaces H^0(X,L(nK)), and systemNonempty n says |nK| is nonempty. The
construction of those objects belongs to the preceding canonical-sheaf and
linear-system owners. -/
structure PluricanonicalSectionRingData
    (k : Type u) [Field k] where
  sectionRing : Type v
  commRing : CommRing sectionRing
  algebra : Algebra k sectionRing
  systemNonempty : ℕ → Prop

/-- The transcendence degree of the supplied pluricanonical section algebra. -/
def pluricanonicalTranscendenceDegreeData
    {k : Type u} [Field k]
    (D : PluricanonicalSectionRingData k) : Cardinal := by
  letI : CommRing D.sectionRing := D.commRing
  letI : Algebra k D.sectionRing := D.algebra
  exact Algebra.trdeg k D.sectionRing

/-- A proof-free, total encoding of Kodaira dimension before geometric
finiteness is established.

* `none` means that every positive pluricanonical system is empty, i.e.
  Hartshorne's convention `κ = -1`;
* `some c` means that a positive pluricanonical system is nonempty and
  `κ + 1` is represented by the transcendence-degree cardinal `c`.

This representation does not choose an integer from a cardinal.  The theorem
that the second case is a finite positive cardinal belongs to the result
layer. -/
def kodairaDimensionData
    {k : Type u} [Field k]
    (D : PluricanonicalSectionRingData k) : Option Cardinal := by
  classical
  exact if ∃ n : ℕ, 0 < n ∧ D.systemNonempty n then
    some (pluricanonicalTranscendenceDegreeData D)
  else
    none

/-- Hartshorne's exact defining graph for Kodaira dimension.

The value -1 is used exactly when every positive pluricanonical system is
empty. Otherwise d >= 0 is the Kodaira dimension exactly when the
pluricanonical section algebra has transcendence degree d+1.

No finiteness theorem for the transcendence degree is needed to state this
graph. -/
def IsKodairaDimensionData
    {k : Type u} [Field k]
    (D : PluricanonicalSectionRingData k) (κ : ℤ) : Prop :=
  (κ = -1 ∧ ∀ n : ℕ, 0 < n → ¬ D.systemNonempty n) ∨
    ∃ d : ℕ,
      κ = (d : ℤ) ∧
        (∃ n : ℕ, 0 < n ∧ D.systemNonempty n) ∧
          pluricanonicalTranscendenceDegreeData D = (d + 1 : ℕ)

end LeanCategories.Schemes
