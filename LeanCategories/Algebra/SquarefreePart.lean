/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Rat.Lemmas

/-!
# Squarefree representatives of rational square classes

This supplies the canonical arithmetic datum used in Dummit--Foote
FC01-C07-U012.  The field-comparison theorem belongs to the theorem sweep.
-/

@[expose] public section

namespace Int

/-- The squarefree kernel of an integer: retain exactly the prime factors that
occur to odd exponent, together with the sign.  This is the canonical
squarefree representative of the integer modulo rational squares. -/
def squarefreePart (n : ℤ) : ℤ :=
  sign n *
    (((n.natAbs.factorization.support.filter fun p =>
      Odd (n.natAbs.factorization p)).prod id : ℕ) : ℤ)

end Int

namespace Rat

/-- The squarefree part of a rational number.  For reduced `q = a / b`, the
rational square class of `q` is represented by the integer `a*b`; applying the
integer squarefree kernel therefore gives the canonical squarefree integer
representative. -/
def squarefreePart (q : ℚ) : ℤ :=
  Int.squarefreePart (q.num * q.den)

end Rat
