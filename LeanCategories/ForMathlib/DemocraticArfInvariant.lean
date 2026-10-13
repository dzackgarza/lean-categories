/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The democratic Arf invariant over `𝔽₂`

This ports the majority-count construction from
`roed-math/gq2-lean@3c7b1abaf04ec8424decc2b1eb1b91bfe0ce5a33`,
`GQ2/QuadraticFp2.lean`. The reference is released under Apache-2.0.

Peters--Sterk, *Symmetric and Quadratic Forms* (June 2024), §16.3
(`FC11-C16-U023`), call the Arf invariant of a finite quadratic space of type I or II over `𝔽₂`
the democratic invariant: it is the value taken by the quadratic form on the majority of
vectors. These are precisely the even-dimensional cases in Table 16.3.2, where the polar form
is nondegenerate. The odd semi-unimodular type III spaces in the surrounding section have tied
fiber counts and are outside this convention.
-/

@[expose] public section

namespace LeanCategories.ForMathlib.QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- The number of vectors on which a quadratic form over `𝔽₂` takes the value zero. -/
noncomputable def zeroCount (q : QuadraticForm (ZMod 2) V) : ℕ :=
  Nat.card {v : V // q v = 0}

/-- The democratic, or majority-value, invariant of a finite quadratic form over `𝔽₂`
with nondegenerate polar form.

It is zero when the zero fiber is a strict majority and one otherwise. The nondegeneracy
hypothesis records the source's type-I/type-II domain and excludes its tied type-III case. This
is the source's democratic convention; no theorem comparing it with another Arf construction
is asserted here.
-/
noncomputable def democraticArfInvariant (q : QuadraticForm (ZMod 2) V)
    (_hq : q.polarBilin.Nondegenerate) : ZMod 2 :=
  if 2 * zeroCount q > Nat.card V then 0 else 1

end LeanCategories.ForMathlib.QuadraticMap
