/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.NegativeSquareTwoZsmul
public import LeanCategories.Lattices.Valued.Standard

/-!
# Probe for `two_zsmul_ne_zero_of_pairing_neg`

The lemma replaces the `NoZeroSMulDivisors` instance the development does not have, so what decides
it is (a) that the hyperbolic plane really has a vector of negative square and (b) that the lemma
fires there. The two are stated separately only because the plane's carrier is the packed type
`↑hyperbolicPlaneFiniteLattice.obj.obj.carrier`, which does not accept a literal `Fin 2 → ℤ` term
syntactically — the carrier obstruction of `results/issue-116-report.md`, not a gap in the lemma.

(a) is computed on the Gram matrix: `!![0, 1; 1, 0]` at `![1, -1]` gives `-2`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The hyperbolic plane's Gram matrix has a vector of square `-2`: the sign the lemma needs. -/
example : Matrix.toBilin' hyperbolicPlaneGramMatrix (![1, -1] : Fin 2 → ℤ) ![1, -1] = -2 := by
  decide

/-- The lemma fires at the hyperbolic plane, with that square as the hypothesis. -/
example (x : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
    (h : hyperbolicPlaneFiniteLattice.obj.obj.pairing x x < 0) :
    (2 : ℤ) • x ≠ 0 :=
  two_zsmul_ne_zero_of_pairing_neg (L := hyperbolicPlaneFiniteLattice) h

end LeanCategories.Lattices.Valued
