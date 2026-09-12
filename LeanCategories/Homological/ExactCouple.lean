/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exact couples

Weibel, *An Introduction to Homological Algebra*, §5.9, p. 153
(FC05-C05-U068).

An exact couple is the cyclic diagram `D ⟶ D ⟶ E ⟶ D` which is exact at every vertex.  Weibel
works in modules, or more generally in an AB5 abelian category.  The definition itself only uses
abelian exactness; the stronger AB5 hypothesis enters the convergence arguments later in §5.9.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v, u} C] [Abelian C]

/-- An exact couple `D --i→ D --j→ E --k→ D`: the three consecutive pairs are exact.

Source: Weibel, *An Introduction to Homological Algebra*, §5.9, p. 153.  This is the
Mathlib-compatible port of the definition recorded in
`cmu-phil/Spectral@3b078f5f1de251637decf04bd3fc8aa01930a6b3::algebra/exact_couple.hlean`.
-/
structure ExactCouple where
  /-- The `D` object of the exact couple. -/
  D : C
  /-- The `E` object of the exact couple. -/
  E : C
  /-- The self-map `i : D ⟶ D`. -/
  i : D ⟶ D
  /-- The map `j : D ⟶ E`. -/
  j : D ⟶ E
  /-- The map `k : E ⟶ D`. -/
  k : E ⟶ D
  /-- Consecutive maps `i` and `j` compose to zero. -/
  i_j : i ≫ j = 0
  /-- Consecutive maps `j` and `k` compose to zero. -/
  j_k : j ≫ k = 0
  /-- Consecutive maps `k` and `i` compose to zero. -/
  k_i : k ≫ i = 0
  /-- Exactness at the second copy of `D`: `im(i) = ker(j)`. -/
  exact_ij : (ShortComplex.mk i j i_j).Exact
  /-- Exactness at `E`: `im(j) = ker(k)`. -/
  exact_jk : (ShortComplex.mk j k j_k).Exact
  /-- Exactness at the first copy of `D`: `im(k) = ker(i)`. -/
  exact_ki : (ShortComplex.mk k i k_i).Exact

namespace ExactCouple

variable (𝓔 : ExactCouple (C := C))

/-- The short complex `D --i→ D --j→ E`. -/
abbrev shortComplexIJ : ShortComplex C :=
  ShortComplex.mk 𝓔.i 𝓔.j 𝓔.i_j

/-- The short complex `D --j→ E --k→ D`. -/
abbrev shortComplexJK : ShortComplex C :=
  ShortComplex.mk 𝓔.j 𝓔.k 𝓔.j_k

/-- The short complex `E --k→ D --i→ D`. -/
abbrev shortComplexKI : ShortComplex C :=
  ShortComplex.mk 𝓔.k 𝓔.i 𝓔.k_i

end ExactCouple

end LeanCategories.Homological
