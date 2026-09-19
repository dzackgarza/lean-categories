/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Polynomial.Basic
public import Mathlib.GroupTheory.Coxeter.Length

/-!
# Poincaré polynomials of finite Coxeter systems

Humphreys, *Reflection Groups and Coxeter Groups*, Chapter 1
(FC15-C01-U038).

The source polynomial is purely finite combinatorial data once the Coxeter
length function is fixed. No factorization, parabolic identity, or
longest-element theorem is part of this Sweep-III construction.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanCategories.Combinatorics

universe u v

variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B}

/-- Humphreys' finite-subset Poincaré polynomial (FC15-C01-U038). -/
noncomputable def coxeterPoincarePolynomialOn
    (cs : CoxeterSystem M W) (S : Finset W) : Polynomial ℤ :=
  ∑ w ∈ S, Polynomial.X ^ cs.length w

/-- The Poincaré polynomial of a finite Coxeter system (FC15-C01-U038). -/
noncomputable def coxeterPoincarePolynomial
    [Fintype W] (cs : CoxeterSystem M W) : Polynomial ℤ :=
  coxeterPoincarePolynomialOn cs Finset.univ

end LeanCategories.Combinatorics
