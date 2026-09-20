/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.DimensionTheory
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Hilbert-polynomial naming data

Definition-level realization of Hartshorne FC06-C01-U140.

Hartshorne names the unique polynomial supplied by the preceding
Hilbert--Serre theorem.  Sweep III records that naming step without asking a
caller to supply the existence theorem: the polynomial characterized by
eventual equality is selected by `Classical.epsilon`.  The preceding theorem
is responsible for showing that the selected polynomial actually has the
characterizing property and is unique.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Algebra

universe u v

/-- A proof-free name for the eventual polynomial characterized by
`IsEventuallyPolynomial f`.  Existence and uniqueness are theorem-layer
facts about the particular sequences to which this is applied. -/
def eventualPolynomialData (f : ℕ → ℤ) : Polynomial ℚ :=
  Classical.epsilon (IsEventuallyPolynomial f)

/-- Hartshorne's Hilbert polynomial of a graded vector-space family: the
polynomial selected by eventual agreement with `n ↦ dim_k M_n`.

For a finite graded module over a standard graded polynomial ring,
Hilbert--Serre proves that this selection satisfies the defining predicate;
that theorem is not part of this declaration. -/
def gradedModuleHilbertPolynomialData
    (k : Type u) [Field k]
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module k (M n)] :
    Polynomial ℚ :=
  eventualPolynomialData
    (HilbertFunction
      (fun {N : Type v} [AddCommMonoid N] [Module k N] =>
        (Module.finrank k N : ℤ)) M)

end LeanCategories.Algebra
