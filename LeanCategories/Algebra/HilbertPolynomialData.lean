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
Hilbert--Serre theorem.  Sweep III records exact eventual-polynomial data and
keeps existence/uniqueness in the theorem layer; no arbitrary polynomial is
selected before Hilbert--Serre supplies it.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Algebra

universe u v

/-- Source-faithful eventual-polynomial data for an integer-valued sequence. -/
abbrev EventuallyPolynomialData (f : ℕ → ℤ) :=
  {P : Polynomial ℚ // IsEventuallyPolynomial f P}

/-- Hartshorne's Hilbert polynomial of a graded vector-space family: the
polynomial selected by eventual agreement with `n ↦ dim_k M_n`.

For a finite graded module over a standard graded polynomial ring,
Hilbert--Serre proves that this selection satisfies the defining predicate;
that theorem is not part of this declaration. -/
abbrev GradedModuleHilbertPolynomialData
    (k : Type u) [Field k]
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module k (M n)] :=
  EventuallyPolynomialData
    (HilbertFunction
      (fun {N : Type v} [AddCommMonoid N] [Module k N] =>
        (Module.finrank k N : ℤ)) M)

end LeanCategories.Algebra
