/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# S-integers, S-units, and S-class groups

Definition-level realization of Neukirch FC09-C01-U096.

At the pinned Mathlib revision the valuation-defined ring of `S`-integers and
group of `S`-units already exist as `Set.integer` and `Set.unit`.  This file
records the source terminology and adds the corresponding class-group name.

The theorem that this ring is the localization obtained by inverting precisely
the primes in `S`, and the resulting Dedekind-domain structure, are not part of
this Sweep-III definition unit.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Algebra

open IsDedekindDomain

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  (S : Set (HeightOneSpectrum R)) (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Neukirch's ring of `S`-integers. -/
abbrev SIntegerRing := S.integer K

/-- Neukirch's group of `S`-units. -/
abbrev SUnitGroup := S.unit K

/-- Neukirch's `S`-class group: the ideal class group of the ring of
`S`-integers. -/
abbrev SClassGroup := ClassGroup (S.integer K)

end LeanCategories.Algebra
