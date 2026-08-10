/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations

@[expose] public section

/-!
# Fractional ideals and ideal classes

This file connects Mathlib's fractional ideals to its ideal class group.
-/

namespace LeanCategories.Algebra.FractionalIdeals

universe u

section Domain

variable (R : Type u) [CommRing R] [IsDomain R]

/-- The multiplicative group of invertible fractional ideals of a domain. -/
abbrev InvertibleFractionalIdeal :=
  Units (FractionalIdeal (nonZeroDivisors R) (FractionRing R))

/-- Send an invertible fractional ideal to its ideal class. -/
noncomputable def idealClass : InvertibleFractionalIdeal R →* ClassGroup R :=
  ClassGroup.mk (FractionRing R)

/-- A principal fractional ideal has trivial ideal class. -/
theorem idealClass_principal (x : Units (FractionRing R)) :
    idealClass R (toPrincipalIdeal R (FractionRing R) x) = 1 := by
  rw [idealClass, ClassGroup.mk_eq_one_iff]
  exact (FractionalIdeal.isPrincipal_iff _).2 ⟨x, by simp⟩

/-- An invertible fractional ideal has trivial class exactly when it is principal. -/
theorem idealClass_eq_one_iff (I : InvertibleFractionalIdeal R) :
    idealClass R I = 1 ↔ (I : Submodule R (FractionRing R)).IsPrincipal :=
  ClassGroup.mk_eq_one_iff

end Domain

section Dedekind

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- Over a Dedekind domain, integral ideals represent all ideal classes. -/
theorem integral_classes_surjective :
    Function.Surjective
      (ClassGroup.mk0 : nonZeroDivisors (Ideal R) → ClassGroup R) :=
  ClassGroup.mk0_surjective

end Dedekind

end LeanCategories.Algebra.FractionalIdeals
