/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Local algebra routes

Mathlib owns localization of rings and modules, localization at prime ideals,
fraction rings, local rings, residue fields, and adic completions. This module
exposes the canonical definitions and functorial maps directly.
-/

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.LocalRing

@[expose] public section

open CategoryTheory

namespace LeanCategories.Algebra

universe u

/-- The residue field of a commutative local ring, using Mathlib's canonical quotient.

The local-ring hypothesis is carried by the object of `LocalRingCat`. -/
noncomputable def residueField (R : LocalRingCat.{u}) : CommRingCat.{u} :=
  letI : IsLocalRing (R.1 : Type u) := R.2
  CommRingCat.of (IsLocalRing.ResidueField R.1)

/-- The canonical quotient map from a local ring to its residue field. -/
noncomputable def residue (R : LocalRingCat.{u}) :
    (R.1 : Type u) →+* (residueField R : Type u) :=
  letI : IsLocalRing (R.1 : Type u) := R.2
  IsLocalRing.residue R.1

end LeanCategories.Algebra
